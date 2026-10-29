-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1471_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:10:54.909992+00:00
-- url     : https://prove2.me/submissions/095a4df9-d1d7-4167-9c5d-c25a832bf7f5

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
theorem support_rectangle_w1471_s6_0 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-965165999/5000000000 : ℝ)*x 0 + (1087724357/2000000000 : ℝ)*x 1 + (5215279821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (965165999/5000000000 : ℝ)^4439 ≤ (5893811064477/50000000000000 : ℝ)^3415 := by
    have hnat : (965165999 : ℕ)^4439*50000000000000^3415 ≤ 5893811064477^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965165999 5000000000 5893811064477 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087724357/2000000000 : ℝ)^4439 ≤ (45307932330473/100000000000000 : ℝ)^3415 := by
    have hnat : (1087724357 : ℕ)^4439*100000000000000^3415 ≤ 45307932330473^3415*2000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087724357 2000000000 45307932330473 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215279821/10000000000 : ℝ)^4439 ≤ (42904445527591/100000000000000 : ℝ)^3415 := by
    have hnat : (5215279821 : ℕ)^4439*100000000000000^3415 ≤ 42904445527591^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215279821 10000000000 42904445527591 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-965165999/5000000000 : ℝ), (1087724357/2000000000 : ℝ), (5215279821/10000000000 : ℝ)] ![(5893811064477/50000000000000 : ℝ), (45307932330473/100000000000000 : ℝ), (42904445527591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-965165999/5000000000 : ℝ)|^4439 ≤ (5893811064477/50000000000000 : ℝ)^3415
        have hw : |(-965165999/5000000000 : ℝ)|=(965165999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087724357/2000000000 : ℝ)|^4439 ≤ (45307932330473/100000000000000 : ℝ)^3415
        have hw : |(1087724357/2000000000 : ℝ)|=(1087724357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215279821/10000000000 : ℝ)|^4439 ≤ (42904445527591/100000000000000 : ℝ)^3415
        have hw : |(5215279821/10000000000 : ℝ)|=(5215279821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s6_1 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338442127/2500000000 : ℝ)*x 0 + (-2044816327/10000000000 : ℝ)*x 1 + (208611193/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338442127/2500000000 : ℝ)^4439 ≤ (22195615737321/50000000000000 : ℝ)^3415 := by
    have hnat : (1338442127 : ℕ)^4439*50000000000000^3415 ≤ 22195615737321^3415*2500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338442127 2500000000 22195615737321 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2044816327/10000000000 : ℝ)^4439 ≤ (12704322929241/100000000000000 : ℝ)^3415 := by
    have hnat : (2044816327 : ℕ)^4439*100000000000000^3415 ≤ 12704322929241^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044816327 10000000000 12704322929241 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208611193/400000000 : ℝ)^4439 ≤ (8580889114073/20000000000000 : ℝ)^3415 := by
    have hnat : (208611193 : ℕ)^4439*20000000000000^3415 ≤ 8580889114073^3415*400000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208611193 400000000 8580889114073 20000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338442127/2500000000 : ℝ), (-2044816327/10000000000 : ℝ), (208611193/400000000 : ℝ)] ![(22195615737321/50000000000000 : ℝ), (12704322929241/100000000000000 : ℝ), (8580889114073/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338442127/2500000000 : ℝ)|^4439 ≤ (22195615737321/50000000000000 : ℝ)^3415
        have hw : |(1338442127/2500000000 : ℝ)|=(1338442127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2044816327/10000000000 : ℝ)|^4439 ≤ (12704322929241/100000000000000 : ℝ)^3415
        have hw : |(-2044816327/10000000000 : ℝ)|=(2044816327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208611193/400000000 : ℝ)|^4439 ≤ (8580889114073/20000000000000 : ℝ)^3415
        have hw : |(208611193/400000000 : ℝ)|=(208611193/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s6_2 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353768471/10000000000 : ℝ)*x 0 + (651909983/1250000000 : ℝ)*x 1 + (-1022408163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353768471/10000000000 : ℝ)^4439 ≤ (22195615537931/50000000000000 : ℝ)^3415 := by
    have hnat : (5353768471 : ℕ)^4439*50000000000000^3415 ≤ 22195615537931^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353768471 10000000000 22195615537931 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651909983/1250000000 : ℝ)^4439 ≤ (42904445987411/100000000000000 : ℝ)^3415 := by
    have hnat : (651909983 : ℕ)^4439*100000000000000^3415 ≤ 42904445987411^3415*1250000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651909983 1250000000 42904445987411 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1022408163/5000000000 : ℝ)^4439 ≤ (2540864584233/20000000000000 : ℝ)^3415 := by
    have hnat : (1022408163 : ℕ)^4439*20000000000000^3415 ≤ 2540864584233^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022408163 5000000000 2540864584233 20000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353768471/10000000000 : ℝ), (651909983/1250000000 : ℝ), (-1022408163/5000000000 : ℝ)] ![(22195615537931/50000000000000 : ℝ), (42904445987411/100000000000000 : ℝ), (2540864584233/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353768471/10000000000 : ℝ)|^4439 ≤ (22195615537931/50000000000000 : ℝ)^3415
        have hw : |(5353768471/10000000000 : ℝ)|=(5353768471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(651909983/1250000000 : ℝ)|^4439 ≤ (42904445987411/100000000000000 : ℝ)^3415
        have hw : |(651909983/1250000000 : ℝ)|=(651909983/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1022408163/5000000000 : ℝ)|^4439 ≤ (2540864584233/20000000000000 : ℝ)^3415
        have hw : |(-1022408163/5000000000 : ℝ)|=(1022408163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s6_3 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4289255053/10000000000 : ℝ)*x 0 + (253095349/625000000 : ℝ)*x 1 + (4541375991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4289255053/10000000000 : ℝ)^4439 ≤ (3327746666501/10000000000000 : ℝ)^3415 := by
    have hnat : (4289255053 : ℕ)^4439*10000000000000^3415 ≤ 3327746666501^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4289255053 10000000000 3327746666501 10000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (253095349/625000000 : ℝ)^4439 ≤ (6176079361481/20000000000000 : ℝ)^3415 := by
    have hnat : (253095349 : ℕ)^4439*20000000000000^3415 ≤ 6176079361481^3415*625000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253095349 625000000 6176079361481 20000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4541375991/10000000000 : ℝ)^4439 ≤ (1792106825997/5000000000000 : ℝ)^3415 := by
    have hnat : (4541375991 : ℕ)^4439*5000000000000^3415 ≤ 1792106825997^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4541375991 10000000000 1792106825997 5000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4289255053/10000000000 : ℝ), (253095349/625000000 : ℝ), (4541375991/10000000000 : ℝ)] ![(3327746666501/10000000000000 : ℝ), (6176079361481/20000000000000 : ℝ), (1792106825997/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4289255053/10000000000 : ℝ)|^4439 ≤ (3327746666501/10000000000000 : ℝ)^3415
        have hw : |(4289255053/10000000000 : ℝ)|=(4289255053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(253095349/625000000 : ℝ)|^4439 ≤ (6176079361481/20000000000000 : ℝ)^3415
        have hw : |(253095349/625000000 : ℝ)|=(253095349/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4541375991/10000000000 : ℝ)|^4439 ≤ (1792106825997/5000000000000 : ℝ)^3415
        have hw : |(4541375991/10000000000 : ℝ)|=(4541375991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s6_4 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1930362893/10000000000 : ℝ)*x 0 + (1304105097/2500000000 : ℝ)*x 1 + (5437472749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1930362893/10000000000 : ℝ)^4439 ≤ (11787867361369/100000000000000 : ℝ)^3415 := by
    have hnat : (1930362893 : ℕ)^4439*100000000000000^3415 ≤ 11787867361369^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930362893 10000000000 11787867361369 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304105097/2500000000 : ℝ)^4439 ≤ (21458321279703/50000000000000 : ℝ)^3415 := by
    have hnat : (1304105097 : ℕ)^4439*50000000000000^3415 ≤ 21458321279703^3415*2500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304105097 2500000000 21458321279703 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437472749/10000000000 : ℝ)^4439 ≤ (1415484064319/3125000000000 : ℝ)^3415 := by
    have hnat : (5437472749 : ℕ)^4439*3125000000000^3415 ≤ 1415484064319^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437472749 10000000000 1415484064319 3125000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1930362893/10000000000 : ℝ), (1304105097/2500000000 : ℝ), (5437472749/10000000000 : ℝ)] ![(11787867361369/100000000000000 : ℝ), (21458321279703/50000000000000 : ℝ), (1415484064319/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1930362893/10000000000 : ℝ)|^4439 ≤ (11787867361369/100000000000000 : ℝ)^3415
        have hw : |(-1930362893/10000000000 : ℝ)|=(1930362893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304105097/2500000000 : ℝ)|^4439 ≤ (21458321279703/50000000000000 : ℝ)^3415
        have hw : |(1304105097/2500000000 : ℝ)|=(1304105097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437472749/10000000000 : ℝ)|^4439 ≤ (1415484064319/3125000000000 : ℝ)^3415
        have hw : |(5437472749/10000000000 : ℝ)|=(5437472749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s6_5 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165485363/312500000 : ℝ)*x 0 + (-113913967/625000000 : ℝ)*x 1 + (1087494493/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165485363/312500000 : ℝ)^4439 ≤ (43764589376321/100000000000000 : ℝ)^3415 := by
    have hnat : (165485363 : ℕ)^4439*100000000000000^3415 ≤ 43764589376321^3415*312500000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165485363 312500000 43764589376321 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113913967/625000000 : ℝ)^4439 ≤ (10939923624227/100000000000000 : ℝ)^3415 := by
    have hnat : (113913967 : ℕ)^4439*100000000000000^3415 ≤ 10939923624227^3415*625000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113913967 625000000 10939923624227 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087494493/2000000000 : ℝ)^4439 ≤ (45295486983027/100000000000000 : ℝ)^3415 := by
    have hnat : (1087494493 : ℕ)^4439*100000000000000^3415 ≤ 45295486983027^3415*2000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087494493 2000000000 45295486983027 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165485363/312500000 : ℝ), (-113913967/625000000 : ℝ), (1087494493/2000000000 : ℝ)] ![(43764589376321/100000000000000 : ℝ), (10939923624227/100000000000000 : ℝ), (45295486983027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165485363/312500000 : ℝ)|^4439 ≤ (43764589376321/100000000000000 : ℝ)^3415
        have hw : |(165485363/312500000 : ℝ)|=(165485363/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-113913967/625000000 : ℝ)|^4439 ≤ (10939923624227/100000000000000 : ℝ)^3415
        have hw : |(-113913967/625000000 : ℝ)|=(113913967/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087494493/2000000000 : ℝ)|^4439 ≤ (45295486983027/100000000000000 : ℝ)^3415
        have hw : |(1087494493/2000000000 : ℝ)|=(1087494493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s6_6 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295531399/10000000000 : ℝ)*x 0 + (169921023/312500000 : ℝ)*x 1 + (-364524679/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295531399/10000000000 : ℝ)^4439 ≤ (21882293522593/50000000000000 : ℝ)^3415 := by
    have hnat : (5295531399 : ℕ)^4439*50000000000000^3415 ≤ 21882293522593^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295531399 10000000000 21882293522593 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169921023/312500000 : ℝ)^4439 ≤ (45295489917443/100000000000000 : ℝ)^3415 := by
    have hnat : (169921023 : ℕ)^4439*100000000000000^3415 ≤ 45295489917443^3415*312500000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169921023 312500000 45295489917443 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (364524679/2000000000 : ℝ)^4439 ≤ (2187984604693/20000000000000 : ℝ)^3415 := by
    have hnat : (364524679 : ℕ)^4439*20000000000000^3415 ≤ 2187984604693^3415*2000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364524679 2000000000 2187984604693 20000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295531399/10000000000 : ℝ), (169921023/312500000 : ℝ), (-364524679/2000000000 : ℝ)] ![(21882293522593/50000000000000 : ℝ), (45295489917443/100000000000000 : ℝ), (2187984604693/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295531399/10000000000 : ℝ)|^4439 ≤ (21882293522593/50000000000000 : ℝ)^3415
        have hw : |(5295531399/10000000000 : ℝ)|=(5295531399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169921023/312500000 : ℝ)|^4439 ≤ (45295489917443/100000000000000 : ℝ)^3415
        have hw : |(169921023/312500000 : ℝ)|=(169921023/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-364524679/2000000000 : ℝ)|^4439 ≤ (2187984604693/20000000000000 : ℝ)^3415
        have hw : |(-364524679/2000000000 : ℝ)|=(364524679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_s6_7 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4289322663/10000000000 : ℝ)*x 0 + (4538864331/10000000000 : ℝ)*x 1 + (4052055837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4289322663/10000000000 : ℝ)^4439 ≤ (4159768561617/12500000000000 : ℝ)^3415 := by
    have hnat : (4289322663 : ℕ)^4439*12500000000000^3415 ≤ 4159768561617^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4289322663 10000000000 4159768561617 12500000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4538864331/10000000000 : ℝ)^4439 ≤ (35816371783811/100000000000000 : ℝ)^3415 := by
    have hnat : (4538864331 : ℕ)^4439*100000000000000^3415 ≤ 35816371783811^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4538864331 10000000000 35816371783811 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4052055837/10000000000 : ℝ)^4439 ≤ (772636992743/2500000000000 : ℝ)^3415 := by
    have hnat : (4052055837 : ℕ)^4439*2500000000000^3415 ≤ 772636992743^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4052055837 10000000000 772636992743 2500000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4289322663/10000000000 : ℝ), (4538864331/10000000000 : ℝ), (4052055837/10000000000 : ℝ)] ![(4159768561617/12500000000000 : ℝ), (35816371783811/100000000000000 : ℝ), (772636992743/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4289322663/10000000000 : ℝ)|^4439 ≤ (4159768561617/12500000000000 : ℝ)^3415
        have hw : |(4289322663/10000000000 : ℝ)|=(4289322663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4538864331/10000000000 : ℝ)|^4439 ≤ (35816371783811/100000000000000 : ℝ)^3415
        have hw : |(4538864331/10000000000 : ℝ)|=(4538864331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4052055837/10000000000 : ℝ)|^4439 ≤ (772636992743/2500000000000 : ℝ)^3415
        have hw : |(4052055837/10000000000 : ℝ)|=(4052055837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1471_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160111513/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (619/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2149/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10747/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15473/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (619/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2149/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (619/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2149/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (619/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2149/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (619/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2149/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (619/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2149/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (619/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2149/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2149/20000 : ℝ) ^ (4437/1024 : ℝ) ≤ (3170880335984573/50000000000000000000 : ℝ) := by
    have hpowers : (2149/20000 : ℝ)^4437 ≤ (3170880335984573/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2149 : ℕ)^4437*50000000000000000000^1024 ≤ 3170880335984573^1024*20000^4437 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2149 20000 3170880335984573 50000000000000000000 4437 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2149/20000 : ℝ)) (X := (3170880335984573/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (619/4000 : ℝ) ^ (4437/1024 : ℝ) ≤ (30807986036200737/100000000000000000000 : ℝ) := by
    have hpowers : (619/4000 : ℝ)^4437 ≤ (30807986036200737/100000000000000000000 : ℝ)^1024 := by
      have hnat : (619 : ℕ)^4437*100000000000000000000^1024 ≤ 30807986036200737^1024*4000^4437 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        619 4000 30807986036200737 100000000000000000000 4437 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (619/4000 : ℝ)) (X := (30807986036200737/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003170880335984573/25000000000000000000 : ℝ) ≤ (5000146352178621/5000000000000000 : ℝ) ^ (4437/1024 : ℝ) := by
    have hpowers : (25003170880335984573/25000000000000000000 : ℝ)^1024 ≤ (5000146352178621/5000000000000000 : ℝ)^4437 := by
      have hnat : (25003170880335984573 : ℕ)^1024*5000000000000000^4437 ≤ 5000146352178621^4437*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003170880335984573 25000000000000000000 5000146352178621 5000000000000000 1024 4437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000146352178621/5000000000000000 : ℝ)) (X := (25003170880335984573/25000000000000000000 : ℝ)) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037149746708169883/100000000000000000000 : ℝ) ≤ (1000085724377861/1000000000000000 : ℝ) ^ (4437/1024 : ℝ) := by
    have hpowers : (100037149746708169883/100000000000000000000 : ℝ)^1024 ≤ (1000085724377861/1000000000000000 : ℝ)^4437 := by
      have hnat : (100037149746708169883 : ℕ)^1024*1000000000000000^4437 ≤ 1000085724377861^4437*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037149746708169883 100000000000000000000 1000085724377861 1000000000000000 1024 4437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000085724377861/1000000000000000 : ℝ)) (X := (100037149746708169883/100000000000000000000 : ℝ)) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030807986036200737/50000000000000000000 : ℝ) ≤ (5000710891599989/5000000000000000 : ℝ) ^ (4437/1024 : ℝ) := by
    have hpowers : (50030807986036200737/50000000000000000000 : ℝ)^1024 ≤ (5000710891599989/5000000000000000 : ℝ)^4437 := by
      have hnat : (50030807986036200737 : ℕ)^1024*5000000000000000^4437 ≤ 5000710891599989^4437*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030807986036200737 50000000000000000000 5000710891599989 5000000000000000 1024 4437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000710891599989/5000000000000000 : ℝ)) (X := (50030807986036200737/50000000000000000000 : ℝ)) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3170880335984573/50000000000000000000 : ℝ) ≤ ((2364462626972227817/2365000000000000000 : ℝ)+2*(70567427671/59125000000000 : ℝ)*(2149/20000 : ℝ))^(4437/1024 : ℝ) := by
    rw [show (2364462626972227817/2365000000000000000 : ℝ)+2*(70567427671/59125000000000 : ℝ)*(2149/20000 : ℝ)=(5000146352178621/5000000000000000 : ℝ) by norm_num, show 1+2*(3170880335984573/50000000000000000000 : ℝ)=(25003170880335984573/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30807986036200737/100000000000000000000 : ℝ)+(3170880335984573/50000000000000000000 : ℝ) ≤ ((2364462626972227817/2365000000000000000 : ℝ)+(70567427671/59125000000000 : ℝ)*((619/4000 : ℝ)+(2149/20000 : ℝ)))^(4437/1024 : ℝ) := by
    rw [show (2364462626972227817/2365000000000000000 : ℝ)+(70567427671/59125000000000 : ℝ)*((619/4000 : ℝ)+(2149/20000 : ℝ))=(1000085724377861/1000000000000000 : ℝ) by norm_num, show 1+(30807986036200737/100000000000000000000 : ℝ)+(3170880335984573/50000000000000000000 : ℝ)=(100037149746708169883/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30807986036200737/100000000000000000000 : ℝ) ≤ ((2364462626972227817/2365000000000000000 : ℝ)+2*(70567427671/59125000000000 : ℝ)*(619/4000 : ℝ))^(4437/1024 : ℝ) := by
    rw [show (2364462626972227817/2365000000000000000 : ℝ)+2*(70567427671/59125000000000 : ℝ)*(619/4000 : ℝ)=(5000710891599989/5000000000000000 : ℝ) by norm_num, show 1+2*(30807986036200737/100000000000000000000 : ℝ)=(50030807986036200737/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2364462626972227817/2365000000000000000 : ℝ)*(X 1 0+X 2 0)+(70567427671/59125000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4437/1024 : ℝ)) (lo := (2149/20000 : ℝ)) (hi := (619/4000 : ℝ)) (c := (2364462626972227817/2365000000000000000 : ℝ)) (alpha := (70567427671/59125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2364462626972227817/2365000000000000000 : ℝ)*(X 0 1+X 2 1)+(70567427671/59125000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4437/1024 : ℝ)) (lo := (2149/20000 : ℝ)) (hi := (619/4000 : ℝ)) (c := (2364462626972227817/2365000000000000000 : ℝ)) (alpha := (70567427671/59125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2364462626972227817/2365000000000000000 : ℝ)*(X 0 2+X 1 2)+(70567427671/59125000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4437/1024 : ℝ)) (lo := (2149/20000 : ℝ)) (hi := (619/4000 : ℝ)) (c := (2364462626972227817/2365000000000000000 : ℝ)) (alpha := (70567427671/59125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-965165999/5000000000 : ℝ)*X 0 0+(1087724357/2000000000 : ℝ)*X 0 1+(5215279821/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338442127/2500000000 : ℝ)*X 1 0+(-2044816327/10000000000 : ℝ)*X 1 1+(208611193/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353768471/10000000000 : ℝ)*X 2 0+(651909983/1250000000 : ℝ)*X 2 1+(-1022408163/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4289255053/10000000000 : ℝ)*X 0 0+(253095349/625000000 : ℝ)*X 0 1+(4541375991/10000000000 : ℝ)*X 0 2+(4289255053/10000000000 : ℝ)*X 1 0+(253095349/625000000 : ℝ)*X 1 1+(4541375991/10000000000 : ℝ)*X 1 2+(4289255053/10000000000 : ℝ)*X 2 0+(253095349/625000000 : ℝ)*X 2 1+(4541375991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1930362893/10000000000 : ℝ)*X 0 0+(1304105097/2500000000 : ℝ)*X 0 1+(5437472749/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165485363/312500000 : ℝ)*X 1 0+(-113913967/625000000 : ℝ)*X 1 1+(1087494493/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295531399/10000000000 : ℝ)*X 2 0+(169921023/312500000 : ℝ)*X 2 1+(-364524679/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4289322663/10000000000 : ℝ)*X 0 0+(4538864331/10000000000 : ℝ)*X 0 1+(4052055837/10000000000 : ℝ)*X 0 2+(4289322663/10000000000 : ℝ)*X 1 0+(4538864331/10000000000 : ℝ)*X 1 1+(4052055837/10000000000 : ℝ)*X 1 2+(4289322663/10000000000 : ℝ)*X 2 0+(4538864331/10000000000 : ℝ)*X 2 1+(4052055837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (91553043433032289110282123/11825000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1408615893/100000000000000 : ℝ)*(base19) + (1301883523/100000000000000 : ℝ)*(base23) + (10143839/25000000000000 : ℝ)*(lower2) + (95307409/50000000000000 : ℝ)*(upper3) + (65361529/50000000000000 : ℝ)*(upper5) + (325532128670091/10000000000000 : ℝ)*(major0) + (325532128670091/10000000000000 : ℝ)*(major1) + (325532128670091/10000000000000 : ℝ)*(major2) + (895492339760371/20000000000000 : ℝ)*(sp0) + (2238741062620099/50000000000000 : ℝ)*(sp1) + (559685278996571/12500000000000 : ℝ)*(sp2) + (127071762266277/6250000000000 : ℝ)*(sp3) + (5458763559/25000000000000 : ℝ)*(sp4) + (211704153/2000000000000 : ℝ)*(sp7) + (1016579390734041/50000000000000 : ℝ)*(f.failure) + (4477483533856091/100000000000000 : ℝ)*(f.sum) + (297860406071/295625000000000000000000000 : ℝ)*base65 + (160612309422088653/23650000000000000000000000000000 : ℝ)*base68 + (204358298577088653/23650000000000000000000000000000 : ℝ)*base70 + (68500768310938653/23650000000000000000000000000000 : ℝ)*base72 + (1141859688227/591250000000000000000000000 : ℝ)*base73 + (262596958800238653/23650000000000000000000000000000 : ℝ)*base76 + (37926496336538653/23650000000000000000000000000000 : ℝ)*base78 + (21862395034938653/23650000000000000000000000000000 : ℝ)*base80 + (2469912060661/1182500000000000000000000000 : ℝ)*base82 + (14885967/5000000000000000000000 : ℝ)*base90 + (14885967/5000000000000000000000 : ℝ)*base92 + (14885967/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2673237242895168096483/473000000000000000000000000 : ℝ) := by norm_num
    linear_combination (657443229/50000000000000 : ℝ)*(base19) + (128668483/10000000000000 : ℝ)*(base23) + (315513957/100000000000000 : ℝ)*(lower1) + (60875623/100000000000000 : ℝ)*(upper2) + (77965379/50000000000000 : ℝ)*(upper3) + (107904977/100000000000000 : ℝ)*(upper5) + (65779869359569/2000000000000 : ℝ)*(major0) + (65779869359569/2000000000000 : ℝ)*(major1) + (65779869359569/2000000000000 : ℝ)*(major2) + (3838876761/100000000000000 : ℝ)*(sp2) + (2261898755054639/50000000000000 : ℝ)*(sp4) + (226189809761141/5000000000000 : ℝ)*(sp5) + (2261896192273843/50000000000000 : ℝ)*(sp6) + (1027094618729401/50000000000000 : ℝ)*(sp7) + (1027094618729401/50000000000000 : ℝ)*(f.failure) + (2261898755054639/50000000000000 : ℝ)*(f.sum) + (66591804277/14781250000000000000000000 : ℝ)*base66 + (31573257536910873/4730000000000000000000000000000 : ℝ)*base67 + (115903286802810873/4730000000000000000000000000000 : ℝ)*base69 + (22675848072689127/4730000000000000000000000000000 : ℝ)*base72 + (316506595393/236500000000000000000000000 : ℝ)*base73 + (12528445346129127/4730000000000000000000000000000 : ℝ)*base76 + (19116608330939127/4730000000000000000000000000000 : ℝ)*base78 + (38807463631630873/4730000000000000000000000000000 : ℝ)*base79 + (1541138409139/236500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (31693713/5000000000000000000000 : ℝ)*base89 + (31693713/5000000000000000000000 : ℝ)*base91 + (31693713/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1471_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160111513/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (619/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2149/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10747/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15473/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1471_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1471_box_0 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-85453243/500000000 : ℝ)*x 0 + (5407280713/10000000000 : ℝ)*x 1 + (1351820001/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85453243/500000000 : ℝ)^4439 ≤ (5031163680017/50000000000000 : ℝ)^3415 := by
    have hnat : (85453243 : ℕ)^4439*50000000000000^3415 ≤ 5031163680017^3415*500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85453243 500000000 5031163680017 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407280713/10000000000 : ℝ)^4439 ≤ (22484420073571/50000000000000 : ℝ)^3415 := by
    have hnat : (5407280713 : ℕ)^4439*50000000000000^3415 ≤ 22484420073571^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407280713 10000000000 22484420073571 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351820001/2500000000 : ℝ)^4439 ≤ (22484416241413/50000000000000 : ℝ)^3415 := by
    have hnat : (1351820001 : ℕ)^4439*50000000000000^3415 ≤ 22484416241413^3415*2500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351820001 2500000000 22484416241413 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85453243/500000000 : ℝ), (5407280713/10000000000 : ℝ), (1351820001/2500000000 : ℝ)] ![(5031163680017/50000000000000 : ℝ), (22484420073571/50000000000000 : ℝ), (22484416241413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85453243/500000000 : ℝ)|^4439 ≤ (5031163680017/50000000000000 : ℝ)^3415
        have hw : |(-85453243/500000000 : ℝ)|=(85453243/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407280713/10000000000 : ℝ)|^4439 ≤ (22484420073571/50000000000000 : ℝ)^3415
        have hw : |(5407280713/10000000000 : ℝ)|=(5407280713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351820001/2500000000 : ℝ)|^4439 ≤ (22484416241413/50000000000000 : ℝ)^3415
        have hw : |(1351820001/2500000000 : ℝ)|=(1351820001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_box_1 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1054005827/2000000000 : ℝ)*x 0 + (-949551283/5000000000 : ℝ)*x 1 + (42244377/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054005827/2000000000 : ℝ)^4439 ≤ (21745412755413/50000000000000 : ℝ)^3415 := by
    have hnat : (1054005827 : ℕ)^4439*50000000000000^3415 ≤ 21745412755413^3415*2000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054005827 2000000000 21745412755413 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (949551283/5000000000 : ℝ)^4439 ≤ (11540339267239/100000000000000 : ℝ)^3415 := by
    have hnat : (949551283 : ℕ)^4439*100000000000000^3415 ≤ 11540339267239^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949551283 5000000000 11540339267239 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42244377/78125000 : ℝ)^4439 ≤ (8993767041391/20000000000000 : ℝ)^3415 := by
    have hnat : (42244377 : ℕ)^4439*20000000000000^3415 ≤ 8993767041391^3415*78125000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42244377 78125000 8993767041391 20000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054005827/2000000000 : ℝ), (-949551283/5000000000 : ℝ), (42244377/78125000 : ℝ)] ![(21745412755413/50000000000000 : ℝ), (11540339267239/100000000000000 : ℝ), (8993767041391/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054005827/2000000000 : ℝ)|^4439 ≤ (21745412755413/50000000000000 : ℝ)^3415
        have hw : |(1054005827/2000000000 : ℝ)|=(1054005827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-949551283/5000000000 : ℝ)|^4439 ≤ (11540339267239/100000000000000 : ℝ)^3415
        have hw : |(-949551283/5000000000 : ℝ)|=(949551283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42244377/78125000 : ℝ)|^4439 ≤ (8993767041391/20000000000000 : ℝ)^3415
        have hw : |(42244377/78125000 : ℝ)|=(42244377/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_box_2 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635014751/5000000000 : ℝ)*x 0 + (2703639927/5000000000 : ℝ)*x 1 + (-949551309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635014751/5000000000 : ℝ)^4439 ≤ (21745414723821/50000000000000 : ℝ)^3415 := by
    have hnat : (2635014751 : ℕ)^4439*50000000000000^3415 ≤ 21745414723821^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635014751 5000000000 21745414723821 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703639927/5000000000 : ℝ)^4439 ≤ (1124220771533/2500000000000 : ℝ)^3415 := by
    have hnat : (2703639927 : ℕ)^4439*2500000000000^3415 ≤ 1124220771533^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703639927 5000000000 1124220771533 2500000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (949551309/5000000000 : ℝ)^4439 ≤ (11540339677979/100000000000000 : ℝ)^3415 := by
    have hnat : (949551309 : ℕ)^4439*100000000000000^3415 ≤ 11540339677979^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949551309 5000000000 11540339677979 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635014751/5000000000 : ℝ), (2703639927/5000000000 : ℝ), (-949551309/5000000000 : ℝ)] ![(21745414723821/50000000000000 : ℝ), (1124220771533/2500000000000 : ℝ), (11540339677979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635014751/5000000000 : ℝ)|^4439 ≤ (21745414723821/50000000000000 : ℝ)^3415
        have hw : |(2635014751/5000000000 : ℝ)|=(2635014751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703639927/5000000000 : ℝ)|^4439 ≤ (1124220771533/2500000000000 : ℝ)^3415
        have hw : |(2703639927/5000000000 : ℝ)|=(2703639927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-949551309/5000000000 : ℝ)|^4439 ≤ (11540339677979/100000000000000 : ℝ)^3415
        have hw : |(-949551309/5000000000 : ℝ)|=(949551309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_box_3 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4494326269/10000000000 : ℝ)*x 0 + (209699151/500000000 : ℝ)*x 1 + (2096991683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4494326269/10000000000 : ℝ)^4439 ≤ (8840052400637/25000000000000 : ℝ)^3415 := by
    have hnat : (4494326269 : ℕ)^4439*25000000000000^3415 ≤ 8840052400637^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494326269 10000000000 8840052400637 25000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209699151/500000000 : ℝ)^4439 ≤ (6463978692019/20000000000000 : ℝ)^3415 := by
    have hnat : (209699151 : ℕ)^4439*20000000000000^3415 ≤ 6463978692019^3415*500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209699151 500000000 6463978692019 20000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2096991683/5000000000 : ℝ)^4439 ≤ (32319896925977/100000000000000 : ℝ)^3415 := by
    have hnat : (2096991683 : ℕ)^4439*100000000000000^3415 ≤ 32319896925977^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096991683 5000000000 32319896925977 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4494326269/10000000000 : ℝ), (209699151/500000000 : ℝ), (2096991683/5000000000 : ℝ)] ![(8840052400637/25000000000000 : ℝ), (6463978692019/20000000000000 : ℝ), (32319896925977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4494326269/10000000000 : ℝ)|^4439 ≤ (8840052400637/25000000000000 : ℝ)^3415
        have hw : |(4494326269/10000000000 : ℝ)|=(4494326269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209699151/500000000 : ℝ)|^4439 ≤ (6463978692019/20000000000000 : ℝ)^3415
        have hw : |(209699151/500000000 : ℝ)|=(209699151/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2096991683/5000000000 : ℝ)|^4439 ≤ (32319896925977/100000000000000 : ℝ)^3415
        have hw : |(2096991683/5000000000 : ℝ)|=(2096991683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_box_4 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-431414843/2000000000 : ℝ)*x 0 + (262102161/500000000 : ℝ)*x 1 + (2621021837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431414843/2000000000 : ℝ)^4439 ≤ (1702284549671/12500000000000 : ℝ)^3415 := by
    have hnat : (431414843 : ℕ)^4439*12500000000000^3415 ≤ 1702284549671^3415*2000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431414843 2000000000 1702284549671 12500000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262102161/500000000 : ℝ)^4439 ≤ (8638171873001/20000000000000 : ℝ)^3415 := by
    have hnat : (262102161 : ℕ)^4439*20000000000000^3415 ≤ 8638171873001^3415*500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262102161 500000000 8638171873001 20000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621021837/5000000000 : ℝ)^4439 ≤ (43190864227303/100000000000000 : ℝ)^3415 := by
    have hnat : (2621021837 : ℕ)^4439*100000000000000^3415 ≤ 43190864227303^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621021837 5000000000 43190864227303 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-431414843/2000000000 : ℝ), (262102161/500000000 : ℝ), (2621021837/5000000000 : ℝ)] ![(1702284549671/12500000000000 : ℝ), (8638171873001/20000000000000 : ℝ), (43190864227303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-431414843/2000000000 : ℝ)|^4439 ≤ (1702284549671/12500000000000 : ℝ)^3415
        have hw : |(-431414843/2000000000 : ℝ)|=(431414843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262102161/500000000 : ℝ)|^4439 ≤ (8638171873001/20000000000000 : ℝ)^3415
        have hw : |(262102161/500000000 : ℝ)|=(262102161/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621021837/5000000000 : ℝ)|^4439 ≤ (43190864227303/100000000000000 : ℝ)^3415
        have hw : |(2621021837/5000000000 : ℝ)|=(2621021837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_box_5 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1077088313/2000000000 : ℝ)*x 0 + (-983295347/5000000000 : ℝ)*x 1 + (5242043559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077088313/2000000000 : ℝ)^4439 ≤ (2795806326533/6250000000000 : ℝ)^3415 := by
    have hnat : (1077088313 : ℕ)^4439*6250000000000^3415 ≤ 2795806326533^3415*2000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077088313 2000000000 2795806326533 6250000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (983295347/5000000000 : ℝ)^4439 ≤ (12076235760349/100000000000000 : ℝ)^3415 := by
    have hnat : (983295347 : ℕ)^4439*100000000000000^3415 ≤ 12076235760349^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983295347 5000000000 12076235760349 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242043559/10000000000 : ℝ)^4439 ≤ (43190862995663/100000000000000 : ℝ)^3415 := by
    have hnat : (5242043559 : ℕ)^4439*100000000000000^3415 ≤ 43190862995663^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242043559 10000000000 43190862995663 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077088313/2000000000 : ℝ), (-983295347/5000000000 : ℝ), (5242043559/10000000000 : ℝ)] ![(2795806326533/6250000000000 : ℝ), (12076235760349/100000000000000 : ℝ), (43190862995663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077088313/2000000000 : ℝ)|^4439 ≤ (2795806326533/6250000000000 : ℝ)^3415
        have hw : |(1077088313/2000000000 : ℝ)|=(1077088313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-983295347/5000000000 : ℝ)|^4439 ≤ (12076235760349/100000000000000 : ℝ)^3415
        have hw : |(-983295347/5000000000 : ℝ)|=(983295347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242043559/10000000000 : ℝ)|^4439 ≤ (43190862995663/100000000000000 : ℝ)^3415
        have hw : |(5242043559/10000000000 : ℝ)|=(5242043559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_box_6 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (21036883/39062500 : ℝ)*x 0 + (2621021679/5000000000 : ℝ)*x 1 + (-1966590311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21036883/39062500 : ℝ)^4439 ≤ (11183226609861/25000000000000 : ℝ)^3415 := by
    have hnat : (21036883 : ℕ)^4439*25000000000000^3415 ≤ 11183226609861^3415*39062500^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21036883 39062500 11183226609861 25000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621021679/5000000000 : ℝ)^4439 ≤ (10797715210743/25000000000000 : ℝ)^3415 := by
    have hnat : (2621021679 : ℕ)^4439*25000000000000^3415 ≤ 10797715210743^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621021679 5000000000 10797715210743 25000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1966590311/10000000000 : ℝ)^4439 ≤ (12076232703241/100000000000000 : ℝ)^3415 := by
    have hnat : (1966590311 : ℕ)^4439*100000000000000^3415 ≤ 12076232703241^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966590311 10000000000 12076232703241 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21036883/39062500 : ℝ), (2621021679/5000000000 : ℝ), (-1966590311/10000000000 : ℝ)] ![(11183226609861/25000000000000 : ℝ), (10797715210743/25000000000000 : ℝ), (12076232703241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21036883/39062500 : ℝ)|^4439 ≤ (11183226609861/25000000000000 : ℝ)^3415
        have hw : |(21036883/39062500 : ℝ)|=(21036883/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621021679/5000000000 : ℝ)|^4439 ≤ (10797715210743/25000000000000 : ℝ)^3415
        have hw : |(2621021679/5000000000 : ℝ)|=(2621021679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1966590311/10000000000 : ℝ)|^4439 ≤ (12076232703241/100000000000000 : ℝ)^3415
        have hw : |(-1966590311/10000000000 : ℝ)|=(1966590311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_box_7 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4081972621/10000000000 : ℝ)*x 0 + (440001983/1000000000 : ℝ)*x 1 + (4400020237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4081972621/10000000000 : ℝ)^4439 ≤ (31202406273169/100000000000000 : ℝ)^3415 := by
    have hnat : (4081972621 : ℕ)^4439*100000000000000^3415 ≤ 31202406273169^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4081972621 10000000000 31202406273169 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440001983/1000000000 : ℝ)^4439 ≤ (1719939739547/5000000000000 : ℝ)^3415 := by
    have hnat : (440001983 : ℕ)^4439*5000000000000^3415 ≤ 1719939739547^3415*1000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440001983 1000000000 1719939739547 5000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4400020237/10000000000 : ℝ)^4439 ≤ (34398798926911/100000000000000 : ℝ)^3415 := by
    have hnat : (4400020237 : ℕ)^4439*100000000000000^3415 ≤ 34398798926911^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4400020237 10000000000 34398798926911 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4081972621/10000000000 : ℝ), (440001983/1000000000 : ℝ), (4400020237/10000000000 : ℝ)] ![(31202406273169/100000000000000 : ℝ), (1719939739547/5000000000000 : ℝ), (34398798926911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4081972621/10000000000 : ℝ)|^4439 ≤ (31202406273169/100000000000000 : ℝ)^3415
        have hw : |(4081972621/10000000000 : ℝ)|=(4081972621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(440001983/1000000000 : ℝ)|^4439 ≤ (1719939739547/5000000000000 : ℝ)^3415
        have hw : |(440001983/1000000000 : ℝ)|=(440001983/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4400020237/10000000000 : ℝ)|^4439 ≤ (34398798926911/100000000000000 : ℝ)^3415
        have hw : |(4400020237/10000000000 : ℝ)|=(4400020237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_box_8 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1031320337/5000000000 : ℝ)*x 0 + (1281688517/2500000000 : ℝ)*x 1 + (1356962593/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1031320337/5000000000 : ℝ)^4439 ≤ (6424229277967/50000000000000 : ℝ)^3415 := by
    have hnat : (1031320337 : ℕ)^4439*50000000000000^3415 ≤ 6424229277967^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031320337 5000000000 6424229277967 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1281688517/2500000000 : ℝ)^4439 ≤ (8392043156449/20000000000000 : ℝ)^3415 := by
    have hnat : (1281688517 : ℕ)^4439*20000000000000^3415 ≤ 8392043156449^3415*2500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281688517 2500000000 8392043156449 20000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356962593/2500000000 : ℝ)^4439 ≤ (22595662820763/50000000000000 : ℝ)^3415 := by
    have hnat : (1356962593 : ℕ)^4439*50000000000000^3415 ≤ 22595662820763^3415*2500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356962593 2500000000 22595662820763 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1031320337/5000000000 : ℝ), (1281688517/2500000000 : ℝ), (1356962593/2500000000 : ℝ)] ![(6424229277967/50000000000000 : ℝ), (8392043156449/20000000000000 : ℝ), (22595662820763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1031320337/5000000000 : ℝ)|^4439 ≤ (6424229277967/50000000000000 : ℝ)^3415
        have hw : |(-1031320337/5000000000 : ℝ)|=(1031320337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1281688517/2500000000 : ℝ)|^4439 ≤ (8392043156449/20000000000000 : ℝ)^3415
        have hw : |(1281688517/2500000000 : ℝ)|=(1281688517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356962593/2500000000 : ℝ)|^4439 ≤ (22595662820763/50000000000000 : ℝ)^3415
        have hw : |(1356962593/2500000000 : ℝ)|=(1356962593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_box_9 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627826883/5000000000 : ℝ)*x 0 + (-1890443937/10000000000 : ℝ)*x 1 + (5427850173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627826883/5000000000 : ℝ)^4439 ≤ (5417085468877/12500000000000 : ℝ)^3415 := by
    have hnat : (2627826883 : ℕ)^4439*12500000000000^3415 ≤ 5417085468877^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627826883 5000000000 5417085468877 12500000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1890443937/10000000000 : ℝ)^4439 ≤ (11471992742313/100000000000000 : ℝ)^3415 := by
    have hnat : (1890443937 : ℕ)^4439*100000000000000^3415 ≤ 11471992742313^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1890443937 10000000000 11471992742313 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427850173/10000000000 : ℝ)^4439 ≤ (22595661743939/50000000000000 : ℝ)^3415 := by
    have hnat : (5427850173 : ℕ)^4439*50000000000000^3415 ≤ 22595661743939^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427850173 10000000000 22595661743939 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627826883/5000000000 : ℝ), (-1890443937/10000000000 : ℝ), (5427850173/10000000000 : ℝ)] ![(5417085468877/12500000000000 : ℝ), (11471992742313/100000000000000 : ℝ), (22595661743939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627826883/5000000000 : ℝ)|^4439 ≤ (5417085468877/12500000000000 : ℝ)^3415
        have hw : |(2627826883/5000000000 : ℝ)|=(2627826883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1890443937/10000000000 : ℝ)|^4439 ≤ (11471992742313/100000000000000 : ℝ)^3415
        have hw : |(-1890443937/10000000000 : ℝ)|=(1890443937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427850173/10000000000 : ℝ)|^4439 ≤ (22595661743939/50000000000000 : ℝ)^3415
        have hw : |(5427850173/10000000000 : ℝ)|=(5427850173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_box_10 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627826713/5000000000 : ℝ)*x 0 + (5427850727/10000000000 : ℝ)*x 1 + (-945221819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627826713/5000000000 : ℝ)^4439 ≤ (8667336021363/20000000000000 : ℝ)^3415 := by
    have hnat : (2627826713 : ℕ)^4439*20000000000000^3415 ≤ 8667336021363^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627826713 5000000000 8667336021363 20000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427850727/10000000000 : ℝ)^4439 ≤ (45191329483461/100000000000000 : ℝ)^3415 := by
    have hnat : (5427850727 : ℕ)^4439*100000000000000^3415 ≤ 45191329483461^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427850727 10000000000 45191329483461 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (945221819/5000000000 : ℝ)^4439 ≤ (11471990383787/100000000000000 : ℝ)^3415 := by
    have hnat : (945221819 : ℕ)^4439*100000000000000^3415 ≤ 11471990383787^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945221819 5000000000 11471990383787 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627826713/5000000000 : ℝ), (5427850727/10000000000 : ℝ), (-945221819/5000000000 : ℝ)] ![(8667336021363/20000000000000 : ℝ), (45191329483461/100000000000000 : ℝ), (11471990383787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627826713/5000000000 : ℝ)|^4439 ≤ (8667336021363/20000000000000 : ℝ)^3415
        have hw : |(2627826713/5000000000 : ℝ)|=(2627826713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427850727/10000000000 : ℝ)|^4439 ≤ (45191329483461/100000000000000 : ℝ)^3415
        have hw : |(5427850727/10000000000 : ℝ)|=(5427850727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-945221819/5000000000 : ℝ)|^4439 ≤ (11471990383787/100000000000000 : ℝ)^3415
        have hw : |(-945221819/5000000000 : ℝ)|=(945221819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_box_11 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4544504297/10000000000 : ℝ)*x 0 + (4168302267/10000000000 : ℝ)*x 1 + (2084150907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4544504297/10000000000 : ℝ)^4439 ≤ (35874232817493/100000000000000 : ℝ)^3415 := by
    have hnat : (4544504297 : ℕ)^4439*100000000000000^3415 ≤ 35874232817493^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4544504297 10000000000 35874232817493 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4168302267/10000000000 : ℝ)^4439 ≤ (1603144292297/5000000000000 : ℝ)^3415 := by
    have hnat : (4168302267 : ℕ)^4439*5000000000000^3415 ≤ 1603144292297^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4168302267 10000000000 1603144292297 5000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084150907/5000000000 : ℝ)^4439 ≤ (8015720329147/25000000000000 : ℝ)^3415 := by
    have hnat : (2084150907 : ℕ)^4439*25000000000000^3415 ≤ 8015720329147^3415*5000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084150907 5000000000 8015720329147 25000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4544504297/10000000000 : ℝ), (4168302267/10000000000 : ℝ), (2084150907/5000000000 : ℝ)] ![(35874232817493/100000000000000 : ℝ), (1603144292297/5000000000000 : ℝ), (8015720329147/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4544504297/10000000000 : ℝ)|^4439 ≤ (35874232817493/100000000000000 : ℝ)^3415
        have hw : |(4544504297/10000000000 : ℝ)|=(4544504297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4168302267/10000000000 : ℝ)|^4439 ≤ (1603144292297/5000000000000 : ℝ)^3415
        have hw : |(4168302267/10000000000 : ℝ)|=(4168302267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2084150907/5000000000 : ℝ)|^4439 ≤ (8015720329147/25000000000000 : ℝ)^3415
        have hw : |(2084150907/5000000000 : ℝ)|=(2084150907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_box_12 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-45092111/250000000 : ℝ)*x 0 + (551871149/1000000000 : ℝ)*x 1 + (5227063331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (45092111/250000000 : ℝ)^4439 ≤ (168631094979/1562500000000 : ℝ)^3415 := by
    have hnat : (45092111 : ℕ)^4439*1562500000000^3415 ≤ 168631094979^3415*250000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45092111 250000000 168631094979 1562500000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551871149/1000000000 : ℝ)^4439 ≤ (9235422993901/20000000000000 : ℝ)^3415 := by
    have hnat : (551871149 : ℕ)^4439*20000000000000^3415 ≤ 9235422993901^3415*1000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551871149 1000000000 9235422993901 20000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227063331/10000000000 : ℝ)^4439 ≤ (537881186673/1250000000000 : ℝ)^3415 := by
    have hnat : (5227063331 : ℕ)^4439*1250000000000^3415 ≤ 537881186673^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227063331 10000000000 537881186673 1250000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-45092111/250000000 : ℝ), (551871149/1000000000 : ℝ), (5227063331/10000000000 : ℝ)] ![(168631094979/1562500000000 : ℝ), (9235422993901/20000000000000 : ℝ), (537881186673/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-45092111/250000000 : ℝ)|^4439 ≤ (168631094979/1562500000000 : ℝ)^3415
        have hw : |(-45092111/250000000 : ℝ)|=(45092111/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(551871149/1000000000 : ℝ)|^4439 ≤ (9235422993901/20000000000000 : ℝ)^3415
        have hw : |(551871149/1000000000 : ℝ)|=(551871149/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227063331/10000000000 : ℝ)|^4439 ≤ (537881186673/1250000000000 : ℝ)^3415
        have hw : |(5227063331/10000000000 : ℝ)|=(5227063331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_box_13 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079180663/2000000000 : ℝ)*x 0 + (-123282747/625000000 : ℝ)*x 1 + (1045412661/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079180663/2000000000 : ℝ)^4439 ≤ (44845888863667/100000000000000 : ℝ)^3415 := by
    have hnat : (1079180663 : ℕ)^4439*100000000000000^3415 ≤ 44845888863667^3415*2000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079180663 2000000000 44845888863667 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (123282747/625000000 : ℝ)^4439 ≤ (12123616467379/100000000000000 : ℝ)^3415 := by
    have hnat : (123282747 : ℕ)^4439*100000000000000^3415 ≤ 12123616467379^3415*625000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123282747 625000000 12123616467379 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1045412661/2000000000 : ℝ)^4439 ≤ (43030494655621/100000000000000 : ℝ)^3415 := by
    have hnat : (1045412661 : ℕ)^4439*100000000000000^3415 ≤ 43030494655621^3415*2000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045412661 2000000000 43030494655621 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079180663/2000000000 : ℝ), (-123282747/625000000 : ℝ), (1045412661/2000000000 : ℝ)] ![(44845888863667/100000000000000 : ℝ), (12123616467379/100000000000000 : ℝ), (43030494655621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079180663/2000000000 : ℝ)|^4439 ≤ (44845888863667/100000000000000 : ℝ)^3415
        have hw : |(1079180663/2000000000 : ℝ)|=(1079180663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-123282747/625000000 : ℝ)|^4439 ≤ (12123616467379/100000000000000 : ℝ)^3415
        have hw : |(-123282747/625000000 : ℝ)|=(123282747/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1045412661/2000000000 : ℝ)|^4439 ≤ (43030494655621/100000000000000 : ℝ)^3415
        have hw : |(1045412661/2000000000 : ℝ)|=(1045412661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_box_14 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395903211/10000000000 : ℝ)*x 0 + (5227063251/10000000000 : ℝ)*x 1 + (-394504833/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395903211/10000000000 : ℝ)^4439 ≤ (11211471935033/25000000000000 : ℝ)^3415 := by
    have hnat : (5395903211 : ℕ)^4439*25000000000000^3415 ≤ 11211471935033^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395903211 10000000000 11211471935033 25000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5227063251/10000000000 : ℝ)^4439 ≤ (43030494077783/100000000000000 : ℝ)^3415 := by
    have hnat : (5227063251 : ℕ)^4439*100000000000000^3415 ≤ 43030494077783^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227063251 10000000000 43030494077783 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394504833/2000000000 : ℝ)^4439 ≤ (6061809084541/50000000000000 : ℝ)^3415 := by
    have hnat : (394504833 : ℕ)^4439*50000000000000^3415 ≤ 6061809084541^3415*2000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394504833 2000000000 6061809084541 50000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395903211/10000000000 : ℝ), (5227063251/10000000000 : ℝ), (-394504833/2000000000 : ℝ)] ![(11211471935033/25000000000000 : ℝ), (43030494077783/100000000000000 : ℝ), (6061809084541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395903211/10000000000 : ℝ)|^4439 ≤ (11211471935033/25000000000000 : ℝ)^3415
        have hw : |(5395903211/10000000000 : ℝ)|=(5395903211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5227063251/10000000000 : ℝ)|^4439 ≤ (43030494077783/100000000000000 : ℝ)^3415
        have hw : |(5227063251/10000000000 : ℝ)|=(5227063251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-394504833/2000000000 : ℝ)|^4439 ≤ (6061809084541/50000000000000 : ℝ)^3415
        have hw : |(-394504833/2000000000 : ℝ)|=(394504833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1471_box_15 (p : ℝ) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (808745859/2000000000 : ℝ)*x 0 + (1104669497/2500000000 : ℝ)*x 1 + (4418678287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (808745859/2000000000 : ℝ)^4439 ≤ (30822954754387/100000000000000 : ℝ)^3415 := by
    have hnat : (808745859 : ℕ)^4439*100000000000000^3415 ≤ 30822954754387^3415*2000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808745859 2000000000 30822954754387 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1104669497/2500000000 : ℝ)^4439 ≤ (691770421871/2000000000000 : ℝ)^3415 := by
    have hnat : (1104669497 : ℕ)^4439*2000000000000^3415 ≤ 691770421871^3415*2500000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104669497 2500000000 691770421871 2000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4418678287/10000000000 : ℝ)^4439 ≤ (34588524135873/100000000000000 : ℝ)^3415 := by
    have hnat : (4418678287 : ℕ)^4439*100000000000000^3415 ≤ 34588524135873^3415*10000000000^4439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4418678287 10000000000 34588524135873 100000000000000 4439 3415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4439/1024 : ℝ)) 4439 3415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(808745859/2000000000 : ℝ), (1104669497/2500000000 : ℝ), (4418678287/10000000000 : ℝ)] ![(30822954754387/100000000000000 : ℝ), (691770421871/2000000000000 : ℝ), (34588524135873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(808745859/2000000000 : ℝ)|^4439 ≤ (30822954754387/100000000000000 : ℝ)^3415
        have hw : |(808745859/2000000000 : ℝ)|=(808745859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1104669497/2500000000 : ℝ)|^4439 ≤ (691770421871/2000000000000 : ℝ)^3415
        have hw : |(1104669497/2500000000 : ℝ)|=(1104669497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4418678287/10000000000 : ℝ)|^4439 ≤ (34588524135873/100000000000000 : ℝ)^3415
        have hw : |(4418678287/10000000000 : ℝ)|=(4418678287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1471_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160111513/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15473/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10747/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63693/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14609/25000 : ℝ) ∧ (39933/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42867/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15473/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10747/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15473/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10747/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15473/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10747/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15473/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10747/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15473/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10747/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15473/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10747/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10747/100000 : ℝ) ^ (4437/1024 : ℝ) ≤ (1269375398181327/20000000000000000000 : ℝ) := by
    have hpowers : (10747/100000 : ℝ)^4437 ≤ (1269375398181327/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10747 : ℕ)^4437*20000000000000000000^1024 ≤ 1269375398181327^1024*100000^4437 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10747 100000 1269375398181327 20000000000000000000 4437 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10747/100000 : ℝ)) (X := (1269375398181327/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15473/100000 : ℝ) ^ (4437/1024 : ℝ) ≤ (1539536862419357/5000000000000000000 : ℝ) := by
    have hpowers : (15473/100000 : ℝ)^4437 ≤ (1539536862419357/5000000000000000000 : ℝ)^1024 := by
      have hnat : (15473 : ℕ)^4437*5000000000000000000^1024 ≤ 1539536862419357^1024*100000^4437 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15473 100000 1539536862419357 5000000000000000000 4437 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15473/100000 : ℝ)) (X := (1539536862419357/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001269375398181327/10000000000000000000 : ℝ) ≤ (2500073235122433/2500000000000000 : ℝ) ^ (4437/1024 : ℝ) := by
    have hpowers : (10001269375398181327/10000000000000000000 : ℝ)^1024 ≤ (2500073235122433/2500000000000000 : ℝ)^4437 := by
      have hnat : (10001269375398181327 : ℕ)^1024*2500000000000000^4437 ≤ 2500073235122433^4437*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001269375398181327 10000000000000000000 2500073235122433 2500000000000000 1024 4437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500073235122433/2500000000000000 : ℝ)) (X := (10001269375398181327/10000000000000000000 : ℝ)) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001485504569571751/4000000000000000000 : ℝ) ≤ (10000856963857499/10000000000000000 : ℝ) ^ (4437/1024 : ℝ) := by
    have hpowers : (4001485504569571751/4000000000000000000 : ℝ)^1024 ≤ (10000856963857499/10000000000000000 : ℝ)^4437 := by
      have hnat : (4001485504569571751 : ℕ)^1024*10000000000000000^4437 ≤ 10000856963857499^4437*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001485504569571751 4000000000000000000 10000856963857499 10000000000000000 1024 4437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000856963857499/10000000000000000 : ℝ)) (X := (4001485504569571751/4000000000000000000 : ℝ)) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501539536862419357/2500000000000000000 : ℝ) ≤ (5000710493612633/5000000000000000 : ℝ) ^ (4437/1024 : ℝ) := by
    have hpowers : (2501539536862419357/2500000000000000000 : ℝ)^1024 ≤ (5000710493612633/5000000000000000 : ℝ)^4437 := by
      have hnat : (2501539536862419357 : ℕ)^1024*5000000000000000^4437 ≤ 5000710493612633^4437*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501539536862419357 2500000000000000000 5000710493612633 5000000000000000 1024 4437 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000710493612633/5000000000000000 : ℝ)) (X := (2501539536862419357/2500000000000000000 : ℝ)) (by norm_num) 4437 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1269375398181327/20000000000000000000 : ℝ) ≤ ((23624630659243844767/23630000000000000000 : ℝ)+2*(564023367767/472600000000000 : ℝ)*(10747/100000 : ℝ))^(4437/1024 : ℝ) := by
    rw [show (23624630659243844767/23630000000000000000 : ℝ)+2*(564023367767/472600000000000 : ℝ)*(10747/100000 : ℝ)=(2500073235122433/2500000000000000 : ℝ) by norm_num, show 1+2*(1269375398181327/20000000000000000000 : ℝ)=(10001269375398181327/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1539536862419357/5000000000000000000 : ℝ)+(1269375398181327/20000000000000000000 : ℝ) ≤ ((23624630659243844767/23630000000000000000 : ℝ)+(564023367767/472600000000000 : ℝ)*((15473/100000 : ℝ)+(10747/100000 : ℝ)))^(4437/1024 : ℝ) := by
    rw [show (23624630659243844767/23630000000000000000 : ℝ)+(564023367767/472600000000000 : ℝ)*((15473/100000 : ℝ)+(10747/100000 : ℝ))=(10000856963857499/10000000000000000 : ℝ) by norm_num, show 1+(1539536862419357/5000000000000000000 : ℝ)+(1269375398181327/20000000000000000000 : ℝ)=(4001485504569571751/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1539536862419357/5000000000000000000 : ℝ) ≤ ((23624630659243844767/23630000000000000000 : ℝ)+2*(564023367767/472600000000000 : ℝ)*(15473/100000 : ℝ))^(4437/1024 : ℝ) := by
    rw [show (23624630659243844767/23630000000000000000 : ℝ)+2*(564023367767/472600000000000 : ℝ)*(15473/100000 : ℝ)=(5000710493612633/5000000000000000 : ℝ) by norm_num, show 1+2*(1539536862419357/5000000000000000000 : ℝ)=(2501539536862419357/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23624630659243844767/23630000000000000000 : ℝ)*(X 1 0+X 2 0)+(564023367767/472600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4437/1024 : ℝ)) (lo := (10747/100000 : ℝ)) (hi := (15473/100000 : ℝ)) (c := (23624630659243844767/23630000000000000000 : ℝ)) (alpha := (564023367767/472600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23624630659243844767/23630000000000000000 : ℝ)*(X 0 1+X 2 1)+(564023367767/472600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4437/1024 : ℝ)) (lo := (10747/100000 : ℝ)) (hi := (15473/100000 : ℝ)) (c := (23624630659243844767/23630000000000000000 : ℝ)) (alpha := (564023367767/472600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23624630659243844767/23630000000000000000 : ℝ)*(X 0 2+X 1 2)+(564023367767/472600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4437/1024 : ℝ)) (lo := (10747/100000 : ℝ)) (hi := (15473/100000 : ℝ)) (c := (23624630659243844767/23630000000000000000 : ℝ)) (alpha := (564023367767/472600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-85453243/500000000 : ℝ)*X 0 0+(5407280713/10000000000 : ℝ)*X 0 1+(1351820001/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1054005827/2000000000 : ℝ)*X 1 0+(-949551283/5000000000 : ℝ)*X 1 1+(42244377/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2635014751/5000000000 : ℝ)*X 2 0+(2703639927/5000000000 : ℝ)*X 2 1+(-949551309/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4494326269/10000000000 : ℝ)*X 0 0+(209699151/500000000 : ℝ)*X 0 1+(2096991683/5000000000 : ℝ)*X 0 2+(4494326269/10000000000 : ℝ)*X 1 0+(209699151/500000000 : ℝ)*X 1 1+(2096991683/5000000000 : ℝ)*X 1 2+(4494326269/10000000000 : ℝ)*X 2 0+(209699151/500000000 : ℝ)*X 2 1+(2096991683/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-431414843/2000000000 : ℝ)*X 0 0+(262102161/500000000 : ℝ)*X 0 1+(2621021837/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1077088313/2000000000 : ℝ)*X 1 0+(-983295347/5000000000 : ℝ)*X 1 1+(5242043559/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((21036883/39062500 : ℝ)*X 2 0+(2621021679/5000000000 : ℝ)*X 2 1+(-1966590311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4081972621/10000000000 : ℝ)*X 0 0+(440001983/1000000000 : ℝ)*X 0 1+(4400020237/10000000000 : ℝ)*X 0 2+(4081972621/10000000000 : ℝ)*X 1 0+(440001983/1000000000 : ℝ)*X 1 1+(4400020237/10000000000 : ℝ)*X 1 2+(4081972621/10000000000 : ℝ)*X 2 0+(440001983/1000000000 : ℝ)*X 2 1+(4400020237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1031320337/5000000000 : ℝ)*X 0 0+(1281688517/2500000000 : ℝ)*X 0 1+(1356962593/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2627826883/5000000000 : ℝ)*X 1 0+(-1890443937/10000000000 : ℝ)*X 1 1+(5427850173/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2627826713/5000000000 : ℝ)*X 2 0+(5427850727/10000000000 : ℝ)*X 2 1+(-945221819/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4544504297/10000000000 : ℝ)*X 0 0+(4168302267/10000000000 : ℝ)*X 0 1+(2084150907/5000000000 : ℝ)*X 0 2+(4544504297/10000000000 : ℝ)*X 1 0+(4168302267/10000000000 : ℝ)*X 1 1+(2084150907/5000000000 : ℝ)*X 1 2+(4544504297/10000000000 : ℝ)*X 2 0+(4168302267/10000000000 : ℝ)*X 2 1+(2084150907/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-45092111/250000000 : ℝ)*X 0 0+(551871149/1000000000 : ℝ)*X 0 1+(5227063331/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1079180663/2000000000 : ℝ)*X 1 0+(-123282747/625000000 : ℝ)*X 1 1+(1045412661/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5395903211/10000000000 : ℝ)*X 2 0+(5227063251/10000000000 : ℝ)*X 2 1+(-394504833/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((808745859/2000000000 : ℝ)*X 0 0+(1104669497/2500000000 : ℝ)*X 0 1+(4418678287/10000000000 : ℝ)*X 0 2+(808745859/2000000000 : ℝ)*X 1 0+(1104669497/2500000000 : ℝ)*X 1 1+(4418678287/10000000000 : ℝ)*X 1 2+(808745859/2000000000 : ℝ)*X 2 0+(1104669497/2500000000 : ℝ)*X 2 1+(4418678287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1471_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63693/100000 : ℝ) ≤ (-188126844555907298054917847105301/295375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14934021/50000000000000 : ℝ)*(lower1) + (113657783/100000000000000 : ℝ)*(lower2) + (633601/390625000000 : ℝ)*(lower3) + (1699227/20000000000000 : ℝ)*(lower4) + (540526615001333/25000000000000 : ℝ)*(major0) + (540526615001333/25000000000000 : ℝ)*(major1) + (540526615001333/25000000000000 : ℝ)*(major2) + (1497533908997603/50000000000000 : ℝ)*(sp4) + (2995002471616569/100000000000000 : ℝ)*(sp5) + (1497520113389911/50000000000000 : ℝ)*(sp6) + (675143930077443/50000000000000 : ℝ)*(sp7) + (32673189319/50000000000000 : ℝ)*(sp13) + (5518243077/20000000000000 : ℝ)*(sp14) + (21881196017/25000000000000 : ℝ)*(sp15) + (675187692469477/50000000000000 : ℝ)*(f.failure) + (1497533908997603/50000000000000 : ℝ)*(f.sum) + (9159727612691/5907500000000000000000000000 : ℝ)*base65 + (229611355003080917/34750000000000000000000000000000 : ℝ)*base68 + (250965176418580917/34750000000000000000000000000000 : ℝ)*base70 + (276876075338830917/34750000000000000000000000000000 : ℝ)*base72 + (5499227142827/2953750000000000000000000000 : ℝ)*base74 + (118747709809330917/34750000000000000000000000000000 : ℝ)*base76 + (307670873289830917/34750000000000000000000000000000 : ℝ)*base78 + (417193091790330917/34750000000000000000000000000000 : ℝ)*base80 + (61381478883943/11815000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (68788701/5000000000000000000000 : ℝ)*base89 + (68788701/5000000000000000000000 : ℝ)*base91 + (68788701/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (14609/25000 : ℝ) ≤ (1380896151380752551829958487/2363000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20440707/25000000000000 : ℝ)*(upper0) + (14900013/100000000000000 : ℝ)*(upper3) + (53911437/100000000000000 : ℝ)*(upper4) + (22355783021111/1000000000000 : ℝ)*(major0) + (22355783021111/1000000000000 : ℝ)*(major1) + (22355783021111/1000000000000 : ℝ)*(major2) + (3055408583105961/100000000000000 : ℝ)*(sp0) + (3055410780131181/100000000000000 : ℝ)*(sp1) + (152769912828177/5000000000000 : ℝ)*(sp2) + (698131522922443/50000000000000 : ℝ)*(sp3) + (3098754891/100000000000000 : ℝ)*(sp5) + (64634479/25000000000000 : ℝ)*(sp7) + (330986257/6250000000000 : ℝ)*(sp8) + (15622322533/100000000000000 : ℝ)*(sp10) + (698131652191401/50000000000000 : ℝ)*(f.failure) + (381926734860759/12500000000000 : ℝ)*(f.sum) + (312117822451/147687500000000000000000000 : ℝ)*base66 + (2605773391650361/1390000000000000000000000000000 : ℝ)*base67 + (5497707081479639/1390000000000000000000000000000 : ℝ)*base70 + (879756151639639/1390000000000000000000000000000 : ℝ)*base72 + (3213297082623/236300000000000000000000000 : ℝ)*base74 + (3787974001690361/1390000000000000000000000000000 : ℝ)*base75 + (2055143331959639/1390000000000000000000000000000 : ℝ)*base78 + (4961366301270361/1390000000000000000000000000000 : ℝ)*base79 + (2466791184813/590750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (20300287/5000000000000000000000 : ℝ)*base90 + (20300287/5000000000000000000000 : ℝ)*base92 + (20300287/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (39933/50000 : ℝ) ≤ (235912672793744181599953076370633/295375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24299371/50000000000000 : ℝ)*(upper1) + (11372789/100000000000000 : ℝ)*(lower3) + (32711483/100000000000000 : ℝ)*(upper4) + (5012293/25000000000000 : ℝ)*(lower5) + (1217005486046267/50000000000000 : ℝ)*(major0) + (1217005486046267/50000000000000 : ℝ)*(major1) + (1217005486046267/50000000000000 : ℝ)*(major2) + (371917363/12500000000000 : ℝ)*(sp0) + (50650935641/50000000000000 : ℝ)*(sp2) + (37198546863/100000000000000 : ℝ)*(sp3) + (1660599332942859/50000000000000 : ℝ)*(sp8) + (3321201641224623/100000000000000 : ℝ)*(sp9) + (3321100339353341/100000000000000 : ℝ)*(sp10) + (760080073984541/50000000000000 : ℝ)*(sp11) + (760098673257973/50000000000000 : ℝ)*(f.failure) + (3321201641224623/100000000000000 : ℝ)*(f.sum) + (38459988810827/5907500000000000000000000000 : ℝ)*base65 + (490786950195428517/69500000000000000000000000000000 : ℝ)*base67 + (776270446929428517/69500000000000000000000000000000 : ℝ)*base69 + (837770204559928517/69500000000000000000000000000000 : ℝ)*base71 + (965631100543/1476875000000000000000000000 : ℝ)*base73 + (428482225772928517/69500000000000000000000000000000 : ℝ)*base75 + (29303289474071483/69500000000000000000000000000000 : ℝ)*base78 + (39097946244928517/69500000000000000000000000000000 : ℝ)*base79 + (161320398894609/11815000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (3656851/5000000000000000000000 : ℝ)*base90 + (3656851/5000000000000000000000 : ℝ)*base92 + (3656851/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-42867/50000 : ℝ) ≤ (-506459777554843567012348124321667/590750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18109143/50000000000000 : ℝ)*(lower0) + (37952419/100000000000000 : ℝ)*(lower1) + (4303739/5000000000000 : ℝ)*(lower4) + (1236050739726433/50000000000000 : ℝ)*(major0) + (1236050739726433/50000000000000 : ℝ)*(major1) + (1236050739726433/50000000000000 : ℝ)*(major2) + (971836829/50000000000000 : ℝ)*(sp0) + (2186759187/4000000000000 : ℝ)*(sp5) + (102864905613/100000000000000 : ℝ)*(sp6) + (8442156693/50000000000000 : ℝ)*(sp7) + (857197725493981/25000000000000 : ℝ)*(sp12) + (3428738176669907/100000000000000 : ℝ)*(sp13) + (3428689980743969/100000000000000 : ℝ)*(sp14) + (61758817948919/4000000000000 : ℝ)*(sp15) + (1543987333036361/100000000000000 : ℝ)*(f.failure) + (1714396422824791/50000000000000 : ℝ)*(f.sum) + (2047396558973/5907500000000000000000000000 : ℝ)*base65 + (558167037373930817/69500000000000000000000000000000 : ℝ)*base68 + (307144865509430817/69500000000000000000000000000000 : ℝ)*base70 + (43352208844569183/69500000000000000000000000000000 : ℝ)*base71 + (366372180179/11815000000000000000000000000 : ℝ)*base74 + (128039785147430817/69500000000000000000000000000000 : ℝ)*base76 + (212225616036069183/69500000000000000000000000000000 : ℝ)*base77 + (500595097124430817/69500000000000000000000000000000 : ℝ)*base80 + (3628132976887/5907500000000000000000000000 : ℝ)*base82 + (43724193/10000000000000000000000 : ℝ)*base89 + (43724193/10000000000000000000000 : ℝ)*base91 + (43724193/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1471_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160111513/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15473/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10747/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63693/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14609/25000 : ℝ) else (39933/50000 : ℝ) ≤ X j i ∧ X j i ≤ (42867/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1471_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1471_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160111513/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (619/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2149/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63693/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14609/25000 : ℝ) else (39933/50000 : ℝ) ≤ X j i ∧ X j i ≤ (42867/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1471_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1471_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4437/1024 : ℝ) ≤ p) (hpb : p ≤ (4439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160111513/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (619/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2149/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63693/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14609/25000 : ℝ) else (39933/50000 : ℝ) ≤ X j i ∧ X j i ≤ (42867/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1471_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
