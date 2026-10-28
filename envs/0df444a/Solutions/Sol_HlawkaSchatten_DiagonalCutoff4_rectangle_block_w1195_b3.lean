-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1195_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:01:09.017335+00:00
-- url     : https://prove2.me/submissions/25b7537d-5fc4-41af-840c-f33c509215f0

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
theorem support_rectangle_w1195_s9_0 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2141798289/10000000000 : ℝ)*x 0 + (1078404323/2000000000 : ℝ)*x 1 + (5266600137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141798289/10000000000 : ℝ)^2097 ≤ (6509851007523/50000000000000 : ℝ)^1585 := by
    have hnat : (2141798289 : ℕ)^2097*50000000000000^1585 ≤ 6509851007523^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141798289 10000000000 6509851007523 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078404323/2000000000 : ℝ)^2097 ≤ (44167191404421/100000000000000 : ℝ)^1585 := by
    have hnat : (1078404323 : ℕ)^2097*100000000000000^1585 ≤ 44167191404421^1585*2000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078404323 2000000000 44167191404421 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266600137/10000000000 : ℝ)^2097 ≤ (21406553280449/50000000000000 : ℝ)^1585 := by
    have hnat : (5266600137 : ℕ)^2097*50000000000000^1585 ≤ 21406553280449^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266600137 10000000000 21406553280449 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2141798289/10000000000 : ℝ), (1078404323/2000000000 : ℝ), (5266600137/10000000000 : ℝ)] ![(6509851007523/50000000000000 : ℝ), (44167191404421/100000000000000 : ℝ), (21406553280449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2141798289/10000000000 : ℝ)|^2097 ≤ (6509851007523/50000000000000 : ℝ)^1585
        have hw : |(-2141798289/10000000000 : ℝ)|=(2141798289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078404323/2000000000 : ℝ)|^2097 ≤ (44167191404421/100000000000000 : ℝ)^1585
        have hw : |(1078404323/2000000000 : ℝ)|=(1078404323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266600137/10000000000 : ℝ)|^2097 ≤ (21406553280449/50000000000000 : ℝ)^1585
        have hw : |(5266600137/10000000000 : ℝ)|=(5266600137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s9_1 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344528431/10000000000 : ℝ)*x 0 + (-2205400639/10000000000 : ℝ)*x 1 + (5266600137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344528431/10000000000 : ℝ)^2097 ≤ (43653231669307/100000000000000 : ℝ)^1585 := by
    have hnat : (5344528431 : ℕ)^2097*100000000000000^1585 ≤ 43653231669307^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344528431 10000000000 43653231669307 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2205400639/10000000000 : ℝ)^2097 ≤ (6766830879497/50000000000000 : ℝ)^1585 := by
    have hnat : (2205400639 : ℕ)^2097*50000000000000^1585 ≤ 6766830879497^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205400639 10000000000 6766830879497 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266600137/10000000000 : ℝ)^2097 ≤ (21406553280449/50000000000000 : ℝ)^1585 := by
    have hnat : (5266600137 : ℕ)^2097*50000000000000^1585 ≤ 21406553280449^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266600137 10000000000 21406553280449 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344528431/10000000000 : ℝ), (-2205400639/10000000000 : ℝ), (5266600137/10000000000 : ℝ)] ![(43653231669307/100000000000000 : ℝ), (6766830879497/50000000000000 : ℝ), (21406553280449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344528431/10000000000 : ℝ)|^2097 ≤ (43653231669307/100000000000000 : ℝ)^1585
        have hw : |(5344528431/10000000000 : ℝ)|=(5344528431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2205400639/10000000000 : ℝ)|^2097 ≤ (6766830879497/50000000000000 : ℝ)^1585
        have hw : |(-2205400639/10000000000 : ℝ)|=(2205400639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266600137/10000000000 : ℝ)|^2097 ≤ (21406553280449/50000000000000 : ℝ)^1585
        have hw : |(5266600137/10000000000 : ℝ)|=(5266600137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s9_2 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344528431/10000000000 : ℝ)*x 0 + (5266600137/10000000000 : ℝ)*x 1 + (-2205400639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344528431/10000000000 : ℝ)^2097 ≤ (43653231669307/100000000000000 : ℝ)^1585 := by
    have hnat : (5344528431 : ℕ)^2097*100000000000000^1585 ≤ 43653231669307^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344528431 10000000000 43653231669307 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266600137/10000000000 : ℝ)^2097 ≤ (21406553280449/50000000000000 : ℝ)^1585 := by
    have hnat : (5266600137 : ℕ)^2097*50000000000000^1585 ≤ 21406553280449^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266600137 10000000000 21406553280449 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2205400639/10000000000 : ℝ)^2097 ≤ (6766830879497/50000000000000 : ℝ)^1585 := by
    have hnat : (2205400639 : ℕ)^2097*50000000000000^1585 ≤ 6766830879497^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205400639 10000000000 6766830879497 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344528431/10000000000 : ℝ), (5266600137/10000000000 : ℝ), (-2205400639/10000000000 : ℝ)] ![(43653231669307/100000000000000 : ℝ), (21406553280449/50000000000000 : ℝ), (6766830879497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344528431/10000000000 : ℝ)|^2097 ≤ (43653231669307/100000000000000 : ℝ)^1585
        have hw : |(5344528431/10000000000 : ℝ)|=(5344528431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266600137/10000000000 : ℝ)|^2097 ≤ (21406553280449/50000000000000 : ℝ)^1585
        have hw : |(5266600137/10000000000 : ℝ)|=(5266600137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2205400639/10000000000 : ℝ)|^2097 ≤ (6766830879497/50000000000000 : ℝ)^1585
        have hw : |(-2205400639/10000000000 : ℝ)|=(2205400639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s9_3 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1089315497/2500000000 : ℝ)*x 0 + (21164973/50000000 : ℝ)*x 1 + (4485113967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089315497/2500000000 : ℝ)^2097 ≤ (33317272952459/100000000000000 : ℝ)^1585 := by
    have hnat : (1089315497 : ℕ)^2097*100000000000000^1585 ≤ 33317272952459^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089315497 2500000000 33317272952459 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21164973/50000000 : ℝ)^2097 ≤ (2004122868369/6250000000000 : ℝ)^1585 := by
    have hnat : (21164973 : ℕ)^2097*6250000000000^1585 ≤ 2004122868369^1585*50000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21164973 50000000 2004122868369 6250000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4485113967/10000000000 : ℝ)^2097 ≤ (34616761141093/100000000000000 : ℝ)^1585 := by
    have hnat : (4485113967 : ℕ)^2097*100000000000000^1585 ≤ 34616761141093^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485113967 10000000000 34616761141093 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089315497/2500000000 : ℝ), (21164973/50000000 : ℝ), (4485113967/10000000000 : ℝ)] ![(33317272952459/100000000000000 : ℝ), (2004122868369/6250000000000 : ℝ), (34616761141093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089315497/2500000000 : ℝ)|^2097 ≤ (33317272952459/100000000000000 : ℝ)^1585
        have hw : |(1089315497/2500000000 : ℝ)|=(1089315497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21164973/50000000 : ℝ)|^2097 ≤ (2004122868369/6250000000000 : ℝ)^1585
        have hw : |(21164973/50000000 : ℝ)|=(21164973/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4485113967/10000000000 : ℝ)|^2097 ≤ (34616761141093/100000000000000 : ℝ)^1585
        have hw : |(4485113967/10000000000 : ℝ)|=(4485113967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s9_4 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1070901459/5000000000 : ℝ)*x 0 + (1316728957/2500000000 : ℝ)*x 1 + (2695852437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070901459/5000000000 : ℝ)^2097 ≤ (13019739243841/100000000000000 : ℝ)^1585 := by
    have hnat : (1070901459 : ℕ)^2097*100000000000000^1585 ≤ 13019739243841^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070901459 5000000000 13019739243841 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316728957/2500000000 : ℝ)^2097 ≤ (5352062736337/12500000000000 : ℝ)^1585 := by
    have hnat : (1316728957 : ℕ)^2097*12500000000000^1585 ≤ 5352062736337^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316728957 2500000000 5352062736337 12500000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695852437/5000000000 : ℝ)^2097 ≤ (44163758849571/100000000000000 : ℝ)^1585 := by
    have hnat : (2695852437 : ℕ)^2097*100000000000000^1585 ≤ 44163758849571^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695852437 5000000000 44163758849571 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1070901459/5000000000 : ℝ), (1316728957/2500000000 : ℝ), (2695852437/5000000000 : ℝ)] ![(13019739243841/100000000000000 : ℝ), (5352062736337/12500000000000 : ℝ), (44163758849571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1070901459/5000000000 : ℝ)|^2097 ≤ (13019739243841/100000000000000 : ℝ)^1585
        have hw : |(-1070901459/5000000000 : ℝ)|=(1070901459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316728957/2500000000 : ℝ)|^2097 ≤ (5352062736337/12500000000000 : ℝ)^1585
        have hw : |(1316728957/2500000000 : ℝ)|=(1316728957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695852437/5000000000 : ℝ)|^2097 ≤ (44163758849571/100000000000000 : ℝ)^1585
        have hw : |(2695852437/5000000000 : ℝ)|=(2695852437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s9_5 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (531263019/1000000000 : ℝ)*x 0 + (-2080296021/10000000000 : ℝ)*x 1 + (5391704831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531263019/1000000000 : ℝ)^2097 ≤ (5413607889269/12500000000000 : ℝ)^1585 := by
    have hnat : (531263019 : ℕ)^2097*12500000000000^1585 ≤ 5413607889269^1585*1000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531263019 1000000000 5413607889269 12500000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080296021/10000000000 : ℝ)^2097 ≤ (501095139487/4000000000000 : ℝ)^1585 := by
    have hnat : (2080296021 : ℕ)^2097*4000000000000^1585 ≤ 501095139487^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080296021 10000000000 501095139487 4000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391704831/10000000000 : ℝ)^2097 ≤ (2208187919179/5000000000000 : ℝ)^1585 := by
    have hnat : (5391704831 : ℕ)^2097*5000000000000^1585 ≤ 2208187919179^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391704831 10000000000 2208187919179 5000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531263019/1000000000 : ℝ), (-2080296021/10000000000 : ℝ), (5391704831/10000000000 : ℝ)] ![(5413607889269/12500000000000 : ℝ), (501095139487/4000000000000 : ℝ), (2208187919179/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531263019/1000000000 : ℝ)|^2097 ≤ (5413607889269/12500000000000 : ℝ)^1585
        have hw : |(531263019/1000000000 : ℝ)|=(531263019/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2080296021/10000000000 : ℝ)|^2097 ≤ (501095139487/4000000000000 : ℝ)^1585
        have hw : |(-2080296021/10000000000 : ℝ)|=(2080296021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391704831/10000000000 : ℝ)|^2097 ≤ (2208187919179/5000000000000 : ℝ)^1585
        have hw : |(5391704831/10000000000 : ℝ)|=(5391704831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s9_6 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656315323/5000000000 : ℝ)*x 0 + (2695852457/5000000000 : ℝ)*x 1 + (-2080295291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656315323/5000000000 : ℝ)^2097 ≤ (5413608504037/12500000000000 : ℝ)^1585 := by
    have hnat : (2656315323 : ℕ)^2097*12500000000000^1585 ≤ 5413608504037^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656315323 5000000000 5413608504037 12500000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695852457/5000000000 : ℝ)^2097 ≤ (44163759283051/100000000000000 : ℝ)^1585 := by
    have hnat : (2695852457 : ℕ)^2097*100000000000000^1585 ≤ 44163759283051^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695852457 5000000000 44163759283051 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2080295291/10000000000 : ℝ)^2097 ≤ (12527372671139/100000000000000 : ℝ)^1585 := by
    have hnat : (2080295291 : ℕ)^2097*100000000000000^1585 ≤ 12527372671139^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080295291 10000000000 12527372671139 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656315323/5000000000 : ℝ), (2695852457/5000000000 : ℝ), (-2080295291/10000000000 : ℝ)] ![(5413608504037/12500000000000 : ℝ), (44163759283051/100000000000000 : ℝ), (12527372671139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656315323/5000000000 : ℝ)|^2097 ≤ (5413608504037/12500000000000 : ℝ)^1585
        have hw : |(2656315323/5000000000 : ℝ)|=(2656315323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695852457/5000000000 : ℝ)|^2097 ≤ (44163759283051/100000000000000 : ℝ)^1585
        have hw : |(2695852457/5000000000 : ℝ)|=(2695852457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2080295291/10000000000 : ℝ)|^2097 ≤ (12527372671139/100000000000000 : ℝ)^1585
        have hw : |(-2080295291/10000000000 : ℝ)|=(2080295291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s9_7 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2178635953/5000000000 : ℝ)*x 0 + (4484479601/10000000000 : ℝ)*x 1 + (4233630891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178635953/5000000000 : ℝ)^2097 ≤ (33317373286707/100000000000000 : ℝ)^1585 := by
    have hnat : (2178635953 : ℕ)^2097*100000000000000^1585 ≤ 33317373286707^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178635953 5000000000 33317373286707 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484479601/10000000000 : ℝ)^2097 ≤ (865257089287/2500000000000 : ℝ)^1585 := by
    have hnat : (4484479601 : ℕ)^2097*2500000000000^1585 ≤ 865257089287^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484479601 10000000000 865257089287 2500000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4233630891/10000000000 : ℝ)^2097 ≤ (16036171562093/50000000000000 : ℝ)^1585 := by
    have hnat : (4233630891 : ℕ)^2097*50000000000000^1585 ≤ 16036171562093^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233630891 10000000000 16036171562093 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178635953/5000000000 : ℝ), (4484479601/10000000000 : ℝ), (4233630891/10000000000 : ℝ)] ![(33317373286707/100000000000000 : ℝ), (865257089287/2500000000000 : ℝ), (16036171562093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178635953/5000000000 : ℝ)|^2097 ≤ (33317373286707/100000000000000 : ℝ)^1585
        have hw : |(2178635953/5000000000 : ℝ)|=(2178635953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484479601/10000000000 : ℝ)|^2097 ≤ (865257089287/2500000000000 : ℝ)^1585
        have hw : |(4484479601/10000000000 : ℝ)|=(4484479601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4233630891/10000000000 : ℝ)|^2097 ≤ (16036171562093/50000000000000 : ℝ)^1585
        have hw : |(4233630891/10000000000 : ℝ)|=(4233630891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1195_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11421/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5711/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7039/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14079/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11421/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14079/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11421/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14079/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11421/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14079/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11421/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14079/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11421/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14079/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11421/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11421/100000 : ℝ) ^ (8387/2048 : ℝ) ≤ (6919360795892153/50000000000000000000 : ℝ) := by
    have hpowers : (11421/100000 : ℝ)^8387 ≤ (6919360795892153/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11421 : ℕ)^8387*50000000000000000000^2048 ≤ 6919360795892153^2048*100000^8387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11421 100000 6919360795892153 50000000000000000000 8387 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11421/100000 : ℝ)) (X := (6919360795892153/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14079/100000 : ℝ) ^ (8387/2048 : ℝ) ≤ (8150019394451239/25000000000000000000 : ℝ) := by
    have hpowers : (14079/100000 : ℝ)^8387 ≤ (8150019394451239/25000000000000000000 : ℝ)^2048 := by
      have hnat : (14079 : ℕ)^8387*25000000000000000000^2048 ≤ 8150019394451239^2048*100000^8387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14079 100000 8150019394451239 25000000000000000000 8387 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14079/100000 : ℝ)) (X := (8150019394451239/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006919360795892153/25000000000000000000 : ℝ) ≤ (10000675777701337/10000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (25006919360795892153/25000000000000000000 : ℝ)^2048 ≤ (10000675777701337/10000000000000000 : ℝ)^8387 := by
      have hnat : (25006919360795892153 : ℕ)^2048*10000000000000000^8387 ≤ 10000675777701337^8387*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006919360795892153 25000000000000000000 10000675777701337 10000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000675777701337/10000000000000000 : ℝ)) (X := (25006919360795892153/25000000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023219399584794631/50000000000000000000 : ℝ) ≤ (5000566889081183/5000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (50023219399584794631/50000000000000000000 : ℝ)^2048 ≤ (5000566889081183/5000000000000000 : ℝ)^8387 := by
      have hnat : (50023219399584794631 : ℕ)^2048*5000000000000000^8387 ≤ 5000566889081183^8387*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023219399584794631 50000000000000000000 5000566889081183 5000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000566889081183/5000000000000000 : ℝ)) (X := (50023219399584794631/50000000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508150019394451239/12500000000000000000 : ℝ) ≤ (2000318355724679/2000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (12508150019394451239/12500000000000000000 : ℝ)^2048 ≤ (2000318355724679/2000000000000000 : ℝ)^8387 := by
      have hnat : (12508150019394451239 : ℕ)^2048*2000000000000000^8387 ≤ 2000318355724679^8387*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508150019394451239 12500000000000000000 2000318355724679 2000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000318355724679/2000000000000000 : ℝ)) (X := (12508150019394451239/12500000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6919360795892153/50000000000000000000 : ℝ) ≤ ((553569470220819361/553750000000000000 : ℝ)+2*(152666820343/88600000000000 : ℝ)*(11421/100000 : ℝ))^(8387/2048 : ℝ) := by
    rw [show (553569470220819361/553750000000000000 : ℝ)+2*(152666820343/88600000000000 : ℝ)*(11421/100000 : ℝ)=(10000675777701337/10000000000000000 : ℝ) by norm_num, show 1+2*(6919360795892153/50000000000000000000 : ℝ)=(25006919360795892153/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8150019394451239/25000000000000000000 : ℝ)+(6919360795892153/50000000000000000000 : ℝ) ≤ ((553569470220819361/553750000000000000 : ℝ)+(152666820343/88600000000000 : ℝ)*((14079/100000 : ℝ)+(11421/100000 : ℝ)))^(8387/2048 : ℝ) := by
    rw [show (553569470220819361/553750000000000000 : ℝ)+(152666820343/88600000000000 : ℝ)*((14079/100000 : ℝ)+(11421/100000 : ℝ))=(5000566889081183/5000000000000000 : ℝ) by norm_num, show 1+(8150019394451239/25000000000000000000 : ℝ)+(6919360795892153/50000000000000000000 : ℝ)=(50023219399584794631/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8150019394451239/25000000000000000000 : ℝ) ≤ ((553569470220819361/553750000000000000 : ℝ)+2*(152666820343/88600000000000 : ℝ)*(14079/100000 : ℝ))^(8387/2048 : ℝ) := by
    rw [show (553569470220819361/553750000000000000 : ℝ)+2*(152666820343/88600000000000 : ℝ)*(14079/100000 : ℝ)=(2000318355724679/2000000000000000 : ℝ) by norm_num, show 1+2*(8150019394451239/25000000000000000000 : ℝ)=(12508150019394451239/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (553569470220819361/553750000000000000 : ℝ)*(X 1 0+X 2 0)+(152666820343/88600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (11421/100000 : ℝ)) (hi := (14079/100000 : ℝ)) (c := (553569470220819361/553750000000000000 : ℝ)) (alpha := (152666820343/88600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (553569470220819361/553750000000000000 : ℝ)*(X 0 1+X 2 1)+(152666820343/88600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (11421/100000 : ℝ)) (hi := (14079/100000 : ℝ)) (c := (553569470220819361/553750000000000000 : ℝ)) (alpha := (152666820343/88600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (553569470220819361/553750000000000000 : ℝ)*(X 0 2+X 1 2)+(152666820343/88600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (11421/100000 : ℝ)) (hi := (14079/100000 : ℝ)) (c := (553569470220819361/553750000000000000 : ℝ)) (alpha := (152666820343/88600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2141798289/10000000000 : ℝ)*X 0 0+(1078404323/2000000000 : ℝ)*X 0 1+(5266600137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344528431/10000000000 : ℝ)*X 1 0+(-2205400639/10000000000 : ℝ)*X 1 1+(5266600137/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344528431/10000000000 : ℝ)*X 2 0+(5266600137/10000000000 : ℝ)*X 2 1+(-2205400639/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1089315497/2500000000 : ℝ)*X 0 0+(21164973/50000000 : ℝ)*X 0 1+(4485113967/10000000000 : ℝ)*X 0 2+(1089315497/2500000000 : ℝ)*X 1 0+(21164973/50000000 : ℝ)*X 1 1+(4485113967/10000000000 : ℝ)*X 1 2+(1089315497/2500000000 : ℝ)*X 2 0+(21164973/50000000 : ℝ)*X 2 1+(4485113967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1070901459/5000000000 : ℝ)*X 0 0+(1316728957/2500000000 : ℝ)*X 0 1+(2695852437/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531263019/1000000000 : ℝ)*X 1 0+(-2080296021/10000000000 : ℝ)*X 1 1+(5391704831/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s9_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656315323/5000000000 : ℝ)*X 2 0+(2695852457/5000000000 : ℝ)*X 2 1+(-2080295291/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s9_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2178635953/5000000000 : ℝ)*X 0 0+(4484479601/10000000000 : ℝ)*X 0 1+(4233630891/10000000000 : ℝ)*X 0 2+(2178635953/5000000000 : ℝ)*X 1 0+(4484479601/10000000000 : ℝ)*X 1 1+(4233630891/10000000000 : ℝ)*X 1 2+(2178635953/5000000000 : ℝ)*X 2 0+(4484479601/10000000000 : ℝ)*X 2 1+(4233630891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s9_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15539505473552246577542649/6921875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (88645837/20000000000000 : ℝ)*(base19) + (412636989/100000000000000 : ℝ)*(base23) + (8175043/50000000000000 : ℝ)*(lower2) + (57256177/100000000000000 : ℝ)*(upper3) + (17361941/50000000000000 : ℝ)*(upper5) + (1492441095248947/25000000000000 : ℝ)*(major0) + (1492441095248947/25000000000000 : ℝ)*(major1) + (1492441095248947/25000000000000 : ℝ)*(major2) + (7973128829559691/100000000000000 : ℝ)*(sp0) + (3986570289733799/50000000000000 : ℝ)*(sp1) + (3986570305029897/50000000000000 : ℝ)*(sp2) + (3966381093278187/100000000000000 : ℝ)*(sp3) + (12193137091/100000000000000 : ℝ)*(sp4) + (1642795941/25000000000000 : ℝ)*(sp7) + (30987403628609/781250000000 : ℝ)*(f.failure) + (3986570511348391/50000000000000 : ℝ)*(f.sum) + (5528397665497/2215000000000000000000000000 : ℝ)*base65 + (68857205798374633/13843750000000000000000000000000 : ℝ)*base68 + (100070252666906617/13843750000000000000000000000000 : ℝ)*base69 + (28305388906531617/13843750000000000000000000000000 : ℝ)*base71 + (1032252543347/553750000000000000000000000 : ℝ)*base74 + (240602288161437867/13843750000000000000000000000000 : ℝ)*base75 + (10464609441906617/13843750000000000000000000000000 : ℝ)*base77 + (100588388548218383/13843750000000000000000000000000 : ℝ)*base80 + (5877939098437/2215000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (132179/9765625000000000000 : ℝ)*base89 + (132179/9765625000000000000 : ℝ)*base91 + (132179/9765625000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3294440158456467457129161/6921875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (235769737/100000000000000 : ℝ)*(base19) + (413920987/25000000000000 : ℝ)*(base23) + (34380447/100000000000000 : ℝ)*(lower2) + (74191493/100000000000000 : ℝ)*(upper3) + (106832619/50000000000000 : ℝ)*(lower4) + (6000001999683909/100000000000000 : ℝ)*(major0) + (6000001999683909/100000000000000 : ℝ)*(major1) + (6000001999683909/100000000000000 : ℝ)*(major2) + (6572444093/10000000000000 : ℝ)*(sp2) + (605052783/20000000000000 : ℝ)*(sp3) + (4006763029586297/50000000000000 : ℝ)*(sp4) + (8013525823402857/100000000000000 : ℝ)*(sp5) + (2003364669761929/25000000000000 : ℝ)*(sp6) + (3986474899066427/100000000000000 : ℝ)*(sp7) + (1993238962165171/50000000000000 : ℝ)*(f.failure) + (4006763029586297/50000000000000 : ℝ)*(f.sum) + (35391425842913/4430000000000000000000000000 : ℝ)*base66 + (424220713424844101/55375000000000000000000000000000 : ℝ)*base68 + (988541134154469101/55375000000000000000000000000000 : ℝ)*base70 + (235783763940280899/55375000000000000000000000000000 : ℝ)*base71 + (6598858090113/4430000000000000000000000000 : ℝ)*base74 + (405391384388594101/55375000000000000000000000000000 : ℝ)*base76 + (841400225240719101/55375000000000000000000000000000 : ℝ)*base78 + (726660468285594101/55375000000000000000000000000000 : ℝ)*base80 + (20060542766693/4430000000000000000000000000 : ℝ)*base82 + (1433313/312500000000000000000 : ℝ)*base89 + (1433313/312500000000000000000 : ℝ)*base91 + (1433313/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1195_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11421/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5711/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1195_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1195_box_0 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2016633103/10000000000 : ℝ)*x 0 + (5375539121/10000000000 : ℝ)*x 1 + (5375539067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2016633103/10000000000 : ℝ)^2097 ≤ (2404537924201/20000000000000 : ℝ)^1585 := by
    have hnat : (2016633103 : ℕ)^2097*20000000000000^1585 ≤ 2404537924201^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016633103 10000000000 2404537924201 20000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375539121/10000000000 : ℝ)^2097 ≤ (43988655475533/100000000000000 : ℝ)^1585 := by
    have hnat : (5375539121 : ℕ)^2097*100000000000000^1585 ≤ 43988655475533^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375539121 10000000000 43988655475533 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375539067/10000000000 : ℝ)^2097 ≤ (43988654890903/100000000000000 : ℝ)^1585 := by
    have hnat : (5375539067 : ℕ)^2097*100000000000000^1585 ≤ 43988654890903^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375539067 10000000000 43988654890903 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2016633103/10000000000 : ℝ), (5375539121/10000000000 : ℝ), (5375539067/10000000000 : ℝ)] ![(2404537924201/20000000000000 : ℝ), (43988655475533/100000000000000 : ℝ), (43988654890903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2016633103/10000000000 : ℝ)|^2097 ≤ (2404537924201/20000000000000 : ℝ)^1585
        have hw : |(-2016633103/10000000000 : ℝ)|=(2016633103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375539121/10000000000 : ℝ)|^2097 ≤ (43988655475533/100000000000000 : ℝ)^1585
        have hw : |(5375539121/10000000000 : ℝ)|=(5375539121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375539067/10000000000 : ℝ)|^2097 ≤ (43988654890903/100000000000000 : ℝ)^1585
        have hw : |(5375539067/10000000000 : ℝ)|=(5375539067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_box_1 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5296445921/10000000000 : ℝ)*x 0 + (-2124024569/10000000000 : ℝ)*x 1 + (5375539183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296445921/10000000000 : ℝ)^2097 ≤ (43134395202493/100000000000000 : ℝ)^1585 := by
    have hnat : (5296445921 : ℕ)^2097*100000000000000^1585 ≤ 43134395202493^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296445921 10000000000 43134395202493 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2124024569/10000000000 : ℝ)^2097 ≤ (12876948637199/100000000000000 : ℝ)^1585 := by
    have hnat : (2124024569 : ℕ)^2097*100000000000000^1585 ≤ 12876948637199^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124024569 10000000000 12876948637199 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375539183/10000000000 : ℝ)^2097 ≤ (5498582018347/12500000000000 : ℝ)^1585 := by
    have hnat : (5375539183 : ℕ)^2097*12500000000000^1585 ≤ 5498582018347^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375539183 10000000000 5498582018347 12500000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296445921/10000000000 : ℝ), (-2124024569/10000000000 : ℝ), (5375539183/10000000000 : ℝ)] ![(43134395202493/100000000000000 : ℝ), (12876948637199/100000000000000 : ℝ), (5498582018347/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296445921/10000000000 : ℝ)|^2097 ≤ (43134395202493/100000000000000 : ℝ)^1585
        have hw : |(5296445921/10000000000 : ℝ)|=(5296445921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2124024569/10000000000 : ℝ)|^2097 ≤ (12876948637199/100000000000000 : ℝ)^1585
        have hw : |(-2124024569/10000000000 : ℝ)|=(2124024569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375539183/10000000000 : ℝ)|^2097 ≤ (5498582018347/12500000000000 : ℝ)^1585
        have hw : |(5375539183/10000000000 : ℝ)|=(5375539183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_box_2 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5296445601/10000000000 : ℝ)*x 0 + (1343884853/2500000000 : ℝ)*x 1 + (-212402469/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296445601/10000000000 : ℝ)^2097 ≤ (10783597938641/25000000000000 : ℝ)^1585 := by
    have hnat : (5296445601 : ℕ)^2097*25000000000000^1585 ≤ 10783597938641^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296445601 10000000000 10783597938641 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1343884853/2500000000 : ℝ)^2097 ≤ (43988658626043/100000000000000 : ℝ)^1585 := by
    have hnat : (1343884853 : ℕ)^2097*100000000000000^1585 ≤ 43988658626043^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343884853 2500000000 43988658626043 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212402469/1000000000 : ℝ)^2097 ≤ (6438474803863/50000000000000 : ℝ)^1585 := by
    have hnat : (212402469 : ℕ)^2097*50000000000000^1585 ≤ 6438474803863^1585*1000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212402469 1000000000 6438474803863 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296445601/10000000000 : ℝ), (1343884853/2500000000 : ℝ), (-212402469/1000000000 : ℝ)] ![(10783597938641/25000000000000 : ℝ), (43988658626043/100000000000000 : ℝ), (6438474803863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296445601/10000000000 : ℝ)|^2097 ≤ (10783597938641/25000000000000 : ℝ)^1585
        have hw : |(5296445601/10000000000 : ℝ)|=(5296445601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1343884853/2500000000 : ℝ)|^2097 ≤ (43988658626043/100000000000000 : ℝ)^1585
        have hw : |(1343884853/2500000000 : ℝ)|=(1343884853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-212402469/1000000000 : ℝ)|^2097 ≤ (6438474803863/50000000000000 : ℝ)^1585
        have hw : |(-212402469/1000000000 : ℝ)|=(212402469/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_box_3 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2232124287/5000000000 : ℝ)*x 0 + (269115043/625000000 : ℝ)*x 1 + (4305840883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2232124287/5000000000 : ℝ)^2097 ≤ (6880771617349/20000000000000 : ℝ)^1585 := by
    have hnat : (2232124287 : ℕ)^2097*20000000000000^1585 ≤ 6880771617349^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2232124287 5000000000 6880771617349 20000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269115043/625000000 : ℝ)^2097 ≤ (2049879372891/6250000000000 : ℝ)^1585 := by
    have hnat : (269115043 : ℕ)^2097*6250000000000^1585 ≤ 2049879372891^1585*625000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269115043 625000000 2049879372891 6250000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4305840883/10000000000 : ℝ)^2097 ≤ (16399035965699/50000000000000 : ℝ)^1585 := by
    have hnat : (4305840883 : ℕ)^2097*50000000000000^1585 ≤ 16399035965699^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305840883 10000000000 16399035965699 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2232124287/5000000000 : ℝ), (269115043/625000000 : ℝ), (4305840883/10000000000 : ℝ)] ![(6880771617349/20000000000000 : ℝ), (2049879372891/6250000000000 : ℝ), (16399035965699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2232124287/5000000000 : ℝ)|^2097 ≤ (6880771617349/20000000000000 : ℝ)^1585
        have hw : |(2232124287/5000000000 : ℝ)|=(2232124287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269115043/625000000 : ℝ)|^2097 ≤ (2049879372891/6250000000000 : ℝ)^1585
        have hw : |(269115043/625000000 : ℝ)|=(269115043/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4305840883/10000000000 : ℝ)|^2097 ≤ (16399035965699/50000000000000 : ℝ)^1585
        have hw : |(4305840883/10000000000 : ℝ)|=(4305840883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_box_4 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2268346591/10000000000 : ℝ)*x 0 + (2640891069/5000000000 : ℝ)*x 1 + (5281783243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2268346591/10000000000 : ℝ)^2097 ≤ (1404705430561/10000000000000 : ℝ)^1585 := by
    have hnat : (2268346591 : ℕ)^2097*10000000000000^1585 ≤ 1404705430561^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2268346591 10000000000 1404705430561 10000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640891069/5000000000 : ℝ)^2097 ≤ (42976466891171/100000000000000 : ℝ)^1585 := by
    have hnat : (2640891069 : ℕ)^2097*100000000000000^1585 ≤ 42976466891171^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640891069 5000000000 42976466891171 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281783243/10000000000 : ℝ)^2097 ≤ (42976478786643/100000000000000 : ℝ)^1585 := by
    have hnat : (5281783243 : ℕ)^2097*100000000000000^1585 ≤ 42976478786643^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281783243 10000000000 42976478786643 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2268346591/10000000000 : ℝ), (2640891069/5000000000 : ℝ), (5281783243/10000000000 : ℝ)] ![(1404705430561/10000000000000 : ℝ), (42976466891171/100000000000000 : ℝ), (42976478786643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2268346591/10000000000 : ℝ)|^2097 ≤ (1404705430561/10000000000000 : ℝ)^1585
        have hw : |(-2268346591/10000000000 : ℝ)|=(2268346591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640891069/5000000000 : ℝ)|^2097 ≤ (42976466891171/100000000000000 : ℝ)^1585
        have hw : |(2640891069/5000000000 : ℝ)|=(2640891069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281783243/10000000000 : ℝ)|^2097 ≤ (42976478786643/100000000000000 : ℝ)^1585
        have hw : |(5281783243/10000000000 : ℝ)|=(5281783243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_box_5 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5362606429/10000000000 : ℝ)*x 0 + (-1080529473/5000000000 : ℝ)*x 1 + (5281782909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362606429/10000000000 : ℝ)^2097 ≤ (8769738840883/20000000000000 : ℝ)^1585 := by
    have hnat : (5362606429 : ℕ)^2097*20000000000000^1585 ≤ 8769738840883^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362606429 10000000000 8769738840883 20000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080529473/5000000000 : ℝ)^2097 ≤ (13174830589413/100000000000000 : ℝ)^1585 := by
    have hnat : (1080529473 : ℕ)^2097*100000000000000^1585 ≤ 13174830589413^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080529473 5000000000 13174830589413 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281782909/10000000000 : ℝ)^2097 ≤ (42976475191089/100000000000000 : ℝ)^1585 := by
    have hnat : (5281782909 : ℕ)^2097*100000000000000^1585 ≤ 42976475191089^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281782909 10000000000 42976475191089 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362606429/10000000000 : ℝ), (-1080529473/5000000000 : ℝ), (5281782909/10000000000 : ℝ)] ![(8769738840883/20000000000000 : ℝ), (13174830589413/100000000000000 : ℝ), (42976475191089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362606429/10000000000 : ℝ)|^2097 ≤ (8769738840883/20000000000000 : ℝ)^1585
        have hw : |(5362606429/10000000000 : ℝ)|=(5362606429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1080529473/5000000000 : ℝ)|^2097 ≤ (13174830589413/100000000000000 : ℝ)^1585
        have hw : |(-1080529473/5000000000 : ℝ)|=(1080529473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281782909/10000000000 : ℝ)|^2097 ≤ (42976475191089/100000000000000 : ℝ)^1585
        have hw : |(5281782909/10000000000 : ℝ)|=(5281782909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_box_6 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5362605857/10000000000 : ℝ)*x 0 + (2640891561/5000000000 : ℝ)*x 1 + (-2161059429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362605857/10000000000 : ℝ)^2097 ≤ (43848688016477/100000000000000 : ℝ)^1585 := by
    have hnat : (5362605857 : ℕ)^2097*100000000000000^1585 ≤ 43848688016477^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362605857 10000000000 43848688016477 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640891561/5000000000 : ℝ)^2097 ≤ (21488238742031/50000000000000 : ℝ)^1585 := by
    have hnat : (2640891561 : ℕ)^2097*50000000000000^1585 ≤ 21488238742031^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640891561 5000000000 21488238742031 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2161059429/10000000000 : ℝ)^2097 ≤ (3293708621299/25000000000000 : ℝ)^1585 := by
    have hnat : (2161059429 : ℕ)^2097*25000000000000^1585 ≤ 3293708621299^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161059429 10000000000 3293708621299 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362605857/10000000000 : ℝ), (2640891561/5000000000 : ℝ), (-2161059429/10000000000 : ℝ)] ![(43848688016477/100000000000000 : ℝ), (21488238742031/50000000000000 : ℝ), (3293708621299/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362605857/10000000000 : ℝ)|^2097 ≤ (43848688016477/100000000000000 : ℝ)^1585
        have hw : |(5362605857/10000000000 : ℝ)|=(5362605857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640891561/5000000000 : ℝ)|^2097 ≤ (21488238742031/50000000000000 : ℝ)^1585
        have hw : |(2640891561/5000000000 : ℝ)|=(2640891561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2161059429/10000000000 : ℝ)|^2097 ≤ (3293708621299/25000000000000 : ℝ)^1585
        have hw : |(-2161059429/10000000000 : ℝ)|=(2161059429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_box_7 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (531236599/1250000000 : ℝ)*x 0 + (4412998213/10000000000 : ℝ)*x 1 + (2206499139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531236599/1250000000 : ℝ)^2097 ≤ (32235433109233/100000000000000 : ℝ)^1585 := by
    have hnat : (531236599 : ℕ)^2097*100000000000000^1585 ≤ 32235433109233^1585*1250000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531236599 1250000000 32235433109233 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4412998213/10000000000 : ℝ)^2097 ≤ (33882283106453/100000000000000 : ℝ)^1585 := by
    have hnat : (4412998213 : ℕ)^2097*100000000000000^1585 ≤ 33882283106453^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4412998213 10000000000 33882283106453 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2206499139/5000000000 : ℝ)^2097 ≤ (16941141883361/50000000000000 : ℝ)^1585 := by
    have hnat : (2206499139 : ℕ)^2097*50000000000000^1585 ≤ 16941141883361^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206499139 5000000000 16941141883361 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531236599/1250000000 : ℝ), (4412998213/10000000000 : ℝ), (2206499139/5000000000 : ℝ)] ![(32235433109233/100000000000000 : ℝ), (33882283106453/100000000000000 : ℝ), (16941141883361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531236599/1250000000 : ℝ)|^2097 ≤ (32235433109233/100000000000000 : ℝ)^1585
        have hw : |(531236599/1250000000 : ℝ)|=(531236599/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4412998213/10000000000 : ℝ)|^2097 ≤ (33882283106453/100000000000000 : ℝ)^1585
        have hw : |(4412998213/10000000000 : ℝ)|=(4412998213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2206499139/5000000000 : ℝ)|^2097 ≤ (16941141883361/50000000000000 : ℝ)^1585
        have hw : |(2206499139/5000000000 : ℝ)|=(2206499139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_box_8 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-553912529/2500000000 : ℝ)*x 0 + (5217919151/10000000000 : ℝ)*x 1 + (269257519/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (553912529/2500000000 : ℝ)^2097 ≤ (851058662251/6250000000000 : ℝ)^1585 := by
    have hnat : (553912529 : ℕ)^2097*6250000000000^1585 ≤ 851058662251^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553912529 2500000000 851058662251 6250000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217919151/10000000000 : ℝ)^2097 ≤ (422903196449/1000000000000 : ℝ)^1585 := by
    have hnat : (5217919151 : ℕ)^2097*1000000000000^1585 ≤ 422903196449^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217919151 10000000000 422903196449 1000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269257519/500000000 : ℝ)^2097 ≤ (22046370873651/50000000000000 : ℝ)^1585 := by
    have hnat : (269257519 : ℕ)^2097*50000000000000^1585 ≤ 22046370873651^1585*500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269257519 500000000 22046370873651 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-553912529/2500000000 : ℝ), (5217919151/10000000000 : ℝ), (269257519/500000000 : ℝ)] ![(851058662251/6250000000000 : ℝ), (422903196449/1000000000000 : ℝ), (22046370873651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-553912529/2500000000 : ℝ)|^2097 ≤ (851058662251/6250000000000 : ℝ)^1585
        have hw : |(-553912529/2500000000 : ℝ)|=(553912529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217919151/10000000000 : ℝ)|^2097 ≤ (422903196449/1000000000000 : ℝ)^1585
        have hw : |(5217919151/10000000000 : ℝ)|=(5217919151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269257519/500000000 : ℝ)|^2097 ≤ (22046370873651/50000000000000 : ℝ)^1585
        have hw : |(269257519/500000000 : ℝ)|=(269257519/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_box_9 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (528966031/1000000000 : ℝ)*x 0 + (-2120160159/10000000000 : ℝ)*x 1 + (673143793/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528966031/1000000000 : ℝ)^2097 ≤ (2691331055199/6250000000000 : ℝ)^1585 := by
    have hnat : (528966031 : ℕ)^2097*6250000000000^1585 ≤ 2691331055199^1585*1000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528966031 1000000000 2691331055199 6250000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2120160159/10000000000 : ℝ)^2097 ≤ (802872608723/6250000000000 : ℝ)^1585 := by
    have hnat : (2120160159 : ℕ)^2097*6250000000000^1585 ≤ 802872608723^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120160159 10000000000 802872608723 6250000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673143793/1250000000 : ℝ)^2097 ≤ (11023185339331/25000000000000 : ℝ)^1585 := by
    have hnat : (673143793 : ℕ)^2097*25000000000000^1585 ≤ 11023185339331^1585*1250000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673143793 1250000000 11023185339331 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528966031/1000000000 : ℝ), (-2120160159/10000000000 : ℝ), (673143793/1250000000 : ℝ)] ![(2691331055199/6250000000000 : ℝ), (802872608723/6250000000000 : ℝ), (11023185339331/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528966031/1000000000 : ℝ)|^2097 ≤ (2691331055199/6250000000000 : ℝ)^1585
        have hw : |(528966031/1000000000 : ℝ)|=(528966031/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2120160159/10000000000 : ℝ)|^2097 ≤ (802872608723/6250000000000 : ℝ)^1585
        have hw : |(-2120160159/10000000000 : ℝ)|=(2120160159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673143793/1250000000 : ℝ)|^2097 ≤ (11023185339331/25000000000000 : ℝ)^1585
        have hw : |(673143793/1250000000 : ℝ)|=(673143793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_box_10 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5289660367/10000000000 : ℝ)*x 0 + (5385150393/10000000000 : ℝ)*x 1 + (-132510001/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289660367/10000000000 : ℝ)^2097 ≤ (10765324374273/25000000000000 : ℝ)^1585 := by
    have hnat : (5289660367 : ℕ)^2097*25000000000000^1585 ≤ 10765324374273^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289660367 10000000000 10765324374273 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385150393/10000000000 : ℝ)^2097 ≤ (344474546001/781250000000 : ℝ)^1585 := by
    have hnat : (5385150393 : ℕ)^2097*781250000000^1585 ≤ 344474546001^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385150393 10000000000 344474546001 781250000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132510001/625000000 : ℝ)^2097 ≤ (2569192118651/20000000000000 : ℝ)^1585 := by
    have hnat : (132510001 : ℕ)^2097*20000000000000^1585 ≤ 2569192118651^1585*625000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132510001 625000000 2569192118651 20000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289660367/10000000000 : ℝ), (5385150393/10000000000 : ℝ), (-132510001/625000000 : ℝ)] ![(10765324374273/25000000000000 : ℝ), (344474546001/781250000000 : ℝ), (2569192118651/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289660367/10000000000 : ℝ)|^2097 ≤ (10765324374273/25000000000000 : ℝ)^1585
        have hw : |(5289660367/10000000000 : ℝ)|=(5289660367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385150393/10000000000 : ℝ)|^2097 ≤ (344474546001/781250000000 : ℝ)^1585
        have hw : |(5385150393/10000000000 : ℝ)|=(5385150393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-132510001/625000000 : ℝ)|^2097 ≤ (2569192118651/20000000000000 : ℝ)^1585
        have hw : |(-132510001/625000000 : ℝ)|=(132510001/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_box_11 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (560743699/1250000000 : ℝ)*x 0 + (2147424843/5000000000 : ℝ)*x 1 + (2147424917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (560743699/1250000000 : ℝ)^2097 ≤ (34625294236569/100000000000000 : ℝ)^1585 := by
    have hnat : (560743699 : ℕ)^2097*100000000000000^1585 ≤ 34625294236569^1585*1250000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560743699 1250000000 34625294236569 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2147424843/5000000000 : ℝ)^2097 ≤ (32687352129631/100000000000000 : ℝ)^1585 := by
    have hnat : (2147424843 : ℕ)^2097*100000000000000^1585 ≤ 32687352129631^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147424843 5000000000 32687352129631 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2147424917/5000000000 : ℝ)^2097 ≤ (32687353619893/100000000000000 : ℝ)^1585 := by
    have hnat : (2147424917 : ℕ)^2097*100000000000000^1585 ≤ 32687353619893^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147424917 5000000000 32687353619893 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(560743699/1250000000 : ℝ), (2147424843/5000000000 : ℝ), (2147424917/5000000000 : ℝ)] ![(34625294236569/100000000000000 : ℝ), (32687352129631/100000000000000 : ℝ), (32687353619893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(560743699/1250000000 : ℝ)|^2097 ≤ (34625294236569/100000000000000 : ℝ)^1585
        have hw : |(560743699/1250000000 : ℝ)|=(560743699/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2147424843/5000000000 : ℝ)|^2097 ≤ (32687352129631/100000000000000 : ℝ)^1585
        have hw : |(2147424843/5000000000 : ℝ)|=(2147424843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2147424917/5000000000 : ℝ)|^2097 ≤ (32687353619893/100000000000000 : ℝ)^1585
        have hw : |(2147424917/5000000000 : ℝ)|=(2147424917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_box_12 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2069616019/10000000000 : ℝ)*x 0 + (5438162581/10000000000 : ℝ)*x 1 + (527372201/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2069616019/10000000000 : ℝ)^2097 ≤ (1555294963227/12500000000000 : ℝ)^1585 := by
    have hnat : (2069616019 : ℕ)^2097*12500000000000^1585 ≤ 1555294963227^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069616019 10000000000 1555294963227 12500000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438162581/10000000000 : ℝ)^2097 ≤ (8933584067077/20000000000000 : ℝ)^1585 := by
    have hnat : (5438162581 : ℕ)^2097*20000000000000^1585 ≤ 8933584067077^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438162581 10000000000 8933584067077 20000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527372201/1000000000 : ℝ)^2097 ≤ (42889719936867/100000000000000 : ℝ)^1585 := by
    have hnat : (527372201 : ℕ)^2097*100000000000000^1585 ≤ 42889719936867^1585*1000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527372201 1000000000 42889719936867 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2069616019/10000000000 : ℝ), (5438162581/10000000000 : ℝ), (527372201/1000000000 : ℝ)] ![(1555294963227/12500000000000 : ℝ), (8933584067077/20000000000000 : ℝ), (42889719936867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2069616019/10000000000 : ℝ)|^2097 ≤ (1555294963227/12500000000000 : ℝ)^1585
        have hw : |(-2069616019/10000000000 : ℝ)|=(2069616019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438162581/10000000000 : ℝ)|^2097 ≤ (8933584067077/20000000000000 : ℝ)^1585
        have hw : |(5438162581/10000000000 : ℝ)|=(5438162581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(527372201/1000000000 : ℝ)|^2097 ≤ (42889719936867/100000000000000 : ℝ)^1585
        have hw : |(527372201/1000000000 : ℝ)|=(527372201/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_box_13 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5368292361/10000000000 : ℝ)*x 0 + (-1082093441/5000000000 : ℝ)*x 1 + (164803809/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368292361/10000000000 : ℝ)^2097 ≤ (10977553890679/25000000000000 : ℝ)^1585 := by
    have hnat : (5368292361 : ℕ)^2097*25000000000000^1585 ≤ 10977553890679^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368292361 10000000000 10977553890679 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082093441/5000000000 : ℝ)^2097 ≤ (6600032899961/50000000000000 : ℝ)^1585 := by
    have hnat : (1082093441 : ℕ)^2097*50000000000000^1585 ≤ 6600032899961^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082093441 5000000000 6600032899961 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164803809/312500000 : ℝ)^2097 ≤ (5361214828021/12500000000000 : ℝ)^1585 := by
    have hnat : (164803809 : ℕ)^2097*12500000000000^1585 ≤ 5361214828021^1585*312500000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164803809 312500000 5361214828021 12500000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368292361/10000000000 : ℝ), (-1082093441/5000000000 : ℝ), (164803809/312500000 : ℝ)] ![(10977553890679/25000000000000 : ℝ), (6600032899961/50000000000000 : ℝ), (5361214828021/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368292361/10000000000 : ℝ)|^2097 ≤ (10977553890679/25000000000000 : ℝ)^1585
        have hw : |(5368292361/10000000000 : ℝ)|=(5368292361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1082093441/5000000000 : ℝ)|^2097 ≤ (6600032899961/50000000000000 : ℝ)^1585
        have hw : |(-1082093441/5000000000 : ℝ)|=(1082093441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164803809/312500000 : ℝ)|^2097 ≤ (5361214828021/12500000000000 : ℝ)^1585
        have hw : |(164803809/312500000 : ℝ)|=(164803809/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_box_14 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5368292393/10000000000 : ℝ)*x 0 + (1054744369/2000000000 : ℝ)*x 1 + (-135261681/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368292393/10000000000 : ℝ)^2097 ≤ (43910215909013/100000000000000 : ℝ)^1585 := by
    have hnat : (5368292393 : ℕ)^2097*100000000000000^1585 ≤ 43910215909013^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368292393 10000000000 43910215909013 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054744369/2000000000 : ℝ)^2097 ≤ (5361214770187/12500000000000 : ℝ)^1585 := by
    have hnat : (1054744369 : ℕ)^2097*12500000000000^1585 ≤ 5361214770187^1585*2000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054744369 2000000000 5361214770187 12500000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135261681/625000000 : ℝ)^2097 ≤ (206251029889/1562500000000 : ℝ)^1585 := by
    have hnat : (135261681 : ℕ)^2097*1562500000000^1585 ≤ 206251029889^1585*625000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135261681 625000000 206251029889 1562500000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368292393/10000000000 : ℝ), (1054744369/2000000000 : ℝ), (-135261681/625000000 : ℝ)] ![(43910215909013/100000000000000 : ℝ), (5361214770187/12500000000000 : ℝ), (206251029889/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368292393/10000000000 : ℝ)|^2097 ≤ (43910215909013/100000000000000 : ℝ)^1585
        have hw : |(5368292393/10000000000 : ℝ)|=(5368292393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054744369/2000000000 : ℝ)|^2097 ≤ (5361214770187/12500000000000 : ℝ)^1585
        have hw : |(1054744369/2000000000 : ℝ)|=(1054744369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-135261681/625000000 : ℝ)|^2097 ≤ (206251029889/1562500000000 : ℝ)^1585
        have hw : |(-135261681/625000000 : ℝ)|=(135261681/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_box_15 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2115615621/5000000000 : ℝ)*x 0 + (1105551647/2500000000 : ℝ)*x 1 + (442220651/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2115615621/5000000000 : ℝ)^2097 ≤ (32048294246241/100000000000000 : ℝ)^1585 := by
    have hnat : (2115615621 : ℕ)^2097*100000000000000^1585 ≤ 32048294246241^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115615621 5000000000 32048294246241 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1105551647/2500000000 : ℝ)^2097 ≤ (33975853261739/100000000000000 : ℝ)^1585 := by
    have hnat : (1105551647 : ℕ)^2097*100000000000000^1585 ≤ 33975853261739^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105551647 2500000000 33975853261739 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442220651/1000000000 : ℝ)^2097 ≤ (16987926234441/50000000000000 : ℝ)^1585 := by
    have hnat : (442220651 : ℕ)^2097*50000000000000^1585 ≤ 16987926234441^1585*1000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442220651 1000000000 16987926234441 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2115615621/5000000000 : ℝ), (1105551647/2500000000 : ℝ), (442220651/1000000000 : ℝ)] ![(32048294246241/100000000000000 : ℝ), (33975853261739/100000000000000 : ℝ), (16987926234441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2115615621/5000000000 : ℝ)|^2097 ≤ (32048294246241/100000000000000 : ℝ)^1585
        have hw : |(2115615621/5000000000 : ℝ)|=(2115615621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1105551647/2500000000 : ℝ)|^2097 ≤ (33975853261739/100000000000000 : ℝ)^1585
        have hw : |(1105551647/2500000000 : ℝ)|=(1105551647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(442220651/1000000000 : ℝ)|^2097 ≤ (16987926234441/50000000000000 : ℝ)^1585
        have hw : |(442220651/1000000000 : ℝ)|=(442220651/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1195_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5711/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31119/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(2967/5000 : ℝ) ∧ (79969/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41621/50000 : ℝ) := by
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
  have lower0 : (5711/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7039/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5711/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7039/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5711/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7039/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5711/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7039/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5711/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7039/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5711/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5711/50000 : ℝ) ^ (8387/2048 : ℝ) ≤ (13843684398717761/100000000000000000000 : ℝ) := by
    have hpowers : (5711/50000 : ℝ)^8387 ≤ (13843684398717761/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5711 : ℕ)^8387*100000000000000000000^2048 ≤ 13843684398717761^2048*50000^8387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5711 50000 13843684398717761 100000000000000000000 8387 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5711/50000 : ℝ)) (X := (13843684398717761/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7039/50000 : ℝ) ^ (8387/2048 : ℝ) ≤ (651811922112073/2000000000000000000 : ℝ) := by
    have hpowers : (7039/50000 : ℝ)^8387 ≤ (651811922112073/2000000000000000000 : ℝ)^2048 := by
      have hnat : (7039 : ℕ)^8387*2000000000000000000^2048 ≤ 651811922112073^2048*50000^8387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7039 50000 651811922112073 2000000000000000000 8387 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7039/50000 : ℝ)) (X := (651811922112073/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013843684398717761/50000000000000000000 : ℝ) ≤ (2000135204004331/2000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (50013843684398717761/50000000000000000000 : ℝ)^2048 ≤ (2000135204004331/2000000000000000 : ℝ)^8387 := by
      have hnat : (50013843684398717761 : ℕ)^2048*2000000000000000^8387 ≤ 2000135204004331^8387*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013843684398717761 50000000000000000000 2000135204004331 2000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000135204004331/2000000000000000 : ℝ)) (X := (50013843684398717761/50000000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046434280504321411/100000000000000000000 : ℝ) ≤ (10001133667860949/10000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (100046434280504321411/100000000000000000000 : ℝ)^2048 ≤ (10001133667860949/10000000000000000 : ℝ)^8387 := by
      have hnat : (100046434280504321411 : ℕ)^2048*10000000000000000^8387 ≤ 10001133667860949^8387*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046434280504321411 100000000000000000000 10001133667860949 10000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001133667860949/10000000000000000 : ℝ)) (X := (100046434280504321411/100000000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000651811922112073/1000000000000000000 : ℝ) ≤ (10001591315700243/10000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (1000651811922112073/1000000000000000000 : ℝ)^2048 ≤ (10001591315700243/10000000000000000 : ℝ)^8387 := by
      have hnat : (1000651811922112073 : ℕ)^2048*10000000000000000^8387 ≤ 10001591315700243^8387*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000651811922112073 1000000000000000000 10001591315700243 10000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001591315700243/10000000000000000 : ℝ)) (X := (1000651811922112073/1000000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13843684398717761/100000000000000000000 : ℝ) ≤ ((3318917625242085443/3320000000000000000 : ℝ)+2*(228823919647/132800000000000 : ℝ)*(5711/50000 : ℝ))^(8387/2048 : ℝ) := by
    rw [show (3318917625242085443/3320000000000000000 : ℝ)+2*(228823919647/132800000000000 : ℝ)*(5711/50000 : ℝ)=(2000135204004331/2000000000000000 : ℝ) by norm_num, show 1+2*(13843684398717761/100000000000000000000 : ℝ)=(50013843684398717761/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(651811922112073/2000000000000000000 : ℝ)+(13843684398717761/100000000000000000000 : ℝ) ≤ ((3318917625242085443/3320000000000000000 : ℝ)+(228823919647/132800000000000 : ℝ)*((7039/50000 : ℝ)+(5711/50000 : ℝ)))^(8387/2048 : ℝ) := by
    rw [show (3318917625242085443/3320000000000000000 : ℝ)+(228823919647/132800000000000 : ℝ)*((7039/50000 : ℝ)+(5711/50000 : ℝ))=(10001133667860949/10000000000000000 : ℝ) by norm_num, show 1+(651811922112073/2000000000000000000 : ℝ)+(13843684398717761/100000000000000000000 : ℝ)=(100046434280504321411/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(651811922112073/2000000000000000000 : ℝ) ≤ ((3318917625242085443/3320000000000000000 : ℝ)+2*(228823919647/132800000000000 : ℝ)*(7039/50000 : ℝ))^(8387/2048 : ℝ) := by
    rw [show (3318917625242085443/3320000000000000000 : ℝ)+2*(228823919647/132800000000000 : ℝ)*(7039/50000 : ℝ)=(10001591315700243/10000000000000000 : ℝ) by norm_num, show 1+2*(651811922112073/2000000000000000000 : ℝ)=(1000651811922112073/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3318917625242085443/3320000000000000000 : ℝ)*(X 1 0+X 2 0)+(228823919647/132800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (5711/50000 : ℝ)) (hi := (7039/50000 : ℝ)) (c := (3318917625242085443/3320000000000000000 : ℝ)) (alpha := (228823919647/132800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3318917625242085443/3320000000000000000 : ℝ)*(X 0 1+X 2 1)+(228823919647/132800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (5711/50000 : ℝ)) (hi := (7039/50000 : ℝ)) (c := (3318917625242085443/3320000000000000000 : ℝ)) (alpha := (228823919647/132800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3318917625242085443/3320000000000000000 : ℝ)*(X 0 2+X 1 2)+(228823919647/132800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (5711/50000 : ℝ)) (hi := (7039/50000 : ℝ)) (c := (3318917625242085443/3320000000000000000 : ℝ)) (alpha := (228823919647/132800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2016633103/10000000000 : ℝ)*X 0 0+(5375539121/10000000000 : ℝ)*X 0 1+(5375539067/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296445921/10000000000 : ℝ)*X 1 0+(-2124024569/10000000000 : ℝ)*X 1 1+(5375539183/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296445601/10000000000 : ℝ)*X 2 0+(1343884853/2500000000 : ℝ)*X 2 1+(-212402469/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2232124287/5000000000 : ℝ)*X 0 0+(269115043/625000000 : ℝ)*X 0 1+(4305840883/10000000000 : ℝ)*X 0 2+(2232124287/5000000000 : ℝ)*X 1 0+(269115043/625000000 : ℝ)*X 1 1+(4305840883/10000000000 : ℝ)*X 1 2+(2232124287/5000000000 : ℝ)*X 2 0+(269115043/625000000 : ℝ)*X 2 1+(4305840883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2268346591/10000000000 : ℝ)*X 0 0+(2640891069/5000000000 : ℝ)*X 0 1+(5281783243/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5362606429/10000000000 : ℝ)*X 1 0+(-1080529473/5000000000 : ℝ)*X 1 1+(5281782909/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5362605857/10000000000 : ℝ)*X 2 0+(2640891561/5000000000 : ℝ)*X 2 1+(-2161059429/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((531236599/1250000000 : ℝ)*X 0 0+(4412998213/10000000000 : ℝ)*X 0 1+(2206499139/5000000000 : ℝ)*X 0 2+(531236599/1250000000 : ℝ)*X 1 0+(4412998213/10000000000 : ℝ)*X 1 1+(2206499139/5000000000 : ℝ)*X 1 2+(531236599/1250000000 : ℝ)*X 2 0+(4412998213/10000000000 : ℝ)*X 2 1+(2206499139/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-553912529/2500000000 : ℝ)*X 0 0+(5217919151/10000000000 : ℝ)*X 0 1+(269257519/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((528966031/1000000000 : ℝ)*X 1 0+(-2120160159/10000000000 : ℝ)*X 1 1+(673143793/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289660367/10000000000 : ℝ)*X 2 0+(5385150393/10000000000 : ℝ)*X 2 1+(-132510001/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((560743699/1250000000 : ℝ)*X 0 0+(2147424843/5000000000 : ℝ)*X 0 1+(2147424917/5000000000 : ℝ)*X 0 2+(560743699/1250000000 : ℝ)*X 1 0+(2147424843/5000000000 : ℝ)*X 1 1+(2147424917/5000000000 : ℝ)*X 1 2+(560743699/1250000000 : ℝ)*X 2 0+(2147424843/5000000000 : ℝ)*X 2 1+(2147424917/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2069616019/10000000000 : ℝ)*X 0 0+(5438162581/10000000000 : ℝ)*X 0 1+(527372201/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5368292361/10000000000 : ℝ)*X 1 0+(-1082093441/5000000000 : ℝ)*X 1 1+(164803809/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5368292393/10000000000 : ℝ)*X 2 0+(1054744369/2000000000 : ℝ)*X 2 1+(-135261681/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2115615621/5000000000 : ℝ)*X 0 0+(1105551647/2500000000 : ℝ)*X 0 1+(442220651/1000000000 : ℝ)*X 0 2+(2115615621/5000000000 : ℝ)*X 1 0+(1105551647/2500000000 : ℝ)*X 1 1+(442220651/1000000000 : ℝ)*X 1 2+(2115615621/5000000000 : ℝ)*X 2 0+(1105551647/2500000000 : ℝ)*X 2 1+(442220651/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31119/50000 : ℝ) ≤ (-622358129397414897363548860101/1000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78183411/50000000000000 : ℝ)*(lower0) + (7425773/25000000000000 : ℝ)*(upper1) + (99945831/25000000000000 : ℝ)*(lower4) + (3964789805354973/100000000000000 : ℝ)*(major0) + (3964789805354973/100000000000000 : ℝ)*(major1) + (3964789805354973/100000000000000 : ℝ)*(major2) + (1546283293/12500000000000 : ℝ)*(sp1) + (214686653/800000000000 : ℝ)*(sp2) + (7826874031/50000000000000 : ℝ)*(sp3) + (664503547516461/12500000000000 : ℝ)*(sp4) + (5316055550427453/100000000000000 : ℝ)*(sp5) + (1329010271215543/25000000000000 : ℝ)*(sp6) + (1317120653623997/50000000000000 : ℝ)*(sp7) + (39540562109/100000000000000 : ℝ)*(sp12) + (329282120124507/12500000000000 : ℝ)*(f.failure) + (5316067920693797/100000000000000 : ℝ)*(f.sum) + (22796286092051/6640000000000000000000000000 : ℝ)*base65 + (2546116568357766961/332000000000000000000000000000000 : ℝ)*base68 + (2315503625089766961/332000000000000000000000000000000 : ℝ)*base70 + (402744832770233039/332000000000000000000000000000000 : ℝ)*base71 + (126152246676029/6640000000000000000000000000 : ℝ)*base74 + (2116613864149766961/332000000000000000000000000000000 : ℝ)*base76 + (1089460663405766961/332000000000000000000000000000000 : ℝ)*base78 + (4907610394409766961/332000000000000000000000000000000 : ℝ)*base80 + (22983916891069/6640000000000000000000000000 : ℝ)*base82 + (164871/78125000000000000000 : ℝ)*base89 + (164871/78125000000000000000 : ℝ)*base91 + (164871/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (2967/5000 : ℝ) ≤ (49254229186897714574783084586429/83000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7557221/25000000000000 : ℝ)*(lower0) + (1510003/25000000000000 : ℝ)*(lower1) + (75513419/50000000000000 : ℝ)*(lower4) + (2014900896453099/50000000000000 : ℝ)*(major0) + (2014900896453099/50000000000000 : ℝ)*(major1) + (2014900896453099/50000000000000 : ℝ)*(major2) + (2681184276144459/50000000000000 : ℝ)*(sp0) + (5362362350147939/100000000000000 : ℝ)*(sp1) + (5362359241143497/100000000000000 : ℝ)*(sp2) + (2677447589351663/100000000000000 : ℝ)*(sp3) + (2166316227/25000000000000 : ℝ)*(sp5) + (11774269349/100000000000000 : ℝ)*(sp6) + (416611337/10000000000000 : ℝ)*(sp7) + (307890491/12500000000000 : ℝ)*(sp12) + (334681469433129/12500000000000 : ℝ)*(f.failure) + (2681185507706423/50000000000000 : ℝ)*(f.sum) + (2950357885067/3320000000000000000000000000 : ℝ)*base66 + (61829204801462857/166000000000000000000000000000000 : ℝ)*base67 + (377750631551462857/166000000000000000000000000000000 : ℝ)*base69 + (1661738296196537143/166000000000000000000000000000000 : ℝ)*base72 + (240681071708653/3320000000000000000000000000 : ℝ)*base73 + (121838985333462857/166000000000000000000000000000000 : ℝ)*base75 + (972237947070537143/166000000000000000000000000000000 : ℝ)*base78 + (4862211876865462857/166000000000000000000000000000000 : ℝ)*base79 + (8756640222107/3320000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1010913/78125000000000000000 : ℝ)*base90 + (1010913/78125000000000000000 : ℝ)*base92 + (1010913/78125000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (79969/100000 : ℝ) ≤ (66376334562583509233980519755771/83000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13173671/100000000000000 : ℝ)*(upper0) + (11214163/50000000000000 : ℝ)*(lower1) + (39369193/50000000000000 : ℝ)*(lower3) + (7638281/12500000000000 : ℝ)*(upper4) + (2248600651051633/50000000000000 : ℝ)*(major0) + (2248600651051633/50000000000000 : ℝ)*(major1) + (2248600651051633/50000000000000 : ℝ)*(major2) + (36190184831/100000000000000 : ℝ)*(sp1) + (19004111923/25000000000000 : ℝ)*(sp2) + (14031959477/50000000000000 : ℝ)*(sp3) + (5979747485556103/100000000000000 : ℝ)*(sp8) + (5979711295371271/100000000000000 : ℝ)*(sp9) + (5979671469108411/100000000000000 : ℝ)*(sp10) + (2987969892256531/100000000000000 : ℝ)*(sp11) + (746999489043871/25000000000000 : ℝ)*(f.failure) + (5979747485556103/100000000000000 : ℝ)*(f.sum) + (2827755453551/3320000000000000000000000000 : ℝ)*base65 + (2189287325056546581/166000000000000000000000000000000 : ℝ)*base68 + (2678606057086546581/166000000000000000000000000000000 : ℝ)*base70 + (2952058509964546581/166000000000000000000000000000000 : ℝ)*base72 + (6380250237249/3320000000000000000000000000 : ℝ)*base74 + (1367925029148546581/166000000000000000000000000000000 : ℝ)*base76 + (3138654357052546581/166000000000000000000000000000000 : ℝ)*base78 + (2141157961340546581/166000000000000000000000000000000 : ℝ)*base80 + (167926895951/3320000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (270587/156250000000000000000 : ℝ)*base90 + (270587/156250000000000000000 : ℝ)*base92 + (270587/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-41621/50000 : ℝ) ≤ (-5527125437646406665542403513/6640000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6377033/25000000000000 : ℝ)*(upper1) + (16099/40000000000 : ℝ)*(upper3) + (2222351/5000000000000 : ℝ)*(upper5) + (4532457539031711/100000000000000 : ℝ)*(major0) + (4532457539031711/100000000000000 : ℝ)*(major1) + (4532457539031711/100000000000000 : ℝ)*(major2) + (131507977/800000000000 : ℝ)*(sp4) + (126760546421/100000000000000 : ℝ)*(sp5) + (40242051539/25000000000000 : ℝ)*(sp6) + (127954186867/100000000000000 : ℝ)*(sp7) + (6081222603138897/100000000000000 : ℝ)*(sp12) + (3040556140544801/50000000000000 : ℝ)*(sp13) + (6081078073429867/100000000000000 : ℝ)*(sp14) + (75282367397083/2500000000000 : ℝ)*(sp15) + (752855662517547/25000000000000 : ℝ)*(f.failure) + (3040619520818011/50000000000000 : ℝ)*(f.sum) + (19280949130977/6640000000000000000000000000 : ℝ)*base65 + (627970696682907973/332000000000000000000000000000000 : ℝ)*base67 + (19083326026126907973/332000000000000000000000000000000 : ℝ)*base69 + (1225708075921092027/332000000000000000000000000000000 : ℝ)*base72 + (27433252855377/6640000000000000000000000000 : ℝ)*base73 + (8004211156686907973/332000000000000000000000000000000 : ℝ)*base75 + (363665591265092027/332000000000000000000000000000000 : ℝ)*base78 + (650321346997092027/332000000000000000000000000000000 : ℝ)*base80 + (157361367405217/6640000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (234741/156250000000000000000 : ℝ)*base89 + (234741/156250000000000000000 : ℝ)*base91 + (234741/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1195_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5711/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31119/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(2967/5000 : ℝ) else (79969/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41621/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1195_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1195_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11421/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31119/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(2967/5000 : ℝ) else (79969/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41621/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1195_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1195_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11421/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31119/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(2967/5000 : ℝ) else (79969/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41621/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1195_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
