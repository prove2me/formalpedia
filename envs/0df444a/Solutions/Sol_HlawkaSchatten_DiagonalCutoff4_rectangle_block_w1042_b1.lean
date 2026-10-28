-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1042_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:48:03.489642+00:00
-- url     : https://prove2.me/submissions/621105b0-52f9-4a15-8718-3ca78eff9b3b

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
theorem support_rectangle_w1042_s3_0 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2210565967/10000000000 : ℝ)*x 0 + (2720189199/5000000000 : ℝ)*x 1 + (326357193/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2210565967/10000000000 : ℝ)^8235 ≤ (13412916428489/100000000000000 : ℝ)^6187 := by
    have hnat : (2210565967 : ℕ)^8235*100000000000000^6187 ≤ 13412916428489^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210565967 10000000000 13412916428489 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720189199/5000000000 : ℝ)^8235 ≤ (5559400398797/12500000000000 : ℝ)^6187 := by
    have hnat : (2720189199 : ℕ)^8235*12500000000000^6187 ≤ 5559400398797^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720189199 5000000000 5559400398797 12500000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326357193/625000000 : ℝ)^8235 ≤ (10527970091277/25000000000000 : ℝ)^6187 := by
    have hnat : (326357193 : ℕ)^8235*25000000000000^6187 ≤ 10527970091277^6187*625000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326357193 625000000 10527970091277 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2210565967/10000000000 : ℝ), (2720189199/5000000000 : ℝ), (326357193/625000000 : ℝ)] ![(13412916428489/100000000000000 : ℝ), (5559400398797/12500000000000 : ℝ), (10527970091277/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2210565967/10000000000 : ℝ)|^8235 ≤ (13412916428489/100000000000000 : ℝ)^6187
        have hw : |(-2210565967/10000000000 : ℝ)|=(2210565967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720189199/5000000000 : ℝ)|^8235 ≤ (5559400398797/12500000000000 : ℝ)^6187
        have hw : |(2720189199/5000000000 : ℝ)|=(2720189199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326357193/625000000 : ℝ)|^8235 ≤ (10527970091277/25000000000000 : ℝ)^6187
        have hw : |(326357193/625000000 : ℝ)|=(326357193/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s3_1 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1339078423/2500000000 : ℝ)*x 0 + (-2322607661/10000000000 : ℝ)*x 1 + (5221714927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339078423/2500000000 : ℝ)^8235 ≤ (10890708791963/25000000000000 : ℝ)^6187 := by
    have hnat : (1339078423 : ℕ)^8235*25000000000000^6187 ≤ 10890708791963^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339078423 2500000000 10890708791963 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2322607661/10000000000 : ℝ)^8235 ≤ (14325286182947/100000000000000 : ℝ)^6187 := by
    have hnat : (2322607661 : ℕ)^8235*100000000000000^6187 ≤ 14325286182947^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2322607661 10000000000 14325286182947 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5221714927/10000000000 : ℝ)^8235 ≤ (42111878636881/100000000000000 : ℝ)^6187 := by
    have hnat : (5221714927 : ℕ)^8235*100000000000000^6187 ≤ 42111878636881^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221714927 10000000000 42111878636881 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1339078423/2500000000 : ℝ), (-2322607661/10000000000 : ℝ), (5221714927/10000000000 : ℝ)] ![(10890708791963/25000000000000 : ℝ), (14325286182947/100000000000000 : ℝ), (42111878636881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1339078423/2500000000 : ℝ)|^8235 ≤ (10890708791963/25000000000000 : ℝ)^6187
        have hw : |(1339078423/2500000000 : ℝ)|=(1339078423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2322607661/10000000000 : ℝ)|^8235 ≤ (14325286182947/100000000000000 : ℝ)^6187
        have hw : |(-2322607661/10000000000 : ℝ)|=(2322607661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5221714927/10000000000 : ℝ)|^8235 ≤ (42111878636881/100000000000000 : ℝ)^6187
        have hw : |(5221714927/10000000000 : ℝ)|=(5221714927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s3_2 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5356313589/10000000000 : ℝ)*x 0 + (261085739/500000000 : ℝ)*x 1 + (-580651997/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356313589/10000000000 : ℝ)^8235 ≤ (21781417026431/50000000000000 : ℝ)^6187 := by
    have hnat : (5356313589 : ℕ)^8235*50000000000000^6187 ≤ 21781417026431^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356313589 10000000000 21781417026431 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261085739/500000000 : ℝ)^8235 ≤ (8422375411787/20000000000000 : ℝ)^6187 := by
    have hnat : (261085739 : ℕ)^8235*20000000000000^6187 ≤ 8422375411787^6187*500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261085739 500000000 8422375411787 20000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (580651997/2500000000 : ℝ)^8235 ≤ (7162644433709/50000000000000 : ℝ)^6187 := by
    have hnat : (580651997 : ℕ)^8235*50000000000000^6187 ≤ 7162644433709^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      580651997 2500000000 7162644433709 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356313589/10000000000 : ℝ), (261085739/500000000 : ℝ), (-580651997/2500000000 : ℝ)] ![(21781417026431/50000000000000 : ℝ), (8422375411787/20000000000000 : ℝ), (7162644433709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356313589/10000000000 : ℝ)|^8235 ≤ (21781417026431/50000000000000 : ℝ)^6187
        have hw : |(5356313589/10000000000 : ℝ)|=(5356313589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261085739/500000000 : ℝ)|^8235 ≤ (8422375411787/20000000000000 : ℝ)^6187
        have hw : |(261085739/500000000 : ℝ)|=(261085739/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-580651997/2500000000 : ℝ)|^8235 ≤ (7162644433709/50000000000000 : ℝ)^6187
        have hw : |(-580651997/2500000000 : ℝ)|=(580651997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s3_3 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (546994577/1250000000 : ℝ)*x 0 + (2083993751/5000000000 : ℝ)*x 1 + (4594497537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546994577/1250000000 : ℝ)^8235 ≤ (33286045144939/100000000000000 : ℝ)^6187 := by
    have hnat : (546994577 : ℕ)^8235*100000000000000^6187 ≤ 33286045144939^6187*1250000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546994577 1250000000 33286045144939 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2083993751/5000000000 : ℝ)^8235 ≤ (31197207511923/100000000000000 : ℝ)^6187 := by
    have hnat : (2083993751 : ℕ)^8235*100000000000000^6187 ≤ 31197207511923^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083993751 5000000000 31197207511923 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4594497537/10000000000 : ℝ)^8235 ≤ (35516747330477/100000000000000 : ℝ)^6187 := by
    have hnat : (4594497537 : ℕ)^8235*100000000000000^6187 ≤ 35516747330477^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4594497537 10000000000 35516747330477 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546994577/1250000000 : ℝ), (2083993751/5000000000 : ℝ), (4594497537/10000000000 : ℝ)] ![(33286045144939/100000000000000 : ℝ), (31197207511923/100000000000000 : ℝ), (35516747330477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546994577/1250000000 : ℝ)|^8235 ≤ (33286045144939/100000000000000 : ℝ)^6187
        have hw : |(546994577/1250000000 : ℝ)|=(546994577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2083993751/5000000000 : ℝ)|^8235 ≤ (31197207511923/100000000000000 : ℝ)^6187
        have hw : |(2083993751/5000000000 : ℝ)|=(2083993751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4594497537/10000000000 : ℝ)|^8235 ≤ (35516747330477/100000000000000 : ℝ)^6187
        have hw : |(4594497537/10000000000 : ℝ)|=(4594497537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s3_4 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2210589781/10000000000 : ℝ)*x 0 + (652828337/1250000000 : ℝ)*x 1 + (5439461359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2210589781/10000000000 : ℝ)^8235 ≤ (6706554376879/50000000000000 : ℝ)^6187 := by
    have hnat : (2210589781 : ℕ)^8235*50000000000000^6187 ≤ 6706554376879^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210589781 10000000000 6706554376879 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652828337/1250000000 : ℝ)^8235 ≤ (42121666149107/100000000000000 : ℝ)^6187 := by
    have hnat : (652828337 : ℕ)^8235*100000000000000^6187 ≤ 42121666149107^6187*1250000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652828337 1250000000 42121666149107 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439461359/10000000000 : ℝ)^8235 ≤ (44465225086749/100000000000000 : ℝ)^6187 := by
    have hnat : (5439461359 : ℕ)^8235*100000000000000^6187 ≤ 44465225086749^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439461359 10000000000 44465225086749 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2210589781/10000000000 : ℝ), (652828337/1250000000 : ℝ), (5439461359/10000000000 : ℝ)] ![(6706554376879/50000000000000 : ℝ), (42121666149107/100000000000000 : ℝ), (44465225086749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2210589781/10000000000 : ℝ)|^8235 ≤ (6706554376879/50000000000000 : ℝ)^6187
        have hw : |(-2210589781/10000000000 : ℝ)|=(2210589781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652828337/1250000000 : ℝ)|^8235 ≤ (42121666149107/100000000000000 : ℝ)^6187
        have hw : |(652828337/1250000000 : ℝ)|=(652828337/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439461359/10000000000 : ℝ)|^8235 ≤ (44465225086749/100000000000000 : ℝ)^6187
        have hw : |(5439461359/10000000000 : ℝ)|=(5439461359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s3_5 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5301336803/10000000000 : ℝ)*x 0 + (-2104861841/10000000000 : ℝ)*x 1 + (5439460717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301336803/10000000000 : ℝ)^8235 ≤ (42968715827891/100000000000000 : ℝ)^6187 := by
    have hnat : (5301336803 : ℕ)^8235*100000000000000^6187 ≤ 42968715827891^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301336803 10000000000 42968715827891 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2104861841/10000000000 : ℝ)^8235 ≤ (12566066044033/100000000000000 : ℝ)^6187 := by
    have hnat : (2104861841 : ℕ)^8235*100000000000000^6187 ≤ 12566066044033^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104861841 10000000000 12566066044033 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439460717/10000000000 : ℝ)^8235 ≤ (1111630452537/2500000000000 : ℝ)^6187 := by
    have hnat : (5439460717 : ℕ)^8235*2500000000000^6187 ≤ 1111630452537^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439460717 10000000000 1111630452537 2500000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301336803/10000000000 : ℝ), (-2104861841/10000000000 : ℝ), (5439460717/10000000000 : ℝ)] ![(42968715827891/100000000000000 : ℝ), (12566066044033/100000000000000 : ℝ), (1111630452537/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301336803/10000000000 : ℝ)|^8235 ≤ (42968715827891/100000000000000 : ℝ)^6187
        have hw : |(5301336803/10000000000 : ℝ)|=(5301336803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2104861841/10000000000 : ℝ)|^8235 ≤ (12566066044033/100000000000000 : ℝ)^6187
        have hw : |(-2104861841/10000000000 : ℝ)|=(2104861841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439460717/10000000000 : ℝ)|^8235 ≤ (1111630452537/2500000000000 : ℝ)^6187
        have hw : |(5439460717/10000000000 : ℝ)|=(5439460717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s3_6 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1325334107/2500000000 : ℝ)*x 0 + (1359865307/2500000000 : ℝ)*x 1 + (-526215413/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325334107/2500000000 : ℝ)^8235 ≤ (21484355891151/50000000000000 : ℝ)^6187 := by
    have hnat : (1325334107 : ℕ)^8235*50000000000000^6187 ≤ 21484355891151^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325334107 2500000000 21484355891151 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359865307/2500000000 : ℝ)^8235 ≤ (22232611830703/50000000000000 : ℝ)^6187 := by
    have hnat : (1359865307 : ℕ)^8235*50000000000000^6187 ≤ 22232611830703^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359865307 2500000000 22232611830703 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526215413/2500000000 : ℝ)^8235 ≤ (6283032271101/50000000000000 : ℝ)^6187 := by
    have hnat : (526215413 : ℕ)^8235*50000000000000^6187 ≤ 6283032271101^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526215413 2500000000 6283032271101 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325334107/2500000000 : ℝ), (1359865307/2500000000 : ℝ), (-526215413/2500000000 : ℝ)] ![(21484355891151/50000000000000 : ℝ), (22232611830703/50000000000000 : ℝ), (6283032271101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325334107/2500000000 : ℝ)|^8235 ≤ (21484355891151/50000000000000 : ℝ)^6187
        have hw : |(1325334107/2500000000 : ℝ)|=(1325334107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359865307/2500000000 : ℝ)|^8235 ≤ (22232611830703/50000000000000 : ℝ)^6187
        have hw : |(1359865307/2500000000 : ℝ)|=(1359865307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-526215413/2500000000 : ℝ)|^8235 ≤ (6283032271101/50000000000000 : ℝ)^6187
        have hw : |(-526215413/2500000000 : ℝ)|=(526215413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s3_7 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (875200643/2000000000 : ℝ)*x 0 + (4592717937/10000000000 : ℝ)*x 1 + (4169777827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875200643/2000000000 : ℝ)^8235 ≤ (33286516936361/100000000000000 : ℝ)^6187 := by
    have hnat : (875200643 : ℕ)^8235*100000000000000^6187 ≤ 33286516936361^6187*2000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875200643 2000000000 33286516936361 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4592717937/10000000000 : ℝ)^8235 ≤ (35498437968843/100000000000000 : ℝ)^6187 := by
    have hnat : (4592717937 : ℕ)^8235*100000000000000^6187 ≤ 35498437968843^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4592717937 10000000000 35498437968843 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4169777827/10000000000 : ℝ)^8235 ≤ (7803761269023/25000000000000 : ℝ)^6187 := by
    have hnat : (4169777827 : ℕ)^8235*25000000000000^6187 ≤ 7803761269023^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169777827 10000000000 7803761269023 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875200643/2000000000 : ℝ), (4592717937/10000000000 : ℝ), (4169777827/10000000000 : ℝ)] ![(33286516936361/100000000000000 : ℝ), (35498437968843/100000000000000 : ℝ), (7803761269023/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875200643/2000000000 : ℝ)|^8235 ≤ (33286516936361/100000000000000 : ℝ)^6187
        have hw : |(875200643/2000000000 : ℝ)|=(875200643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4592717937/10000000000 : ℝ)|^8235 ≤ (35498437968843/100000000000000 : ℝ)^6187
        have hw : |(4592717937/10000000000 : ℝ)|=(4592717937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4169777827/10000000000 : ℝ)|^8235 ≤ (7803761269023/25000000000000 : ℝ)^6187
        have hw : |(4169777827/10000000000 : ℝ)|=(4169777827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1042_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (841/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8593/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2063/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14941/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (841/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8593/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (841/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8593/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (841/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8593/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (841/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8593/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (841/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8593/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (841/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8593/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8593/100000 : ℝ) ^ (4117/1024 : ℝ) ≤ (1296166812665761/25000000000000000000 : ℝ) := by
    have hpowers : (8593/100000 : ℝ)^4117 ≤ (1296166812665761/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8593 : ℕ)^4117*25000000000000000000^1024 ≤ 1296166812665761^1024*100000^4117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8593 100000 1296166812665761 25000000000000000000 4117 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8593/100000 : ℝ)) (X := (1296166812665761/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (841/5000 : ℝ) ^ (4117/1024 : ℝ) ≤ (77166241971041341/100000000000000000000 : ℝ) := by
    have hpowers : (841/5000 : ℝ)^4117 ≤ (77166241971041341/100000000000000000000 : ℝ)^1024 := by
      have hnat : (841 : ℕ)^4117*100000000000000000000^1024 ≤ 77166241971041341^1024*5000^4117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        841 5000 77166241971041341 100000000000000000000 4117 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (841/5000 : ℝ)) (X := (77166241971041341/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501296166812665761/12500000000000000000 : ℝ) ≤ (5000128950509639/5000000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (12501296166812665761/12500000000000000000 : ℝ)^1024 ≤ (5000128950509639/5000000000000000 : ℝ)^4117 := by
      have hnat : (12501296166812665761 : ℕ)^1024*5000000000000000^4117 ≤ 5000128950509639^4117*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501296166812665761 12500000000000000000 5000128950509639 5000000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000128950509639/5000000000000000 : ℝ)) (X := (12501296166812665761/12500000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20016470181844340877/20000000000000000000 : ℝ) ≤ (5001023819014781/5000000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (20016470181844340877/20000000000000000000 : ℝ)^1024 ≤ (5001023819014781/5000000000000000 : ℝ)^4117 := by
      have hnat : (20016470181844340877 : ℕ)^1024*5000000000000000^4117 ≤ 5001023819014781^4117*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20016470181844340877 20000000000000000000 5001023819014781 5000000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001023819014781/5000000000000000 : ℝ)) (X := (20016470181844340877/20000000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50077166241971041341/50000000000000000000 : ℝ) ≤ (5001918687519923/5000000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (50077166241971041341/50000000000000000000 : ℝ)^1024 ≤ (5001918687519923/5000000000000000 : ℝ)^4117 := by
      have hnat : (50077166241971041341 : ℕ)^1024*5000000000000000^4117 ≤ 5001918687519923^4117*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50077166241971041341 50000000000000000000 5001918687519923 5000000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001918687519923/5000000000000000 : ℝ)) (X := (50077166241971041341/50000000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1296166812665761/25000000000000000000 : ℝ) ≤ ((41120681665713429641/41135000000000000000 : ℝ)+2*(447434252571/205675000000000 : ℝ)*(8593/100000 : ℝ))^(4117/1024 : ℝ) := by
    rw [show (41120681665713429641/41135000000000000000 : ℝ)+2*(447434252571/205675000000000 : ℝ)*(8593/100000 : ℝ)=(5000128950509639/5000000000000000 : ℝ) by norm_num, show 1+2*(1296166812665761/25000000000000000000 : ℝ)=(12501296166812665761/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(77166241971041341/100000000000000000000 : ℝ)+(1296166812665761/25000000000000000000 : ℝ) ≤ ((41120681665713429641/41135000000000000000 : ℝ)+(447434252571/205675000000000 : ℝ)*((841/5000 : ℝ)+(8593/100000 : ℝ)))^(4117/1024 : ℝ) := by
    rw [show (41120681665713429641/41135000000000000000 : ℝ)+(447434252571/205675000000000 : ℝ)*((841/5000 : ℝ)+(8593/100000 : ℝ))=(5001023819014781/5000000000000000 : ℝ) by norm_num, show 1+(77166241971041341/100000000000000000000 : ℝ)+(1296166812665761/25000000000000000000 : ℝ)=(20016470181844340877/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(77166241971041341/100000000000000000000 : ℝ) ≤ ((41120681665713429641/41135000000000000000 : ℝ)+2*(447434252571/205675000000000 : ℝ)*(841/5000 : ℝ))^(4117/1024 : ℝ) := by
    rw [show (41120681665713429641/41135000000000000000 : ℝ)+2*(447434252571/205675000000000 : ℝ)*(841/5000 : ℝ)=(5001918687519923/5000000000000000 : ℝ) by norm_num, show 1+2*(77166241971041341/100000000000000000000 : ℝ)=(50077166241971041341/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (41120681665713429641/41135000000000000000 : ℝ)*(X 1 0+X 2 0)+(447434252571/205675000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (8593/100000 : ℝ)) (hi := (841/5000 : ℝ)) (c := (41120681665713429641/41135000000000000000 : ℝ)) (alpha := (447434252571/205675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (41120681665713429641/41135000000000000000 : ℝ)*(X 0 1+X 2 1)+(447434252571/205675000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (8593/100000 : ℝ)) (hi := (841/5000 : ℝ)) (c := (41120681665713429641/41135000000000000000 : ℝ)) (alpha := (447434252571/205675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (41120681665713429641/41135000000000000000 : ℝ)*(X 0 2+X 1 2)+(447434252571/205675000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (8593/100000 : ℝ)) (hi := (841/5000 : ℝ)) (c := (41120681665713429641/41135000000000000000 : ℝ)) (alpha := (447434252571/205675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2210565967/10000000000 : ℝ)*X 0 0+(2720189199/5000000000 : ℝ)*X 0 1+(326357193/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1339078423/2500000000 : ℝ)*X 1 0+(-2322607661/10000000000 : ℝ)*X 1 1+(5221714927/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5356313589/10000000000 : ℝ)*X 2 0+(261085739/500000000 : ℝ)*X 2 1+(-580651997/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((546994577/1250000000 : ℝ)*X 0 0+(2083993751/5000000000 : ℝ)*X 0 1+(4594497537/10000000000 : ℝ)*X 0 2+(546994577/1250000000 : ℝ)*X 1 0+(2083993751/5000000000 : ℝ)*X 1 1+(4594497537/10000000000 : ℝ)*X 1 2+(546994577/1250000000 : ℝ)*X 2 0+(2083993751/5000000000 : ℝ)*X 2 1+(4594497537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2210589781/10000000000 : ℝ)*X 0 0+(652828337/1250000000 : ℝ)*X 0 1+(5439461359/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301336803/10000000000 : ℝ)*X 1 0+(-2104861841/10000000000 : ℝ)*X 1 1+(5439460717/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325334107/2500000000 : ℝ)*X 2 0+(1359865307/2500000000 : ℝ)*X 2 1+(-526215413/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((875200643/2000000000 : ℝ)*X 0 0+(4592717937/10000000000 : ℝ)*X 0 1+(4169777827/10000000000 : ℝ)*X 0 2+(875200643/2000000000 : ℝ)*X 1 0+(4592717937/10000000000 : ℝ)*X 1 1+(4169777827/10000000000 : ℝ)*X 1 2+(875200643/2000000000 : ℝ)*X 2 0+(4592717937/10000000000 : ℝ)*X 2 1+(4169777827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3619620547614879301574928267/514187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (737886493/50000000000000 : ℝ)*(base19) + (1365360557/100000000000000 : ℝ)*(base23) + (18323/50000000000000 : ℝ)*(upper2) + (352430343/100000000000000 : ℝ)*(upper3) + (12072267/100000000000000 : ℝ)*(upper4) + (1729478356355971/50000000000000 : ℝ)*(major0) + (1729478356355971/50000000000000 : ℝ)*(major1) + (1729478356355971/50000000000000 : ℝ)*(major2) + (914652854955759/20000000000000 : ℝ)*(sp0) + (457327561696579/10000000000000 : ℝ)*(sp1) + (4573275727378219/100000000000000 : ℝ)*(sp2) + (1172310634437229/50000000000000 : ℝ)*(sp3) + (12817959981/100000000000000 : ℝ)*(sp4) + (14829160797/100000000000000 : ℝ)*(sp7) + (293079512254407/12500000000000 : ℝ)*(f.failure) + (571659636592347/12500000000000 : ℝ)*(f.sum) + (29282919320667/41135000000000000000000000000 : ℝ)*base66 + (3567750135317313589/2056750000000000000000000000000000 : ℝ)*base68 + (6303768931919936411/2056750000000000000000000000000000 : ℝ)*base69 + (9623811887746686411/2056750000000000000000000000000000 : ℝ)*base71 + (163040895457003/41135000000000000000000000000 : ℝ)*base73 + (5235258119580686411/2056750000000000000000000000000000 : ℝ)*base75 + (19291110081347436411/2056750000000000000000000000000000 : ℝ)*base77 + (18592386752953186411/2056750000000000000000000000000000 : ℝ)*base79 + (21392902835027/41135000000000000000000000000 : ℝ)*base82 + (2123923/625000000000000000000 : ℝ)*base89 + (2123923/625000000000000000000 : ℝ)*base91 + (2123923/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (926410165441936092046154769/205675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4466761/500000000000 : ℝ)*(base19) + (278764197/50000000000000 : ℝ)*(base23) + (488131/12500000000000 : ℝ)*(lower4) + (102122787/50000000000000 : ℝ)*(upper5) + (697621956643997/20000000000000 : ℝ)*(major0) + (697621956643997/20000000000000 : ℝ)*(major1) + (697621956643997/20000000000000 : ℝ)*(major2) + (290006341/6250000000000 : ℝ)*(sp0) + (4876656473/50000000000000 : ℝ)*(sp1) + (2029362183/25000000000000 : ℝ)*(sp2) + (2305908709290067/50000000000000 : ℝ)*(sp4) + (1152952853004111/25000000000000 : ℝ)*(sp5) + (288238336481529/6250000000000 : ℝ)*(sp6) + (147774834851059/6250000000000 : ℝ)*(sp7) + (147774834851059/6250000000000 : ℝ)*(f.failure) + (461182205868159/10000000000000 : ℝ)*(f.sum) + (3243430542079/822700000000000000000000000 : ℝ)*base65 + (1676961543945915077/822700000000000000000000000000000 : ℝ)*base67 + (655213312927484923/822700000000000000000000000000000 : ℝ)*base70 + (5425848436587115077/822700000000000000000000000000000 : ℝ)*base71 + (8718947900769/4113500000000000000000000000 : ℝ)*base74 + (2189218415501315077/822700000000000000000000000000000 : ℝ)*base75 + (3967375275111915077/822700000000000000000000000000000 : ℝ)*base77 + (2729379128745915077/822700000000000000000000000000000 : ℝ)*base79 + (930442176043/411350000000000000000000000 : ℝ)*base81 + (1257849/312500000000000000000 : ℝ)*base90 + (1257849/312500000000000000000 : ℝ)*base92 + (1257849/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1042_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (841/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8593/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2063/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14941/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1042_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1042_s4_0 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-34601311/156250000 : ℝ)*x 0 + (5407171101/10000000000 : ℝ)*x 1 + (262618201/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34601311/156250000 : ℝ)^8235 ≤ (1344456746979/10000000000000 : ℝ)^6187 := by
    have hnat : (34601311 : ℕ)^8235*10000000000000^6187 ≤ 1344456746979^6187*156250000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34601311 156250000 1344456746979 10000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407171101/10000000000 : ℝ)^8235 ≤ (44114237200371/100000000000000 : ℝ)^6187 := by
    have hnat : (5407171101 : ℕ)^8235*100000000000000^6187 ≤ 44114237200371^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407171101 10000000000 44114237200371 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262618201/500000000 : ℝ)^8235 ≤ (21220597653749/50000000000000 : ℝ)^6187 := by
    have hnat : (262618201 : ℕ)^8235*50000000000000^6187 ≤ 21220597653749^6187*500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262618201 500000000 21220597653749 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-34601311/156250000 : ℝ), (5407171101/10000000000 : ℝ), (262618201/500000000 : ℝ)] ![(1344456746979/10000000000000 : ℝ), (44114237200371/100000000000000 : ℝ), (21220597653749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-34601311/156250000 : ℝ)|^8235 ≤ (1344456746979/10000000000000 : ℝ)^6187
        have hw : |(-34601311/156250000 : ℝ)|=(34601311/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407171101/10000000000 : ℝ)|^8235 ≤ (44114237200371/100000000000000 : ℝ)^6187
        have hw : |(5407171101/10000000000 : ℝ)|=(5407171101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262618201/500000000 : ℝ)|^8235 ≤ (21220597653749/50000000000000 : ℝ)^6187
        have hw : |(262618201/500000000 : ℝ)|=(262618201/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s4_1 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668513721/1250000000 : ℝ)*x 0 + (-1146623293/5000000000 : ℝ)*x 1 + (1313091011/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668513721/1250000000 : ℝ)^8235 ≤ (43474049042289/100000000000000 : ℝ)^6187 := by
    have hnat : (668513721 : ℕ)^8235*100000000000000^6187 ≤ 43474049042289^6187*1250000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668513721 1250000000 43474049042289 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1146623293/5000000000 : ℝ)^8235 ≤ (1408475537917/10000000000000 : ℝ)^6187 := by
    have hnat : (1146623293 : ℕ)^8235*10000000000000^6187 ≤ 1408475537917^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146623293 5000000000 1408475537917 10000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313091011/2500000000 : ℝ)^8235 ≤ (42441195565621/100000000000000 : ℝ)^6187 := by
    have hnat : (1313091011 : ℕ)^8235*100000000000000^6187 ≤ 42441195565621^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313091011 2500000000 42441195565621 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668513721/1250000000 : ℝ), (-1146623293/5000000000 : ℝ), (1313091011/2500000000 : ℝ)] ![(43474049042289/100000000000000 : ℝ), (1408475537917/10000000000000 : ℝ), (42441195565621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668513721/1250000000 : ℝ)|^8235 ≤ (43474049042289/100000000000000 : ℝ)^6187
        have hw : |(668513721/1250000000 : ℝ)|=(668513721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1146623293/5000000000 : ℝ)|^8235 ≤ (1408475537917/10000000000000 : ℝ)^6187
        have hw : |(-1146623293/5000000000 : ℝ)|=(1146623293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313091011/2500000000 : ℝ)|^8235 ≤ (42441195565621/100000000000000 : ℝ)^6187
        have hw : |(1313091011/2500000000 : ℝ)|=(1313091011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s4_2 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668513727/1250000000 : ℝ)*x 0 + (525236397/1000000000 : ℝ)*x 1 + (-114662331/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668513727/1250000000 : ℝ)^8235 ≤ (1358564048801/3125000000000 : ℝ)^6187 := by
    have hnat : (668513727 : ℕ)^8235*3125000000000^6187 ≤ 1358564048801^6187*1250000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668513727 1250000000 1358564048801 3125000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525236397/1000000000 : ℝ)^8235 ≤ (2122059738487/5000000000000 : ℝ)^6187 := by
    have hnat : (525236397 : ℕ)^8235*5000000000000^6187 ≤ 2122059738487^6187*1000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525236397 1000000000 2122059738487 5000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114662331/500000000 : ℝ)^8235 ≤ (3521188914279/25000000000000 : ℝ)^6187 := by
    have hnat : (114662331 : ℕ)^8235*25000000000000^6187 ≤ 3521188914279^6187*500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114662331 500000000 3521188914279 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668513727/1250000000 : ℝ), (525236397/1000000000 : ℝ), (-114662331/500000000 : ℝ)] ![(1358564048801/3125000000000 : ℝ), (2122059738487/5000000000000 : ℝ), (3521188914279/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668513727/1250000000 : ℝ)|^8235 ≤ (1358564048801/3125000000000 : ℝ)^6187
        have hw : |(668513727/1250000000 : ℝ)|=(668513727/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(525236397/1000000000 : ℝ)|^8235 ≤ (2122059738487/5000000000000 : ℝ)^6187
        have hw : |(525236397/1000000000 : ℝ)|=(525236397/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-114662331/500000000 : ℝ)|^8235 ≤ (3521188914279/25000000000000 : ℝ)^6187
        have hw : |(-114662331/500000000 : ℝ)|=(114662331/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s4_3 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4378284841/10000000000 : ℝ)*x 0 + (528744769/1250000000 : ℝ)*x 1 + (453191367/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378284841/10000000000 : ℝ)^8235 ≤ (33309619285197/100000000000000 : ℝ)^6187 := by
    have hnat : (4378284841 : ℕ)^8235*100000000000000^6187 ≤ 33309619285197^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378284841 10000000000 33309619285197 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528744769/1250000000 : ℝ)^8235 ≤ (3977013842247/12500000000000 : ℝ)^6187 := by
    have hnat : (528744769 : ℕ)^8235*12500000000000^6187 ≤ 3977013842247^6187*1250000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528744769 1250000000 3977013842247 12500000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (453191367/1000000000 : ℝ)^8235 ≤ (17437134978157/50000000000000 : ℝ)^6187 := by
    have hnat : (453191367 : ℕ)^8235*50000000000000^6187 ≤ 17437134978157^6187*1000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453191367 1000000000 17437134978157 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378284841/10000000000 : ℝ), (528744769/1250000000 : ℝ), (453191367/1000000000 : ℝ)] ![(33309619285197/100000000000000 : ℝ), (3977013842247/12500000000000 : ℝ), (17437134978157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378284841/10000000000 : ℝ)|^8235 ≤ (33309619285197/100000000000000 : ℝ)^6187
        have hw : |(4378284841/10000000000 : ℝ)|=(4378284841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528744769/1250000000 : ℝ)|^8235 ≤ (3977013842247/12500000000000 : ℝ)^6187
        have hw : |(528744769/1250000000 : ℝ)|=(528744769/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(453191367/1000000000 : ℝ)|^8235 ≤ (17437134978157/50000000000000 : ℝ)^6187
        have hw : |(453191367/1000000000 : ℝ)|=(453191367/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s4_4 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1107246301/5000000000 : ℝ)*x 0 + (131320549/250000000 : ℝ)*x 1 + (2703355529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1107246301/5000000000 : ℝ)^8235 ≤ (1344463775719/10000000000000 : ℝ)^6187 := by
    have hnat : (1107246301 : ℕ)^8235*10000000000000^6187 ≤ 1344463775719^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107246301 5000000000 1344463775719 10000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131320549/250000000 : ℝ)^8235 ≤ (21223060294873/50000000000000 : ℝ)^6187 := by
    have hnat : (131320549 : ℕ)^8235*50000000000000^6187 ≤ 21223060294873^6187*250000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131320549 250000000 21223060294873 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703355529/5000000000 : ℝ)^8235 ≤ (2205462081857/5000000000000 : ℝ)^6187 := by
    have hnat : (2703355529 : ℕ)^8235*5000000000000^6187 ≤ 2205462081857^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703355529 5000000000 2205462081857 5000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1107246301/5000000000 : ℝ), (131320549/250000000 : ℝ), (2703355529/5000000000 : ℝ)] ![(1344463775719/10000000000000 : ℝ), (21223060294873/50000000000000 : ℝ), (2205462081857/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1107246301/5000000000 : ℝ)|^8235 ≤ (1344463775719/10000000000000 : ℝ)^6187
        have hw : |(-1107246301/5000000000 : ℝ)|=(1107246301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131320549/250000000 : ℝ)|^8235 ≤ (21223060294873/50000000000000 : ℝ)^6187
        have hw : |(131320549/250000000 : ℝ)|=(131320549/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703355529/5000000000 : ℝ)|^8235 ≤ (2205462081857/5000000000000 : ℝ)^6187
        have hw : |(2703355529/5000000000 : ℝ)|=(2703355529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s4_5 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2654596947/5000000000 : ℝ)*x 0 + (-267362453/1250000000 : ℝ)*x 1 + (5406710999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654596947/5000000000 : ℝ)^8235 ≤ (43053500770859/100000000000000 : ℝ)^6187 := by
    have hnat : (2654596947 : ℕ)^8235*100000000000000^6187 ≤ 43053500770859^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654596947 5000000000 43053500770859 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (267362453/1250000000 : ℝ)^8235 ≤ (6418629109371/50000000000000 : ℝ)^6187 := by
    have hnat : (267362453 : ℕ)^8235*50000000000000^6187 ≤ 6418629109371^6187*1250000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267362453 1250000000 6418629109371 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406710999/10000000000 : ℝ)^8235 ≤ (22054620498237/50000000000000 : ℝ)^6187 := by
    have hnat : (5406710999 : ℕ)^8235*50000000000000^6187 ≤ 22054620498237^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406710999 10000000000 22054620498237 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2654596947/5000000000 : ℝ), (-267362453/1250000000 : ℝ), (5406710999/10000000000 : ℝ)] ![(43053500770859/100000000000000 : ℝ), (6418629109371/50000000000000 : ℝ), (22054620498237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2654596947/5000000000 : ℝ)|^8235 ≤ (43053500770859/100000000000000 : ℝ)^6187
        have hw : |(2654596947/5000000000 : ℝ)|=(2654596947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-267362453/1250000000 : ℝ)|^8235 ≤ (6418629109371/50000000000000 : ℝ)^6187
        have hw : |(-267362453/1250000000 : ℝ)|=(267362453/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406710999/10000000000 : ℝ)|^8235 ≤ (22054620498237/50000000000000 : ℝ)^6187
        have hw : |(5406710999/10000000000 : ℝ)|=(5406710999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s4_6 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327298461/2500000000 : ℝ)*x 0 + (1351677757/2500000000 : ℝ)*x 1 + (-534724913/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327298461/2500000000 : ℝ)^8235 ≤ (21526750115591/50000000000000 : ℝ)^6187 := by
    have hnat : (1327298461 : ℕ)^8235*50000000000000^6187 ≤ 21526750115591^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327298461 2500000000 21526750115591 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351677757/2500000000 : ℝ)^8235 ≤ (22054620655689/50000000000000 : ℝ)^6187 := by
    have hnat : (1351677757 : ℕ)^8235*50000000000000^6187 ≤ 22054620655689^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351677757 2500000000 22054620655689 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (534724913/2500000000 : ℝ)^8235 ≤ (641862922121/5000000000000 : ℝ)^6187 := by
    have hnat : (534724913 : ℕ)^8235*5000000000000^6187 ≤ 641862922121^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534724913 2500000000 641862922121 5000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327298461/2500000000 : ℝ), (1351677757/2500000000 : ℝ), (-534724913/2500000000 : ℝ)] ![(21526750115591/50000000000000 : ℝ), (22054620655689/50000000000000 : ℝ), (641862922121/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327298461/2500000000 : ℝ)|^8235 ≤ (21526750115591/50000000000000 : ℝ)^6187
        have hw : |(1327298461/2500000000 : ℝ)|=(1327298461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351677757/2500000000 : ℝ)|^8235 ≤ (22054620655689/50000000000000 : ℝ)^6187
        have hw : |(1351677757/2500000000 : ℝ)|=(1351677757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-534724913/2500000000 : ℝ)|^8235 ≤ (641862922121/5000000000000 : ℝ)^6187
        have hw : |(-534724913/2500000000 : ℝ)|=(534724913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s4_7 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (547287673/1250000000 : ℝ)*x 0 + (113275493/250000000 : ℝ)*x 1 + (4230855947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547287673/1250000000 : ℝ)^8235 ≤ (2081861675253/6250000000000 : ℝ)^6187 := by
    have hnat : (547287673 : ℕ)^8235*6250000000000^6187 ≤ 2081861675253^6187*1250000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547287673 1250000000 2081861675253 6250000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113275493/250000000 : ℝ)^8235 ≤ (6973022790211/20000000000000 : ℝ)^6187 := by
    have hnat : (113275493 : ℕ)^8235*20000000000000^6187 ≤ 6973022790211^6187*250000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113275493 250000000 6973022790211 20000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230855947/10000000000 : ℝ)^8235 ≤ (31825099232203/100000000000000 : ℝ)^6187 := by
    have hnat : (4230855947 : ℕ)^8235*100000000000000^6187 ≤ 31825099232203^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230855947 10000000000 31825099232203 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(547287673/1250000000 : ℝ), (113275493/250000000 : ℝ), (4230855947/10000000000 : ℝ)] ![(2081861675253/6250000000000 : ℝ), (6973022790211/20000000000000 : ℝ), (31825099232203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(547287673/1250000000 : ℝ)|^8235 ≤ (2081861675253/6250000000000 : ℝ)^6187
        have hw : |(547287673/1250000000 : ℝ)|=(547287673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(113275493/250000000 : ℝ)|^8235 ≤ (6973022790211/20000000000000 : ℝ)^6187
        have hw : |(113275493/250000000 : ℝ)|=(113275493/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230855947/10000000000 : ℝ)|^8235 ≤ (31825099232203/100000000000000 : ℝ)^6187
        have hw : |(4230855947/10000000000 : ℝ)|=(4230855947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1042_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14941/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2063/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1097/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1781/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14941/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2063/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14941/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2063/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14941/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2063/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14941/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2063/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14941/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2063/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14941/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2063/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2063/20000 : ℝ) ^ (4117/1024 : ℝ) ≤ (2161102356447443/20000000000000000000 : ℝ) := by
    have hpowers : (2063/20000 : ℝ)^4117 ≤ (2161102356447443/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2063 : ℕ)^4117*20000000000000000000^1024 ≤ 2161102356447443^1024*20000^4117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2063 20000 2161102356447443 20000000000000000000 4117 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2063/20000 : ℝ)) (X := (2161102356447443/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14941/100000 : ℝ) ^ (4117/1024 : ℝ) ≤ (47927745007084733/100000000000000000000 : ℝ) := by
    have hpowers : (14941/100000 : ℝ)^4117 ≤ (47927745007084733/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14941 : ℕ)^4117*100000000000000000000^1024 ≤ 47927745007084733^1024*100000^4117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14941 100000 47927745007084733 100000000000000000000 4117 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14941/100000 : ℝ)) (X := (47927745007084733/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002161102356447443/10000000000000000000 : ℝ) ≤ (5000268738060333/5000000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (10002161102356447443/10000000000000000000 : ℝ)^1024 ≤ (5000268738060333/5000000000000000 : ℝ)^4117 := by
      have hnat : (10002161102356447443 : ℕ)^1024*5000000000000000^4117 ≤ 5000268738060333^4117*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002161102356447443 10000000000000000000 5000268738060333 5000000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000268738060333/5000000000000000 : ℝ)) (X := (10002161102356447443/10000000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25014683314197330487/25000000000000000000 : ℝ) ≤ (5000730259782983/5000000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (25014683314197330487/25000000000000000000 : ℝ)^1024 ≤ (5000730259782983/5000000000000000 : ℝ)^4117 := by
      have hnat : (25014683314197330487 : ℕ)^1024*5000000000000000^4117 ≤ 5000730259782983^4117*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014683314197330487 25000000000000000000 5000730259782983 5000000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000730259782983/5000000000000000 : ℝ)) (X := (25014683314197330487/25000000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50047927745007084733/50000000000000000000 : ℝ) ≤ (5001191781505633/5000000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (50047927745007084733/50000000000000000000 : ℝ)^1024 ≤ (5001191781505633/5000000000000000 : ℝ)^4117 := by
      have hnat : (50047927745007084733 : ℕ)^1024*5000000000000000^4117 ≤ 5001191781505633^4117*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50047927745007084733 50000000000000000000 5001191781505633 5000000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001191781505633/5000000000000000 : ℝ)) (X := (50047927745007084733/50000000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2161102356447443/20000000000000000000 : ℝ) ≤ ((11560860994564415479/11565000000000000000 : ℝ)+2*(9230434453/4626000000000 : ℝ)*(2063/20000 : ℝ))^(4117/1024 : ℝ) := by
    rw [show (11560860994564415479/11565000000000000000 : ℝ)+2*(9230434453/4626000000000 : ℝ)*(2063/20000 : ℝ)=(5000268738060333/5000000000000000 : ℝ) by norm_num, show 1+2*(2161102356447443/20000000000000000000 : ℝ)=(10002161102356447443/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(47927745007084733/100000000000000000000 : ℝ)+(2161102356447443/20000000000000000000 : ℝ) ≤ ((11560860994564415479/11565000000000000000 : ℝ)+(9230434453/4626000000000 : ℝ)*((14941/100000 : ℝ)+(2063/20000 : ℝ)))^(4117/1024 : ℝ) := by
    rw [show (11560860994564415479/11565000000000000000 : ℝ)+(9230434453/4626000000000 : ℝ)*((14941/100000 : ℝ)+(2063/20000 : ℝ))=(5000730259782983/5000000000000000 : ℝ) by norm_num, show 1+(47927745007084733/100000000000000000000 : ℝ)+(2161102356447443/20000000000000000000 : ℝ)=(25014683314197330487/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(47927745007084733/100000000000000000000 : ℝ) ≤ ((11560860994564415479/11565000000000000000 : ℝ)+2*(9230434453/4626000000000 : ℝ)*(14941/100000 : ℝ))^(4117/1024 : ℝ) := by
    rw [show (11560860994564415479/11565000000000000000 : ℝ)+2*(9230434453/4626000000000 : ℝ)*(14941/100000 : ℝ)=(5001191781505633/5000000000000000 : ℝ) by norm_num, show 1+2*(47927745007084733/100000000000000000000 : ℝ)=(50047927745007084733/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11560860994564415479/11565000000000000000 : ℝ)*(X 1 0+X 2 0)+(9230434453/4626000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (2063/20000 : ℝ)) (hi := (14941/100000 : ℝ)) (c := (11560860994564415479/11565000000000000000 : ℝ)) (alpha := (9230434453/4626000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11560860994564415479/11565000000000000000 : ℝ)*(X 0 1+X 2 1)+(9230434453/4626000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (2063/20000 : ℝ)) (hi := (14941/100000 : ℝ)) (c := (11560860994564415479/11565000000000000000 : ℝ)) (alpha := (9230434453/4626000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11560860994564415479/11565000000000000000 : ℝ)*(X 0 2+X 1 2)+(9230434453/4626000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (2063/20000 : ℝ)) (hi := (14941/100000 : ℝ)) (c := (11560860994564415479/11565000000000000000 : ℝ)) (alpha := (9230434453/4626000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-34601311/156250000 : ℝ)*X 0 0+(5407171101/10000000000 : ℝ)*X 0 1+(262618201/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668513721/1250000000 : ℝ)*X 1 0+(-1146623293/5000000000 : ℝ)*X 1 1+(1313091011/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668513727/1250000000 : ℝ)*X 2 0+(525236397/1000000000 : ℝ)*X 2 1+(-114662331/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4378284841/10000000000 : ℝ)*X 0 0+(528744769/1250000000 : ℝ)*X 0 1+(453191367/1000000000 : ℝ)*X 0 2+(4378284841/10000000000 : ℝ)*X 1 0+(528744769/1250000000 : ℝ)*X 1 1+(453191367/1000000000 : ℝ)*X 1 2+(4378284841/10000000000 : ℝ)*X 2 0+(528744769/1250000000 : ℝ)*X 2 1+(453191367/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1107246301/5000000000 : ℝ)*X 0 0+(131320549/250000000 : ℝ)*X 0 1+(2703355529/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2654596947/5000000000 : ℝ)*X 1 0+(-267362453/1250000000 : ℝ)*X 1 1+(5406710999/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327298461/2500000000 : ℝ)*X 2 0+(1351677757/2500000000 : ℝ)*X 2 1+(-534724913/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((547287673/1250000000 : ℝ)*X 0 0+(113275493/250000000 : ℝ)*X 0 1+(4230855947/10000000000 : ℝ)*X 0 2+(547287673/1250000000 : ℝ)*X 1 0+(113275493/250000000 : ℝ)*X 1 1+(4230855947/10000000000 : ℝ)*X 1 2+(547287673/1250000000 : ℝ)*X 2 0+(113275493/250000000 : ℝ)*X 2 1+(4230855947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (728414637476991223956878309/192750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (166909773/20000000000000 : ℝ)*(base19) + (435058829/50000000000000 : ℝ)*(base23) + (11983933/100000000000000 : ℝ)*(lower2) + (30243281/25000000000000 : ℝ)*(upper3) + (34924923/50000000000000 : ℝ)*(upper5) + (4885729165513229/100000000000000 : ℝ)*(major0) + (4885729165513229/100000000000000 : ℝ)*(major1) + (4885729165513229/100000000000000 : ℝ)*(major2) + (1614918216972067/25000000000000 : ℝ)*(sp0) + (3229845435171059/50000000000000 : ℝ)*(sp1) + (258387633390933/4000000000000 : ℝ)*(sp2) + (3311755634837691/100000000000000 : ℝ)*(sp3) + (9418501357/50000000000000 : ℝ)*(sp4) + (2716332241/25000000000000 : ℝ)*(sp7) + (1655883250083327/50000000000000 : ℝ)*(f.failure) + (6459691704890983/100000000000000 : ℝ)*(f.sum) + (19819548375421/2313000000000000000000000000 : ℝ)*base66 + (21255612201739371691/1156500000000000000000000000000000 : ℝ)*base67 + (3723657356044371691/1156500000000000000000000000000000 : ℝ)*base69 + (64369668432128309/1156500000000000000000000000000000 : ℝ)*base72 + (1726495556681/1156500000000000000000000000 : ℝ)*base74 + (14156586776314371691/1156500000000000000000000000000000 : ℝ)*base75 + (24107830703076128309/1156500000000000000000000000000000 : ℝ)*base78 + (15424819373116371691/1156500000000000000000000000000000 : ℝ)*base79 + (964916516993/289125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (9750197/2500000000000000000000 : ℝ)*base90 + (9750197/2500000000000000000000 : ℝ)*base92 + (9750197/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (462191525977096066785569489/48187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (219313863/10000000000000 : ℝ)*(base19) + (89106151/4000000000000 : ℝ)*(base23) + (86025979/100000000000000 : ℝ)*(upper2) + (13106611/12500000000000 : ℝ)*(upper3) + (44618733/10000000000000 : ℝ)*(upper5) + (2457426208347191/50000000000000 : ℝ)*(major0) + (2457426208347191/50000000000000 : ℝ)*(major1) + (2457426208347191/50000000000000 : ℝ)*(major2) + (13997355883/25000000000000 : ℝ)*(sp1) + (46941520989/100000000000000 : ℝ)*(sp2) + (6498196966801031/100000000000000 : ℝ)*(sp4) + (649813878423887/10000000000000 : ℝ)*(sp5) + (6498147797626267/100000000000000 : ℝ)*(sp6) + (832876886717571/25000000000000 : ℝ)*(sp7) + (832876886717571/25000000000000 : ℝ)*(f.failure) + (6498196966801031/100000000000000 : ℝ)*(f.sum) + (3750385040431/1156500000000000000000000000 : ℝ)*base66 + (5594774905615930511/578250000000000000000000000000000 : ℝ)*base68 + (1692014446710430511/578250000000000000000000000000000 : ℝ)*base70 + (3057780975925069489/578250000000000000000000000000000 : ℝ)*base71 + (2742309304991/578250000000000000000000000 : ℝ)*base74 + (11431544966865430511/578250000000000000000000000000000 : ℝ)*base76 + (5957314634326930511/578250000000000000000000000000000 : ℝ)*base78 + (1573796750715430511/578250000000000000000000000000000 : ℝ)*base80 + (810130074523/144562500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (4293919/1250000000000000000000 : ℝ)*base89 + (4293919/1250000000000000000000 : ℝ)*base91 + (4293919/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1042_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14941/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2063/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1097/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1781/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1042_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1042_s5_0 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2215380717/10000000000 : ℝ)*x 0 + (5397700603/10000000000 : ℝ)*x 1 + (5261246897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2215380717/10000000000 : ℝ)^8235 ≤ (3362953744831/25000000000000 : ℝ)^6187 := by
    have hnat : (2215380717 : ℕ)^8235*25000000000000^6187 ≤ 3362953744831^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215380717 10000000000 3362953744831 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397700603/10000000000 : ℝ)^8235 ≤ (44011426337551/100000000000000 : ℝ)^6187 := by
    have hnat : (5397700603 : ℕ)^8235*100000000000000^6187 ≤ 44011426337551^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397700603 10000000000 44011426337551 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261246897/10000000000 : ℝ)^8235 ≤ (42536758670733/100000000000000 : ℝ)^6187 := by
    have hnat : (5261246897 : ℕ)^8235*100000000000000^6187 ≤ 42536758670733^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261246897 10000000000 42536758670733 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2215380717/10000000000 : ℝ), (5397700603/10000000000 : ℝ), (5261246897/10000000000 : ℝ)] ![(3362953744831/25000000000000 : ℝ), (44011426337551/100000000000000 : ℝ), (42536758670733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2215380717/10000000000 : ℝ)|^8235 ≤ (3362953744831/25000000000000 : ℝ)^6187
        have hw : |(-2215380717/10000000000 : ℝ)|=(2215380717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397700603/10000000000 : ℝ)|^8235 ≤ (44011426337551/100000000000000 : ℝ)^6187
        have hw : |(5397700603/10000000000 : ℝ)|=(5397700603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261246897/10000000000 : ℝ)|^8235 ≤ (42536758670733/100000000000000 : ℝ)^6187
        have hw : |(5261246897/10000000000 : ℝ)|=(5261246897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s5_1 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672879037/5000000000 : ℝ)*x 0 + (-2284663839/10000000000 : ℝ)*x 1 + (5261246813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672879037/5000000000 : ℝ)^8235 ≤ (43448606385131/100000000000000 : ℝ)^6187 := by
    have hnat : (2672879037 : ℕ)^8235*100000000000000^6187 ≤ 43448606385131^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672879037 5000000000 43448606385131 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2284663839/10000000000 : ℝ)^8235 ≤ (14014635844419/100000000000000 : ℝ)^6187 := by
    have hnat : (2284663839 : ℕ)^8235*100000000000000^6187 ≤ 14014635844419^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2284663839 10000000000 14014635844419 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261246813/10000000000 : ℝ)^8235 ≤ (10634189441699/25000000000000 : ℝ)^6187 := by
    have hnat : (5261246813 : ℕ)^8235*25000000000000^6187 ≤ 10634189441699^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261246813 10000000000 10634189441699 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672879037/5000000000 : ℝ), (-2284663839/10000000000 : ℝ), (5261246813/10000000000 : ℝ)] ![(43448606385131/100000000000000 : ℝ), (14014635844419/100000000000000 : ℝ), (10634189441699/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672879037/5000000000 : ℝ)|^8235 ≤ (43448606385131/100000000000000 : ℝ)^6187
        have hw : |(2672879037/5000000000 : ℝ)|=(2672879037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2284663839/10000000000 : ℝ)|^8235 ≤ (14014635844419/100000000000000 : ℝ)^6187
        have hw : |(-2284663839/10000000000 : ℝ)|=(2284663839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261246813/10000000000 : ℝ)|^8235 ≤ (10634189441699/25000000000000 : ℝ)^6187
        have hw : |(5261246813/10000000000 : ℝ)|=(5261246813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s5_2 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668219763/1250000000 : ℝ)*x 0 + (2630623417/5000000000 : ℝ)*x 1 + (-228466377/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668219763/1250000000 : ℝ)^8235 ≤ (43448606709673/100000000000000 : ℝ)^6187 := by
    have hnat : (668219763 : ℕ)^8235*100000000000000^6187 ≤ 43448606709673^6187*1250000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668219763 1250000000 43448606709673 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630623417/5000000000 : ℝ)^8235 ≤ (2126837899639/5000000000000 : ℝ)^6187 := by
    have hnat : (2630623417 : ℕ)^8235*5000000000000^6187 ≤ 2126837899639^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630623417 5000000000 2126837899639 5000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (228466377/1000000000 : ℝ)^8235 ≤ (14014635281051/100000000000000 : ℝ)^6187 := by
    have hnat : (228466377 : ℕ)^8235*100000000000000^6187 ≤ 14014635281051^6187*1000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228466377 1000000000 14014635281051 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668219763/1250000000 : ℝ), (2630623417/5000000000 : ℝ), (-228466377/1000000000 : ℝ)] ![(43448606709673/100000000000000 : ℝ), (2126837899639/5000000000000 : ℝ), (14014635281051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668219763/1250000000 : ℝ)|^8235 ≤ (43448606709673/100000000000000 : ℝ)^6187
        have hw : |(668219763/1250000000 : ℝ)|=(668219763/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630623417/5000000000 : ℝ)|^8235 ≤ (2126837899639/5000000000000 : ℝ)^6187
        have hw : |(2630623417/5000000000 : ℝ)|=(2630623417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-228466377/1000000000 : ℝ)|^8235 ≤ (14014635281051/100000000000000 : ℝ)^6187
        have hw : |(-228466377/1000000000 : ℝ)|=(228466377/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s5_3 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2189403397/5000000000 : ℝ)*x 0 + (849557757/2000000000 : ℝ)*x 1 + (4513945413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189403397/5000000000 : ℝ)^8235 ≤ (33314904822119/100000000000000 : ℝ)^6187 := by
    have hnat : (2189403397 : ℕ)^8235*100000000000000^6187 ≤ 33314904822119^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189403397 5000000000 33314904822119 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (849557757/2000000000 : ℝ)^8235 ≤ (7998686158697/25000000000000 : ℝ)^6187 := by
    have hnat : (849557757 : ℕ)^8235*25000000000000^6187 ≤ 7998686158697^6187*2000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849557757 2000000000 7998686158697 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4513945413/10000000000 : ℝ)^8235 ≤ (34690350531693/100000000000000 : ℝ)^6187 := by
    have hnat : (4513945413 : ℕ)^8235*100000000000000^6187 ≤ 34690350531693^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513945413 10000000000 34690350531693 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2189403397/5000000000 : ℝ), (849557757/2000000000 : ℝ), (4513945413/10000000000 : ℝ)] ![(33314904822119/100000000000000 : ℝ), (7998686158697/25000000000000 : ℝ), (34690350531693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2189403397/5000000000 : ℝ)|^8235 ≤ (33314904822119/100000000000000 : ℝ)^6187
        have hw : |(2189403397/5000000000 : ℝ)|=(2189403397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(849557757/2000000000 : ℝ)|^8235 ≤ (7998686158697/25000000000000 : ℝ)^6187
        have hw : |(849557757/2000000000 : ℝ)|=(849557757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4513945413/10000000000 : ℝ)|^8235 ≤ (34690350531693/100000000000000 : ℝ)^6187
        have hw : |(4513945413/10000000000 : ℝ)|=(4513945413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s5_4 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-276923287/1250000000 : ℝ)*x 0 + (5261603041/10000000000 : ℝ)*x 1 + (2698671651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (276923287/1250000000 : ℝ)^8235 ≤ (6725930034263/50000000000000 : ℝ)^6187 := by
    have hnat : (276923287 : ℕ)^8235*50000000000000^6187 ≤ 6725930034263^6187*1250000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276923287 1250000000 6725930034263 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261603041/10000000000 : ℝ)^8235 ≤ (10635147809301/25000000000000 : ℝ)^6187 := by
    have hnat : (5261603041 : ℕ)^8235*25000000000000^6187 ≤ 10635147809301^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261603041 10000000000 10635147809301 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698671651/5000000000 : ℝ)^8235 ≤ (22003774339283/50000000000000 : ℝ)^6187 := by
    have hnat : (2698671651 : ℕ)^8235*50000000000000^6187 ≤ 22003774339283^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698671651 5000000000 22003774339283 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-276923287/1250000000 : ℝ), (5261603041/10000000000 : ℝ), (2698671651/5000000000 : ℝ)] ![(6725930034263/50000000000000 : ℝ), (10635147809301/25000000000000 : ℝ), (22003774339283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-276923287/1250000000 : ℝ)|^8235 ≤ (6725930034263/50000000000000 : ℝ)^6187
        have hw : |(-276923287/1250000000 : ℝ)|=(276923287/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261603041/10000000000 : ℝ)|^8235 ≤ (10635147809301/25000000000000 : ℝ)^6187
        have hw : |(5261603041/10000000000 : ℝ)|=(5261603041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698671651/5000000000 : ℝ)|^8235 ≤ (22003774339283/50000000000000 : ℝ)^6187
        have hw : |(2698671651/5000000000 : ℝ)|=(2698671651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s5_5 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (165982961/312500000 : ℝ)*x 0 + (-2148567719/10000000000 : ℝ)*x 1 + (5397342993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165982961/312500000 : ℝ)^8235 ≤ (4307790512187/10000000000000 : ℝ)^6187 := by
    have hnat : (165982961 : ℕ)^8235*10000000000000^6187 ≤ 4307790512187^6187*312500000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165982961 312500000 4307790512187 10000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2148567719/10000000000 : ℝ)^8235 ≤ (1291454953889/10000000000000 : ℝ)^6187 := by
    have hnat : (2148567719 : ℕ)^8235*10000000000000^6187 ≤ 1291454953889^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148567719 10000000000 1291454953889 10000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397342993/10000000000 : ℝ)^8235 ≤ (22003772662569/50000000000000 : ℝ)^6187 := by
    have hnat : (5397342993 : ℕ)^8235*50000000000000^6187 ≤ 22003772662569^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397342993 10000000000 22003772662569 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165982961/312500000 : ℝ), (-2148567719/10000000000 : ℝ), (5397342993/10000000000 : ℝ)] ![(4307790512187/10000000000000 : ℝ), (1291454953889/10000000000000 : ℝ), (22003772662569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165982961/312500000 : ℝ)|^8235 ≤ (4307790512187/10000000000000 : ℝ)^6187
        have hw : |(165982961/312500000 : ℝ)|=(165982961/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2148567719/10000000000 : ℝ)|^8235 ≤ (1291454953889/10000000000000 : ℝ)^6187
        have hw : |(-2148567719/10000000000 : ℝ)|=(2148567719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397342993/10000000000 : ℝ)|^8235 ≤ (22003772662569/50000000000000 : ℝ)^6187
        have hw : |(5397342993/10000000000 : ℝ)|=(5397342993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s5_6 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655727369/5000000000 : ℝ)*x 0 + (1079468581/2000000000 : ℝ)*x 1 + (-134285491/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655727369/5000000000 : ℝ)^8235 ≤ (43077904970739/100000000000000 : ℝ)^6187 := by
    have hnat : (2655727369 : ℕ)^8235*100000000000000^6187 ≤ 43077904970739^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655727369 5000000000 43077904970739 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079468581/2000000000 : ℝ)^8235 ≤ (11001886092529/25000000000000 : ℝ)^6187 := by
    have hnat : (1079468581 : ℕ)^8235*25000000000000^6187 ≤ 11001886092529^6187*2000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079468581 2000000000 11001886092529 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134285491/625000000 : ℝ)^8235 ≤ (258291012699/2000000000000 : ℝ)^6187 := by
    have hnat : (134285491 : ℕ)^8235*2000000000000^6187 ≤ 258291012699^6187*625000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134285491 625000000 258291012699 2000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655727369/5000000000 : ℝ), (1079468581/2000000000 : ℝ), (-134285491/625000000 : ℝ)] ![(43077904970739/100000000000000 : ℝ), (11001886092529/25000000000000 : ℝ), (258291012699/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655727369/5000000000 : ℝ)|^8235 ≤ (43077904970739/100000000000000 : ℝ)^6187
        have hw : |(2655727369/5000000000 : ℝ)|=(2655727369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079468581/2000000000 : ℝ)|^8235 ≤ (11001886092529/25000000000000 : ℝ)^6187
        have hw : |(1079468581/2000000000 : ℝ)|=(1079468581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-134285491/625000000 : ℝ)|^8235 ≤ (258291012699/2000000000000 : ℝ)^6187
        have hw : |(-134285491/625000000 : ℝ)|=(134285491/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s5_7 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2189408861/5000000000 : ℝ)*x 0 + (2256625403/5000000000 : ℝ)*x 1 + (4248486431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189408861/5000000000 : ℝ)^8235 ≤ (16657507743159/50000000000000 : ℝ)^6187 := by
    have hnat : (2189408861 : ℕ)^8235*50000000000000^6187 ≤ 16657507743159^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189408861 5000000000 16657507743159 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2256625403/5000000000 : ℝ)^8235 ≤ (1387329821343/4000000000000 : ℝ)^6187 := by
    have hnat : (2256625403 : ℕ)^8235*4000000000000^6187 ≤ 1387329821343^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256625403 5000000000 1387329821343 4000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4248486431/10000000000 : ℝ)^8235 ≤ (16000869482523/50000000000000 : ℝ)^6187 := by
    have hnat : (4248486431 : ℕ)^8235*50000000000000^6187 ≤ 16000869482523^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248486431 10000000000 16000869482523 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2189408861/5000000000 : ℝ), (2256625403/5000000000 : ℝ), (4248486431/10000000000 : ℝ)] ![(16657507743159/50000000000000 : ℝ), (1387329821343/4000000000000 : ℝ), (16000869482523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2189408861/5000000000 : ℝ)|^8235 ≤ (16657507743159/50000000000000 : ℝ)^6187
        have hw : |(2189408861/5000000000 : ℝ)|=(2189408861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2256625403/5000000000 : ℝ)|^8235 ≤ (1387329821343/4000000000000 : ℝ)^6187
        have hw : |(2256625403/5000000000 : ℝ)|=(2256625403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4248486431/10000000000 : ℝ)|^8235 ≤ (16000869482523/50000000000000 : ℝ)^6187
        have hw : |(4248486431/10000000000 : ℝ)|=(4248486431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1042_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1781/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1097/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11159/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14049/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1781/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1097/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1781/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1097/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1781/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1097/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1781/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1097/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1781/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1097/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1781/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1097/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1097/10000 : ℝ) ^ (4117/1024 : ℝ) ≤ (138402281005229/1000000000000000000 : ℝ) := by
    have hpowers : (1097/10000 : ℝ)^4117 ≤ (138402281005229/1000000000000000000 : ℝ)^1024 := by
      have hnat : (1097 : ℕ)^4117*1000000000000000000^1024 ≤ 138402281005229^1024*10000^4117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1097 10000 138402281005229 1000000000000000000 4117 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1097/10000 : ℝ)) (X := (138402281005229/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1781/12500 : ℝ) ^ (4117/1024 : ℝ) ≤ (39596880197757057/100000000000000000000 : ℝ) := by
    have hpowers : (1781/12500 : ℝ)^4117 ≤ (39596880197757057/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1781 : ℕ)^4117*100000000000000000000^1024 ≤ 39596880197757057^1024*12500^4117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1781 12500 39596880197757057 100000000000000000000 4117 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1781/12500 : ℝ)) (X := (39596880197757057/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (500138402281005229/500000000000000000 : ℝ) ≤ (1250086051252083/1250000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (500138402281005229/500000000000000000 : ℝ)^1024 ≤ (1250086051252083/1250000000000000 : ℝ)^4117 := by
      have hnat : (500138402281005229 : ℕ)^1024*1250000000000000^4117 ≤ 1250086051252083^4117*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500138402281005229 500000000000000000 1250086051252083 1250000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250086051252083/1250000000000000 : ℝ)) (X := (500138402281005229/500000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100053437108298279957/100000000000000000000 : ℝ) ≤ (5000664423347881/5000000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (100053437108298279957/100000000000000000000 : ℝ)^1024 ≤ (5000664423347881/5000000000000000 : ℝ)^4117 := by
      have hnat : (100053437108298279957 : ℕ)^1024*5000000000000000^4117 ≤ 5000664423347881^4117*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100053437108298279957 100000000000000000000 5000664423347881 5000000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000664423347881/5000000000000000 : ℝ)) (X := (100053437108298279957/100000000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039596880197757057/50000000000000000000 : ℝ) ≤ (500098464168743/500000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (50039596880197757057/50000000000000000000 : ℝ)^1024 ≤ (500098464168743/500000000000000 : ℝ)^4117 := by
      have hnat : (50039596880197757057 : ℕ)^1024*500000000000000^4117 ≤ 500098464168743^4117*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039596880197757057 50000000000000000000 500098464168743 500000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500098464168743/500000000000000 : ℝ)) (X := (50039596880197757057/50000000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(138402281005229/1000000000000000000 : ℝ) ≤ ((4096025678411901809/4097500000000000000 : ℝ)+2*(320218339549/163900000000000 : ℝ)*(1097/10000 : ℝ))^(4117/1024 : ℝ) := by
    rw [show (4096025678411901809/4097500000000000000 : ℝ)+2*(320218339549/163900000000000 : ℝ)*(1097/10000 : ℝ)=(1250086051252083/1250000000000000 : ℝ) by norm_num, show 1+2*(138402281005229/1000000000000000000 : ℝ)=(500138402281005229/500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39596880197757057/100000000000000000000 : ℝ)+(138402281005229/1000000000000000000 : ℝ) ≤ ((4096025678411901809/4097500000000000000 : ℝ)+(320218339549/163900000000000 : ℝ)*((1781/12500 : ℝ)+(1097/10000 : ℝ)))^(4117/1024 : ℝ) := by
    rw [show (4096025678411901809/4097500000000000000 : ℝ)+(320218339549/163900000000000 : ℝ)*((1781/12500 : ℝ)+(1097/10000 : ℝ))=(5000664423347881/5000000000000000 : ℝ) by norm_num, show 1+(39596880197757057/100000000000000000000 : ℝ)+(138402281005229/1000000000000000000 : ℝ)=(100053437108298279957/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39596880197757057/100000000000000000000 : ℝ) ≤ ((4096025678411901809/4097500000000000000 : ℝ)+2*(320218339549/163900000000000 : ℝ)*(1781/12500 : ℝ))^(4117/1024 : ℝ) := by
    rw [show (4096025678411901809/4097500000000000000 : ℝ)+2*(320218339549/163900000000000 : ℝ)*(1781/12500 : ℝ)=(500098464168743/500000000000000 : ℝ) by norm_num, show 1+2*(39596880197757057/100000000000000000000 : ℝ)=(50039596880197757057/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4096025678411901809/4097500000000000000 : ℝ)*(X 1 0+X 2 0)+(320218339549/163900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (1097/10000 : ℝ)) (hi := (1781/12500 : ℝ)) (c := (4096025678411901809/4097500000000000000 : ℝ)) (alpha := (320218339549/163900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4096025678411901809/4097500000000000000 : ℝ)*(X 0 1+X 2 1)+(320218339549/163900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (1097/10000 : ℝ)) (hi := (1781/12500 : ℝ)) (c := (4096025678411901809/4097500000000000000 : ℝ)) (alpha := (320218339549/163900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4096025678411901809/4097500000000000000 : ℝ)*(X 0 2+X 1 2)+(320218339549/163900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (1097/10000 : ℝ)) (hi := (1781/12500 : ℝ)) (c := (4096025678411901809/4097500000000000000 : ℝ)) (alpha := (320218339549/163900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2215380717/10000000000 : ℝ)*X 0 0+(5397700603/10000000000 : ℝ)*X 0 1+(5261246897/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672879037/5000000000 : ℝ)*X 1 0+(-2284663839/10000000000 : ℝ)*X 1 1+(5261246813/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668219763/1250000000 : ℝ)*X 2 0+(2630623417/5000000000 : ℝ)*X 2 1+(-228466377/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2189403397/5000000000 : ℝ)*X 0 0+(849557757/2000000000 : ℝ)*X 0 1+(4513945413/10000000000 : ℝ)*X 0 2+(2189403397/5000000000 : ℝ)*X 1 0+(849557757/2000000000 : ℝ)*X 1 1+(4513945413/10000000000 : ℝ)*X 1 2+(2189403397/5000000000 : ℝ)*X 2 0+(849557757/2000000000 : ℝ)*X 2 1+(4513945413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-276923287/1250000000 : ℝ)*X 0 0+(5261603041/10000000000 : ℝ)*X 0 1+(2698671651/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165982961/312500000 : ℝ)*X 1 0+(-2148567719/10000000000 : ℝ)*X 1 1+(5397342993/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655727369/5000000000 : ℝ)*X 2 0+(1079468581/2000000000 : ℝ)*X 2 1+(-134285491/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2189408861/5000000000 : ℝ)*X 0 0+(2256625403/5000000000 : ℝ)*X 0 1+(4248486431/10000000000 : ℝ)*X 0 2+(2189408861/5000000000 : ℝ)*X 1 0+(2256625403/5000000000 : ℝ)*X 1 1+(4248486431/10000000000 : ℝ)*X 1 2+(2189408861/5000000000 : ℝ)*X 2 0+(2256625403/5000000000 : ℝ)*X 2 1+(4248486431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (59440650893588038633041/8195000000000000000000000000 : ℝ) := by norm_num
    linear_combination (812984367/50000000000000 : ℝ)*(base19) + (801443717/50000000000000 : ℝ)*(base23) + (3432443/10000000000000 : ℝ)*(lower2) + (105786277/100000000000000 : ℝ)*(upper3) + (168189029/100000000000000 : ℝ)*(upper5) + (2771451350702011/50000000000000 : ℝ)*(major0) + (2771451350702011/50000000000000 : ℝ)*(major1) + (2771451350702011/50000000000000 : ℝ)*(major2) + (3664266312830919/50000000000000 : ℝ)*(sp0) + (7328575318286943/100000000000000 : ℝ)*(sp1) + (7328575341368243/100000000000000 : ℝ)*(sp2) + (93930186429071/2500000000000 : ℝ)*(sp3) + (44318593839/100000000000000 : ℝ)*(sp4) + (2594951679/12500000000000 : ℝ)*(sp7) + (234826763548517/6250000000000 : ℝ)*(f.failure) + (7328576944255677/100000000000000 : ℝ)*(f.sum) + (1627873752169/1024375000000000000000000000 : ℝ)*base66 + (247821001589937899/204875000000000000000000000000000 : ℝ)*base67 + (976839567106187101/204875000000000000000000000000000 : ℝ)*base70 + (4372453688772437101/204875000000000000000000000000000 : ℝ)*base72 + (82803990770153/8195000000000000000000000000 : ℝ)*base73 + (919415907118187899/204875000000000000000000000000000 : ℝ)*base75 + (5616959396286187101/204875000000000000000000000000000 : ℝ)*base78 + (1202755679538562899/204875000000000000000000000000000 : ℝ)*base79 + (2705059042461/1024375000000000000000000000 : ℝ)*base81 + (1390713/312500000000000000000 : ℝ)*base89 + (1390713/312500000000000000000 : ℝ)*base91 + (1390713/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (988559370371410987089/149000000000000000000000000 : ℝ) := by norm_num
    linear_combination (367568161/100000000000000 : ℝ)*(base19) + (377879097/100000000000000 : ℝ)*(base23) + (94330657/100000000000000 : ℝ)*(lower3) + (23518641/50000000000000 : ℝ)*(lower4) + (139299590530177/2500000000000 : ℝ)*(major0) + (139299590530177/2500000000000 : ℝ)*(major1) + (139299590530177/2500000000000 : ℝ)*(major2) + (3286119583/50000000000000 : ℝ)*(sp0) + (4603890027/50000000000000 : ℝ)*(sp1) + (98796633/100000000000000 : ℝ)*(sp2) + (736701987964877/10000000000000 : ℝ)*(sp4) + (7367016876539719/100000000000000 : ℝ)*(sp5) + (1473405195042441/20000000000000 : ℝ)*(sp6) + (1888470284685997/50000000000000 : ℝ)*(sp7) + (1888470284685997/50000000000000 : ℝ)*(f.failure) + (1473405290377587/20000000000000 : ℝ)*(f.sum) + (45512404277/14900000000000000000000000 : ℝ)*base65 + (7785479046530437/931250000000000000000000000000 : ℝ)*base68 + (7040633656380437/931250000000000000000000000000 : ℝ)*base70 + (11176657181719563/931250000000000000000000000000 : ℝ)*base71 + (708933863709/149000000000000000000000000 : ℝ)*base74 + (3192034070975813/931250000000000000000000000000 : ℝ)*base75 + (8173943586332063/931250000000000000000000000000 : ℝ)*base77 + (18480828284474187/931250000000000000000000000000 : ℝ)*base80 + (211321523033/37250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (2364433/2500000000000000000000 : ℝ)*base89 + (2364433/2500000000000000000000 : ℝ)*base91 + (2364433/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1042_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1781/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1097/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11159/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1042_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1042_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (841/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8593/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11159/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1042_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1042_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1042_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (841/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8593/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11159/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1042_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
