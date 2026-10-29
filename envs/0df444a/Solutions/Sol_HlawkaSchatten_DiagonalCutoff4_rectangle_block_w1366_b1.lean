-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1366_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:19:31.642255+00:00
-- url     : https://prove2.me/submissions/f1057331-2940-4714-9c68-84162d6dbc39

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
theorem support_rectangle_w1366_s3_0 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2021887521/10000000000 : ℝ)*x 0 + (1356049453/2500000000 : ℝ)*x 1 + (52335927/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2021887521/10000000000 : ℝ)^2163 ≤ (3078943881221/25000000000000 : ℝ)^1651 := by
    have hnat : (2021887521 : ℕ)^2163*25000000000000^1651 ≤ 3078943881221^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021887521 10000000000 3078943881221 25000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356049453/2500000000 : ℝ)^2163 ≤ (8973853032041/20000000000000 : ℝ)^1651 := by
    have hnat : (1356049453 : ℕ)^2163*20000000000000^1651 ≤ 8973853032041^1651*2500000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356049453 2500000000 8973853032041 20000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52335927/100000000 : ℝ)^2163 ≤ (42814959300661/100000000000000 : ℝ)^1651 := by
    have hnat : (52335927 : ℕ)^2163*100000000000000^1651 ≤ 42814959300661^1651*100000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52335927 100000000 42814959300661 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2021887521/10000000000 : ℝ), (1356049453/2500000000 : ℝ), (52335927/100000000 : ℝ)] ![(3078943881221/25000000000000 : ℝ), (8973853032041/20000000000000 : ℝ), (42814959300661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2021887521/10000000000 : ℝ)|^2163 ≤ (3078943881221/25000000000000 : ℝ)^1651
        have hw : |(-2021887521/10000000000 : ℝ)|=(2021887521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356049453/2500000000 : ℝ)|^2163 ≤ (8973853032041/20000000000000 : ℝ)^1651
        have hw : |(1356049453/2500000000 : ℝ)|=(1356049453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52335927/100000000 : ℝ)|^2163 ≤ (42814959300661/100000000000000 : ℝ)^1651
        have hw : |(52335927/100000000 : ℝ)|=(52335927/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s3_1 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (535182889/1000000000 : ℝ)*x 0 + (-2119243727/10000000000 : ℝ)*x 1 + (2616796301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535182889/1000000000 : ℝ)^2163 ≤ (22043302858921/50000000000000 : ℝ)^1651 := by
    have hnat : (535182889 : ℕ)^2163*50000000000000^1651 ≤ 22043302858921^1651*1000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535182889 1000000000 22043302858921 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2119243727/10000000000 : ℝ)^2163 ≤ (13098436016129/100000000000000 : ℝ)^1651 := by
    have hnat : (2119243727 : ℕ)^2163*100000000000000^1651 ≤ 13098436016129^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119243727 10000000000 13098436016129 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2616796301/5000000000 : ℝ)^2163 ≤ (21407479125159/50000000000000 : ℝ)^1651 := by
    have hnat : (2616796301 : ℕ)^2163*50000000000000^1651 ≤ 21407479125159^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616796301 5000000000 21407479125159 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535182889/1000000000 : ℝ), (-2119243727/10000000000 : ℝ), (2616796301/5000000000 : ℝ)] ![(22043302858921/50000000000000 : ℝ), (13098436016129/100000000000000 : ℝ), (21407479125159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535182889/1000000000 : ℝ)|^2163 ≤ (22043302858921/50000000000000 : ℝ)^1651
        have hw : |(535182889/1000000000 : ℝ)|=(535182889/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2119243727/10000000000 : ℝ)|^2163 ≤ (13098436016129/100000000000000 : ℝ)^1651
        have hw : |(-2119243727/10000000000 : ℝ)|=(2119243727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2616796301/5000000000 : ℝ)|^2163 ≤ (21407479125159/50000000000000 : ℝ)^1651
        have hw : |(2616796301/5000000000 : ℝ)|=(2616796301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s3_2 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1070365779/2000000000 : ℝ)*x 0 + (654199093/1250000000 : ℝ)*x 1 + (-529810883/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070365779/2000000000 : ℝ)^2163 ≤ (44086605771803/100000000000000 : ℝ)^1651 := by
    have hnat : (1070365779 : ℕ)^2163*100000000000000^1651 ≤ 44086605771803^1651*2000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070365779 2000000000 44086605771803 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654199093/1250000000 : ℝ)^2163 ≤ (42814959772243/100000000000000 : ℝ)^1651 := by
    have hnat : (654199093 : ℕ)^2163*100000000000000^1651 ≤ 42814959772243^1651*1250000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654199093 1250000000 42814959772243 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529810883/2500000000 : ℝ)^2163 ≤ (13098434437127/100000000000000 : ℝ)^1651 := by
    have hnat : (529810883 : ℕ)^2163*100000000000000^1651 ≤ 13098434437127^1651*2500000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529810883 2500000000 13098434437127 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070365779/2000000000 : ℝ), (654199093/1250000000 : ℝ), (-529810883/2500000000 : ℝ)] ![(44086605771803/100000000000000 : ℝ), (42814959772243/100000000000000 : ℝ), (13098434437127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070365779/2000000000 : ℝ)|^2163 ≤ (44086605771803/100000000000000 : ℝ)^1651
        have hw : |(1070365779/2000000000 : ℝ)|=(1070365779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654199093/1250000000 : ℝ)|^2163 ≤ (42814959772243/100000000000000 : ℝ)^1651
        have hw : |(654199093/1250000000 : ℝ)|=(654199093/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-529810883/2500000000 : ℝ)|^2163 ≤ (13098434437127/100000000000000 : ℝ)^1651
        have hw : |(-529810883/2500000000 : ℝ)|=(529810883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s3_3 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (863891027/2000000000 : ℝ)*x 0 + (515296673/1250000000 : ℝ)*x 1 + (2262608873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863891027/2000000000 : ℝ)^2163 ≤ (3329430793103/10000000000000 : ℝ)^1651 := by
    have hnat : (863891027 : ℕ)^2163*10000000000000^1651 ≤ 3329430793103^1651*2000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863891027 2000000000 3329430793103 10000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515296673/1250000000 : ℝ)^2163 ≤ (31318337995273/100000000000000 : ℝ)^1651 := by
    have hnat : (515296673 : ℕ)^2163*100000000000000^1651 ≤ 31318337995273^1651*1250000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515296673 1250000000 31318337995273 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2262608873/5000000000 : ℝ)^2163 ≤ (35387354054543/100000000000000 : ℝ)^1651 := by
    have hnat : (2262608873 : ℕ)^2163*100000000000000^1651 ≤ 35387354054543^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262608873 5000000000 35387354054543 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863891027/2000000000 : ℝ), (515296673/1250000000 : ℝ), (2262608873/5000000000 : ℝ)] ![(3329430793103/10000000000000 : ℝ), (31318337995273/100000000000000 : ℝ), (35387354054543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863891027/2000000000 : ℝ)|^2163 ≤ (3329430793103/10000000000000 : ℝ)^1651
        have hw : |(863891027/2000000000 : ℝ)|=(863891027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(515296673/1250000000 : ℝ)|^2163 ≤ (31318337995273/100000000000000 : ℝ)^1651
        have hw : |(515296673/1250000000 : ℝ)|=(515296673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2262608873/5000000000 : ℝ)|^2163 ≤ (35387354054543/100000000000000 : ℝ)^1651
        have hw : |(2262608873/5000000000 : ℝ)|=(2262608873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s3_4 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-505476413/2500000000 : ℝ)*x 0 + (2617188183/5000000000 : ℝ)*x 1 + (1084681881/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (505476413/2500000000 : ℝ)^2163 ≤ (12315920214239/100000000000000 : ℝ)^1651 := by
    have hnat : (505476413 : ℕ)^2163*100000000000000^1651 ≤ 12315920214239^1651*2500000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505476413 2500000000 12315920214239 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2617188183/5000000000 : ℝ)^2163 ≤ (171293434639/400000000000 : ℝ)^1651 := by
    have hnat : (2617188183 : ℕ)^2163*400000000000^1651 ≤ 171293434639^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617188183 5000000000 171293434639 400000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084681881/2000000000 : ℝ)^2163 ≤ (8972144222883/20000000000000 : ℝ)^1651 := by
    have hnat : (1084681881 : ℕ)^2163*20000000000000^1651 ≤ 8972144222883^1651*2000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084681881 2000000000 8972144222883 20000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-505476413/2500000000 : ℝ), (2617188183/5000000000 : ℝ), (1084681881/2000000000 : ℝ)] ![(12315920214239/100000000000000 : ℝ), (171293434639/400000000000 : ℝ), (8972144222883/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-505476413/2500000000 : ℝ)|^2163 ≤ (12315920214239/100000000000000 : ℝ)^1651
        have hw : |(-505476413/2500000000 : ℝ)|=(505476413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2617188183/5000000000 : ℝ)|^2163 ≤ (171293434639/400000000000 : ℝ)^1651
        have hw : |(2617188183/5000000000 : ℝ)|=(2617188183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084681881/2000000000 : ℝ)|^2163 ≤ (8972144222883/20000000000000 : ℝ)^1651
        have hw : |(1084681881/2000000000 : ℝ)|=(1084681881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s3_5 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5302599481/10000000000 : ℝ)*x 0 + (-1929426827/10000000000 : ℝ)*x 1 + (5423409787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302599481/10000000000 : ℝ)^2163 ≤ (43556066720983/100000000000000 : ℝ)^1651 := by
    have hnat : (5302599481 : ℕ)^2163*100000000000000^1651 ≤ 43556066720983^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302599481 10000000000 43556066720983 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1929426827/10000000000 : ℝ)^2163 ≤ (2316641602311/20000000000000 : ℝ)^1651 := by
    have hnat : (1929426827 : ℕ)^2163*20000000000000^1651 ≤ 2316641602311^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929426827 10000000000 2316641602311 20000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423409787/10000000000 : ℝ)^2163 ≤ (22430362627047/50000000000000 : ℝ)^1651 := by
    have hnat : (5423409787 : ℕ)^2163*50000000000000^1651 ≤ 22430362627047^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423409787 10000000000 22430362627047 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302599481/10000000000 : ℝ), (-1929426827/10000000000 : ℝ), (5423409787/10000000000 : ℝ)] ![(43556066720983/100000000000000 : ℝ), (2316641602311/20000000000000 : ℝ), (22430362627047/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302599481/10000000000 : ℝ)|^2163 ≤ (43556066720983/100000000000000 : ℝ)^1651
        have hw : |(5302599481/10000000000 : ℝ)|=(5302599481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1929426827/10000000000 : ℝ)|^2163 ≤ (2316641602311/20000000000000 : ℝ)^1651
        have hw : |(-1929426827/10000000000 : ℝ)|=(1929426827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423409787/10000000000 : ℝ)|^2163 ≤ (22430362627047/50000000000000 : ℝ)^1651
        have hw : |(5423409787/10000000000 : ℝ)|=(5423409787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s3_6 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5302600217/10000000000 : ℝ)*x 0 + (5423409273/10000000000 : ℝ)*x 1 + (-60294579/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302600217/10000000000 : ℝ)^2163 ≤ (21778037320691/50000000000000 : ℝ)^1651 := by
    have hnat : (5302600217 : ℕ)^2163*50000000000000^1651 ≤ 21778037320691^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302600217 10000000000 21778037320691 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423409273/10000000000 : ℝ)^2163 ≤ (897214393679/2000000000000 : ℝ)^1651 := by
    have hnat : (5423409273 : ℕ)^2163*2000000000000^1651 ≤ 897214393679^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423409273 10000000000 897214393679 2000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (60294579/312500000 : ℝ)^2163 ≤ (11583205659859/100000000000000 : ℝ)^1651 := by
    have hnat : (60294579 : ℕ)^2163*100000000000000^1651 ≤ 11583205659859^1651*312500000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60294579 312500000 11583205659859 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302600217/10000000000 : ℝ), (5423409273/10000000000 : ℝ), (-60294579/312500000 : ℝ)] ![(21778037320691/50000000000000 : ℝ), (897214393679/2000000000000 : ℝ), (11583205659859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302600217/10000000000 : ℝ)|^2163 ≤ (21778037320691/50000000000000 : ℝ)^1651
        have hw : |(5302600217/10000000000 : ℝ)|=(5302600217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423409273/10000000000 : ℝ)|^2163 ≤ (897214393679/2000000000000 : ℝ)^1651
        have hw : |(5423409273/10000000000 : ℝ)|=(5423409273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-60294579/312500000 : ℝ)|^2163 ≤ (11583205659859/100000000000000 : ℝ)^1651
        have hw : |(-60294579/312500000 : ℝ)|=(60294579/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s3_7 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2159747043/5000000000 : ℝ)*x 0 + (2261780491/5000000000 : ℝ)*x 1 + (4124039031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159747043/5000000000 : ℝ)^2163 ≤ (16647350636229/50000000000000 : ℝ)^1651 := by
    have hnat : (2159747043 : ℕ)^2163*50000000000000^1651 ≤ 16647350636229^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159747043 5000000000 16647350636229 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2261780491/5000000000 : ℝ)^2163 ≤ (35370381232897/100000000000000 : ℝ)^1651 := by
    have hnat : (2261780491 : ℕ)^2163*100000000000000^1651 ≤ 35370381232897^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261780491 5000000000 35370381232897 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4124039031/10000000000 : ℝ)^2163 ≤ (31334917478897/100000000000000 : ℝ)^1651 := by
    have hnat : (4124039031 : ℕ)^2163*100000000000000^1651 ≤ 31334917478897^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124039031 10000000000 31334917478897 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2159747043/5000000000 : ℝ), (2261780491/5000000000 : ℝ), (4124039031/10000000000 : ℝ)] ![(16647350636229/50000000000000 : ℝ), (35370381232897/100000000000000 : ℝ), (31334917478897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2159747043/5000000000 : ℝ)|^2163 ≤ (16647350636229/50000000000000 : ℝ)^1651
        have hw : |(2159747043/5000000000 : ℝ)|=(2159747043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2261780491/5000000000 : ℝ)|^2163 ≤ (35370381232897/100000000000000 : ℝ)^1651
        have hw : |(2261780491/5000000000 : ℝ)|=(2261780491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4124039031/10000000000 : ℝ)|^2163 ≤ (31334917478897/100000000000000 : ℝ)^1651
        have hw : |(4124039031/10000000000 : ℝ)|=(4124039031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1366_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155675079/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4003/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2001/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5477/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3747/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4003/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2001/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4003/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2001/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4003/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2001/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4003/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2001/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4003/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2001/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4003/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2001/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2001/20000 : ℝ) ^ (4325/1024 : ℝ) ≤ (5988031944256223/100000000000000000000 : ℝ) := by
    have hpowers : (2001/20000 : ℝ)^4325 ≤ (5988031944256223/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2001 : ℕ)^4325*100000000000000000000^1024 ≤ 5988031944256223^1024*20000^4325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001 20000 5988031944256223 100000000000000000000 4325 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2001/20000 : ℝ)) (X := (5988031944256223/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4003/25000 : ℝ) ^ (4325/1024 : ℝ) ≤ (43638544169662603/100000000000000000000 : ℝ) := by
    have hpowers : (4003/25000 : ℝ)^4325 ≤ (43638544169662603/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4003 : ℕ)^4325*100000000000000000000^1024 ≤ 43638544169662603^1024*25000^4325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4003 25000 43638544169662603 100000000000000000000 4325 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4003/25000 : ℝ)) (X := (43638544169662603/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005988031944256223/50000000000000000000 : ℝ) ≤ (10000283535930279/10000000000000000 : ℝ) ^ (4325/1024 : ℝ) := by
    have hpowers : (50005988031944256223/50000000000000000000 : ℝ)^1024 ≤ (10000283535930279/10000000000000000 : ℝ)^4325 := by
      have hnat : (50005988031944256223 : ℕ)^1024*10000000000000000^4325 ≤ 10000283535930279^4325*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005988031944256223 50000000000000000000 10000283535930279 10000000000000000 1024 4325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283535930279/10000000000000000 : ℝ)) (X := (50005988031944256223/50000000000000000000 : ℝ)) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024813288056959413/50000000000000000000 : ℝ) ≤ (10001174751276161/10000000000000000 : ℝ) ^ (4325/1024 : ℝ) := by
    have hpowers : (50024813288056959413/50000000000000000000 : ℝ)^1024 ≤ (10001174751276161/10000000000000000 : ℝ)^4325 := by
      have hnat : (50024813288056959413 : ℕ)^1024*10000000000000000^4325 ≤ 10001174751276161^4325*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024813288056959413 50000000000000000000 10001174751276161 10000000000000000 1024 4325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001174751276161/10000000000000000 : ℝ)) (X := (50024813288056959413/50000000000000000000 : ℝ)) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50043638544169662603/50000000000000000000 : ℝ) ≤ (10002065966622043/10000000000000000 : ℝ) ^ (4325/1024 : ℝ) := by
    have hpowers : (50043638544169662603/50000000000000000000 : ℝ)^1024 ≤ (10002065966622043/10000000000000000 : ℝ)^4325 := by
      have hnat : (50043638544169662603 : ℕ)^1024*10000000000000000^4325 ≤ 10002065966622043^4325*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50043638544169662603 50000000000000000000 10002065966622043 10000000000000000 1024 4325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002065966622043/10000000000000000 : ℝ)) (X := (50043638544169662603/50000000000000000000 : ℝ)) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5988031944256223/100000000000000000000 : ℝ) ≤ ((60053869981262087133/60070000000000000000 : ℝ)+2*(445607672941/300350000000000 : ℝ)*(2001/20000 : ℝ))^(4325/1024 : ℝ) := by
    rw [show (60053869981262087133/60070000000000000000 : ℝ)+2*(445607672941/300350000000000 : ℝ)*(2001/20000 : ℝ)=(10000283535930279/10000000000000000 : ℝ) by norm_num, show 1+2*(5988031944256223/100000000000000000000 : ℝ)=(50005988031944256223/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(43638544169662603/100000000000000000000 : ℝ)+(5988031944256223/100000000000000000000 : ℝ) ≤ ((60053869981262087133/60070000000000000000 : ℝ)+(445607672941/300350000000000 : ℝ)*((4003/25000 : ℝ)+(2001/20000 : ℝ)))^(4325/1024 : ℝ) := by
    rw [show (60053869981262087133/60070000000000000000 : ℝ)+(445607672941/300350000000000 : ℝ)*((4003/25000 : ℝ)+(2001/20000 : ℝ))=(10001174751276161/10000000000000000 : ℝ) by norm_num, show 1+(43638544169662603/100000000000000000000 : ℝ)+(5988031944256223/100000000000000000000 : ℝ)=(50024813288056959413/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(43638544169662603/100000000000000000000 : ℝ) ≤ ((60053869981262087133/60070000000000000000 : ℝ)+2*(445607672941/300350000000000 : ℝ)*(4003/25000 : ℝ))^(4325/1024 : ℝ) := by
    rw [show (60053869981262087133/60070000000000000000 : ℝ)+2*(445607672941/300350000000000 : ℝ)*(4003/25000 : ℝ)=(10002065966622043/10000000000000000 : ℝ) by norm_num, show 1+2*(43638544169662603/100000000000000000000 : ℝ)=(50043638544169662603/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (60053869981262087133/60070000000000000000 : ℝ)*(X 1 0+X 2 0)+(445607672941/300350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4325/1024 : ℝ)) (lo := (2001/20000 : ℝ)) (hi := (4003/25000 : ℝ)) (c := (60053869981262087133/60070000000000000000 : ℝ)) (alpha := (445607672941/300350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (60053869981262087133/60070000000000000000 : ℝ)*(X 0 1+X 2 1)+(445607672941/300350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4325/1024 : ℝ)) (lo := (2001/20000 : ℝ)) (hi := (4003/25000 : ℝ)) (c := (60053869981262087133/60070000000000000000 : ℝ)) (alpha := (445607672941/300350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (60053869981262087133/60070000000000000000 : ℝ)*(X 0 2+X 1 2)+(445607672941/300350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4325/1024 : ℝ)) (lo := (2001/20000 : ℝ)) (hi := (4003/25000 : ℝ)) (c := (60053869981262087133/60070000000000000000 : ℝ)) (alpha := (445607672941/300350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2021887521/10000000000 : ℝ)*X 0 0+(1356049453/2500000000 : ℝ)*X 0 1+(52335927/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535182889/1000000000 : ℝ)*X 1 0+(-2119243727/10000000000 : ℝ)*X 1 1+(2616796301/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070365779/2000000000 : ℝ)*X 2 0+(654199093/1250000000 : ℝ)*X 2 1+(-529810883/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((863891027/2000000000 : ℝ)*X 0 0+(515296673/1250000000 : ℝ)*X 0 1+(2262608873/5000000000 : ℝ)*X 0 2+(863891027/2000000000 : ℝ)*X 1 0+(515296673/1250000000 : ℝ)*X 1 1+(2262608873/5000000000 : ℝ)*X 1 2+(863891027/2000000000 : ℝ)*X 2 0+(515296673/1250000000 : ℝ)*X 2 1+(2262608873/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-505476413/2500000000 : ℝ)*X 0 0+(2617188183/5000000000 : ℝ)*X 0 1+(1084681881/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302599481/10000000000 : ℝ)*X 1 0+(-1929426827/10000000000 : ℝ)*X 1 1+(5423409787/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302600217/10000000000 : ℝ)*X 2 0+(5423409273/10000000000 : ℝ)*X 2 1+(-60294579/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2159747043/5000000000 : ℝ)*X 0 0+(2261780491/5000000000 : ℝ)*X 0 1+(4124039031/10000000000 : ℝ)*X 0 2+(2159747043/5000000000 : ℝ)*X 1 0+(2261780491/5000000000 : ℝ)*X 1 1+(4124039031/10000000000 : ℝ)*X 1 2+(2159747043/5000000000 : ℝ)*X 2 0+(2261780491/5000000000 : ℝ)*X 2 1+(4124039031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7402262752333915395153742659/1501750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1061093009/100000000000000 : ℝ)*(base19) + (529871699/50000000000000 : ℝ)*(base23) + (422679/10000000000000 : ℝ)*(lower2) + (201819837/100000000000000 : ℝ)*(upper5) + (1932214768195259/50000000000000 : ℝ)*(major0) + (1932214768195259/50000000000000 : ℝ)*(major1) + (1932214768195259/50000000000000 : ℝ)*(major2) + (1049293205648893/20000000000000 : ℝ)*(sp0) + (5246488903114467/100000000000000 : ℝ)*(sp1) + (104929781669483/2000000000000 : ℝ)*(sp2) + (1241179877507269/50000000000000 : ℝ)*(sp3) + (24114973083/100000000000000 : ℝ)*(sp4) + (22376259/12500000000000 : ℝ)*(sp5) + (563140369/6250000000000 : ℝ)*(sp7) + (1241184382630221/50000000000000 : ℝ)*(f.failure) + (1311622535804387/25000000000000 : ℝ)*(f.sum) + (115255592792879/30035000000000000000000000000 : ℝ)*base66 + (12866482012886302447/3003500000000000000000000000000000 : ℝ)*base67 + (1472467894845197553/3003500000000000000000000000000000 : ℝ)*base70 + (16182046518866697553/3003500000000000000000000000000000 : ℝ)*base72 + (89431027462469/30035000000000000000000000000 : ℝ)*base74 + (27951930517764302447/3003500000000000000000000000000000 : ℝ)*base75 + (6022708877175302447/3003500000000000000000000000000000 : ℝ)*base77 + (6510773734639302447/3003500000000000000000000000000000 : ℝ)*base79 + (7587371368357/3754375000000000000000000000 : ℝ)*base81 + (18037541/5000000000000000000000 : ℝ)*base90 + (18037541/5000000000000000000000 : ℝ)*base92 + (18037541/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (260875191818461462988496849/75087500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (212464051/20000000000000 : ℝ)*(base19) + (2253589179/100000000000000 : ℝ)*(base23) + (260120521/100000000000000 : ℝ)*(upper3) + (30430919/20000000000000 : ℝ)*(lower4) + (20136491/10000000000000 : ℝ)*(upper5) + (97413441752949/2500000000000 : ℝ)*(major0) + (97413441752949/2500000000000 : ℝ)*(major1) + (97413441752949/2500000000000 : ℝ)*(major2) + (22555441167/100000000000000 : ℝ)*(sp1) + (2043695801/5000000000000 : ℝ)*(sp2) + (5290081363657067/100000000000000 : ℝ)*(sp4) + (1058011549179129/20000000000000 : ℝ)*(sp5) + (5290038236151869/100000000000000 : ℝ)*(sp6) + (250299386076943/10000000000000 : ℝ)*(sp7) + (250299386076943/10000000000000 : ℝ)*(f.failure) + (5290081363657067/100000000000000 : ℝ)*(f.sum) + (308521929259/750875000000000000000000000 : ℝ)*base65 + (305838094912655217/150175000000000000000000000000000 : ℝ)*base67 + (136924456193130217/150175000000000000000000000000000 : ℝ)*base69 + (1365652042724880217/150175000000000000000000000000000 : ℝ)*base71 + (7524024196227/1501750000000000000000000000 : ℝ)*base74 + (504113902484319783/150175000000000000000000000000000 : ℝ)*base76 + (757924365729769783/150175000000000000000000000000000 : ℝ)*base78 + (534920807383530217/150175000000000000000000000000000 : ℝ)*base79 + (5651467755931/3003500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1603497/1000000000000000000000 : ℝ)*base89 + (1603497/1000000000000000000000 : ℝ)*base91 + (1603497/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1366_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155675079/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4003/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2001/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5477/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3747/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1366_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1366_s4_0 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-202316751/1000000000 : ℝ)*x 0 + (5413625527/10000000000 : ℝ)*x 1 + (5243323741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (202316751/1000000000 : ℝ)^2163 ≤ (12325991106059/100000000000000 : ℝ)^1651 := by
    have hnat : (202316751 : ℕ)^2163*100000000000000^1651 ≤ 12325991106059^1651*1000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202316751 1000000000 12325991106059 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413625527/10000000000 : ℝ)^2163 ≤ (5594340538373/12500000000000 : ℝ)^1651 := by
    have hnat : (5413625527 : ℕ)^2163*12500000000000^1651 ≤ 5594340538373^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413625527 10000000000 5594340538373 12500000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243323741/10000000000 : ℝ)^2163 ≤ (10729821141673/25000000000000 : ℝ)^1651 := by
    have hnat : (5243323741 : ℕ)^2163*25000000000000^1651 ≤ 10729821141673^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243323741 10000000000 10729821141673 25000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-202316751/1000000000 : ℝ), (5413625527/10000000000 : ℝ), (5243323741/10000000000 : ℝ)] ![(12325991106059/100000000000000 : ℝ), (5594340538373/12500000000000 : ℝ), (10729821141673/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-202316751/1000000000 : ℝ)|^2163 ≤ (12325991106059/100000000000000 : ℝ)^1651
        have hw : |(-202316751/1000000000 : ℝ)|=(202316751/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413625527/10000000000 : ℝ)|^2163 ≤ (5594340538373/12500000000000 : ℝ)^1651
        have hw : |(5413625527/10000000000 : ℝ)|=(5413625527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243323741/10000000000 : ℝ)|^2163 ≤ (10729821141673/25000000000000 : ℝ)^1651
        have hw : |(5243323741/10000000000 : ℝ)|=(5243323741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s4_1 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069824831/2000000000 : ℝ)*x 0 + (-1054979001/5000000000 : ℝ)*x 1 + (2621661927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069824831/2000000000 : ℝ)^2163 ≤ (44057417702053/100000000000000 : ℝ)^1651 := by
    have hnat : (1069824831 : ℕ)^2163*100000000000000^1651 ≤ 44057417702053^1651*2000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069824831 2000000000 44057417702053 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054979001/5000000000 : ℝ)^2163 ≤ (1302329650917/10000000000000 : ℝ)^1651 := by
    have hnat : (1054979001 : ℕ)^2163*10000000000000^1651 ≤ 1302329650917^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054979001 5000000000 1302329650917 10000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621661927/5000000000 : ℝ)^2163 ≤ (85838571557/200000000000 : ℝ)^1651 := by
    have hnat : (2621661927 : ℕ)^2163*200000000000^1651 ≤ 85838571557^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621661927 5000000000 85838571557 200000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069824831/2000000000 : ℝ), (-1054979001/5000000000 : ℝ), (2621661927/5000000000 : ℝ)] ![(44057417702053/100000000000000 : ℝ), (1302329650917/10000000000000 : ℝ), (85838571557/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069824831/2000000000 : ℝ)|^2163 ≤ (44057417702053/100000000000000 : ℝ)^1651
        have hw : |(1069824831/2000000000 : ℝ)|=(1069824831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1054979001/5000000000 : ℝ)|^2163 ≤ (1302329650917/10000000000000 : ℝ)^1651
        have hw : |(-1054979001/5000000000 : ℝ)|=(1054979001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621661927/5000000000 : ℝ)|^2163 ≤ (85838571557/200000000000 : ℝ)^1651
        have hw : |(2621661927/5000000000 : ℝ)|=(2621661927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s4_2 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337281027/2500000000 : ℝ)*x 0 + (5243323779/10000000000 : ℝ)*x 1 + (-527489541/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337281027/2500000000 : ℝ)^2163 ≤ (22028708597447/50000000000000 : ℝ)^1651 := by
    have hnat : (1337281027 : ℕ)^2163*50000000000000^1651 ≤ 22028708597447^1651*2500000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337281027 2500000000 22028708597447 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243323779/10000000000 : ℝ)^2163 ≤ (42919284974203/100000000000000 : ℝ)^1651 := by
    have hnat : (5243323779 : ℕ)^2163*100000000000000^1651 ≤ 42919284974203^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243323779 10000000000 42919284974203 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527489541/2500000000 : ℝ)^2163 ≤ (13023297819171/100000000000000 : ℝ)^1651 := by
    have hnat : (527489541 : ℕ)^2163*100000000000000^1651 ≤ 13023297819171^1651*2500000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527489541 2500000000 13023297819171 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337281027/2500000000 : ℝ), (5243323779/10000000000 : ℝ), (-527489541/2500000000 : ℝ)] ![(22028708597447/50000000000000 : ℝ), (42919284974203/100000000000000 : ℝ), (13023297819171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337281027/2500000000 : ℝ)|^2163 ≤ (22028708597447/50000000000000 : ℝ)^1651
        have hw : |(1337281027/2500000000 : ℝ)|=(1337281027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243323779/10000000000 : ℝ)|^2163 ≤ (42919284974203/100000000000000 : ℝ)^1651
        have hw : |(5243323779/10000000000 : ℝ)|=(5243323779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-527489541/2500000000 : ℝ)|^2163 ≤ (13023297819171/100000000000000 : ℝ)^1651
        have hw : |(-527489541/2500000000 : ℝ)|=(527489541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s4_3 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2160117177/5000000000 : ℝ)*x 0 + (2071866509/5000000000 : ℝ)*x 1 + (1125916551/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160117177/5000000000 : ℝ)^2163 ≤ (16651088489127/50000000000000 : ℝ)^1651 := by
    have hnat : (2160117177 : ℕ)^2163*50000000000000^1651 ≤ 16651088489127^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160117177 5000000000 16651088489127 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2071866509/5000000000 : ℝ)^2163 ≤ (15765552186009/50000000000000 : ℝ)^1651 := by
    have hnat : (2071866509 : ℕ)^2163*50000000000000^1651 ≤ 15765552186009^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071866509 5000000000 15765552186009 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125916551/2500000000 : ℝ)^2163 ≤ (35166718640691/100000000000000 : ℝ)^1651 := by
    have hnat : (1125916551 : ℕ)^2163*100000000000000^1651 ≤ 35166718640691^1651*2500000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125916551 2500000000 35166718640691 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2160117177/5000000000 : ℝ), (2071866509/5000000000 : ℝ), (1125916551/2500000000 : ℝ)] ![(16651088489127/50000000000000 : ℝ), (15765552186009/50000000000000 : ℝ), (35166718640691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2160117177/5000000000 : ℝ)|^2163 ≤ (16651088489127/50000000000000 : ℝ)^1651
        have hw : |(2160117177/5000000000 : ℝ)|=(2160117177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2071866509/5000000000 : ℝ)|^2163 ≤ (15765552186009/50000000000000 : ℝ)^1651
        have hw : |(2071866509/5000000000 : ℝ)|=(2071866509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125916551/2500000000 : ℝ)|^2163 ≤ (35166718640691/100000000000000 : ℝ)^1651
        have hw : |(1125916551/2500000000 : ℝ)|=(1125916551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s4_4 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2023180287/10000000000 : ℝ)*x 0 + (5243949809/10000000000 : ℝ)*x 1 + (1353249049/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2023180287/10000000000 : ℝ)^2163 ≤ (12326093089291/100000000000000 : ℝ)^1651 := by
    have hnat : (2023180287 : ℕ)^2163*100000000000000^1651 ≤ 12326093089291^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023180287 10000000000 12326093089291 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243949809/10000000000 : ℝ)^2163 ≤ (4292599862013/10000000000000 : ℝ)^1651 := by
    have hnat : (5243949809 : ℕ)^2163*10000000000000^1651 ≤ 4292599862013^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243949809 10000000000 4292599862013 10000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353249049/2500000000 : ℝ)^2163 ≤ (22373954139087/50000000000000 : ℝ)^1651 := by
    have hnat : (1353249049 : ℕ)^2163*50000000000000^1651 ≤ 22373954139087^1651*2500000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353249049 2500000000 22373954139087 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2023180287/10000000000 : ℝ), (5243949809/10000000000 : ℝ), (1353249049/2500000000 : ℝ)] ![(12326093089291/100000000000000 : ℝ), (4292599862013/10000000000000 : ℝ), (22373954139087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2023180287/10000000000 : ℝ)|^2163 ≤ (12326093089291/100000000000000 : ℝ)^1651
        have hw : |(-2023180287/10000000000 : ℝ)|=(2023180287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243949809/10000000000 : ℝ)|^2163 ≤ (4292599862013/10000000000000 : ℝ)^1651
        have hw : |(5243949809/10000000000 : ℝ)|=(5243949809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353249049/2500000000 : ℝ)|^2163 ≤ (22373954139087/50000000000000 : ℝ)^1651
        have hw : |(1353249049/2500000000 : ℝ)|=(1353249049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s4_5 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305139583/10000000000 : ℝ)*x 0 + (-485071449/2500000000 : ℝ)*x 1 + (5412995957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305139583/10000000000 : ℝ)^2163 ≤ (21791701918171/50000000000000 : ℝ)^1651 := by
    have hnat : (5305139583 : ℕ)^2163*50000000000000^1651 ≤ 21791701918171^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305139583 10000000000 21791701918171 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (485071449/2500000000 : ℝ)^2163 ≤ (1166869045479/10000000000000 : ℝ)^1651 := by
    have hnat : (485071449 : ℕ)^2163*10000000000000^1651 ≤ 1166869045479^1651*2500000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485071449 2500000000 1166869045479 10000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412995957/10000000000 : ℝ)^2163 ≤ (11186976422427/25000000000000 : ℝ)^1651 := by
    have hnat : (5412995957 : ℕ)^2163*25000000000000^1651 ≤ 11186976422427^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412995957 10000000000 11186976422427 25000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305139583/10000000000 : ℝ), (-485071449/2500000000 : ℝ), (5412995957/10000000000 : ℝ)] ![(21791701918171/50000000000000 : ℝ), (1166869045479/10000000000000 : ℝ), (11186976422427/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305139583/10000000000 : ℝ)|^2163 ≤ (21791701918171/50000000000000 : ℝ)^1651
        have hw : |(5305139583/10000000000 : ℝ)|=(5305139583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-485071449/2500000000 : ℝ)|^2163 ≤ (1166869045479/10000000000000 : ℝ)^1651
        have hw : |(-485071449/2500000000 : ℝ)|=(485071449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412995957/10000000000 : ℝ)|^2163 ≤ (11186976422427/25000000000000 : ℝ)^1651
        have hw : |(5412995957/10000000000 : ℝ)|=(5412995957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s4_6 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326284889/2500000000 : ℝ)*x 0 + (2706498039/5000000000 : ℝ)*x 1 + (-485071417/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326284889/2500000000 : ℝ)^2163 ≤ (43583403545741/100000000000000 : ℝ)^1651 := by
    have hnat : (1326284889 : ℕ)^2163*100000000000000^1651 ≤ 43583403545741^1651*2500000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326284889 2500000000 43583403545741 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706498039/5000000000 : ℝ)^2163 ≤ (44747907000187/100000000000000 : ℝ)^1651 := by
    have hnat : (2706498039 : ℕ)^2163*100000000000000^1651 ≤ 44747907000187^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706498039 5000000000 44747907000187 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (485071417/2500000000 : ℝ)^2163 ≤ (1166868944629/10000000000000 : ℝ)^1651 := by
    have hnat : (485071417 : ℕ)^2163*10000000000000^1651 ≤ 1166868944629^1651*2500000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485071417 2500000000 1166868944629 10000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326284889/2500000000 : ℝ), (2706498039/5000000000 : ℝ), (-485071417/2500000000 : ℝ)] ![(43583403545741/100000000000000 : ℝ), (44747907000187/100000000000000 : ℝ), (1166868944629/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326284889/2500000000 : ℝ)|^2163 ≤ (43583403545741/100000000000000 : ℝ)^1651
        have hw : |(1326284889/2500000000 : ℝ)|=(1326284889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706498039/5000000000 : ℝ)|^2163 ≤ (44747907000187/100000000000000 : ℝ)^1651
        have hw : |(2706498039/5000000000 : ℝ)|=(2706498039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-485071417/2500000000 : ℝ)|^2163 ≤ (1166868944629/10000000000000 : ℝ)^1651
        have hw : |(-485071417/2500000000 : ℝ)|=(485071417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s4_7 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4320260761/10000000000 : ℝ)*x 0 + (4502343521/10000000000 : ℝ)*x 1 + (2072531717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320260761/10000000000 : ℝ)^2163 ≤ (4162805457573/12500000000000 : ℝ)^1651 := by
    have hnat : (4320260761 : ℕ)^2163*12500000000000^1651 ≤ 4162805457573^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320260761 10000000000 4162805457573 12500000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502343521/10000000000 : ℝ)^2163 ≤ (2197074264157/6250000000000 : ℝ)^1651 := by
    have hnat : (4502343521 : ℕ)^2163*6250000000000^1651 ≤ 2197074264157^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502343521 10000000000 2197074264157 6250000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072531717/5000000000 : ℝ)^2163 ≤ (31544368110191/100000000000000 : ℝ)^1651 := by
    have hnat : (2072531717 : ℕ)^2163*100000000000000^1651 ≤ 31544368110191^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072531717 5000000000 31544368110191 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320260761/10000000000 : ℝ), (4502343521/10000000000 : ℝ), (2072531717/5000000000 : ℝ)] ![(4162805457573/12500000000000 : ℝ), (2197074264157/6250000000000 : ℝ), (31544368110191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320260761/10000000000 : ℝ)|^2163 ≤ (4162805457573/12500000000000 : ℝ)^1651
        have hw : |(4320260761/10000000000 : ℝ)|=(4320260761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4502343521/10000000000 : ℝ)|^2163 ≤ (2197074264157/6250000000000 : ℝ)^1651
        have hw : |(4502343521/10000000000 : ℝ)|=(4502343521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2072531717/5000000000 : ℝ)|^2163 ≤ (31544368110191/100000000000000 : ℝ)^1651
        have hw : |(2072531717/5000000000 : ℝ)|=(2072531717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1366_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155675079/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3747/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5477/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5581/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14767/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3747/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5477/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3747/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5477/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3747/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5477/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3747/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5477/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3747/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5477/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3747/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5477/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5477/50000 : ℝ) ^ (4325/1024 : ℝ) ≤ (439013525530017/5000000000000000000 : ℝ) := by
    have hpowers : (5477/50000 : ℝ)^4325 ≤ (439013525530017/5000000000000000000 : ℝ)^1024 := by
      have hnat : (5477 : ℕ)^4325*5000000000000000000^1024 ≤ 439013525530017^1024*50000^4325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5477 50000 439013525530017 5000000000000000000 4325 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5477/50000 : ℝ)) (X := (439013525530017/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3747/25000 : ℝ) ^ (4325/1024 : ℝ) ≤ (1650494129442469/5000000000000000000 : ℝ) := by
    have hpowers : (3747/25000 : ℝ)^4325 ≤ (1650494129442469/5000000000000000000 : ℝ)^1024 := by
      have hnat : (3747 : ℕ)^4325*5000000000000000000^1024 ≤ 1650494129442469^1024*25000^4325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3747 25000 1650494129442469 5000000000000000000 4325 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3747/25000 : ℝ)) (X := (1650494129442469/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500439013525530017/2500000000000000000 : ℝ) ≤ (10000415740787973/10000000000000000 : ℝ) ^ (4325/1024 : ℝ) := by
    have hpowers : (2500439013525530017/2500000000000000000 : ℝ)^1024 ≤ (10000415740787973/10000000000000000 : ℝ)^4325 := by
      have hnat : (2500439013525530017 : ℕ)^1024*10000000000000000^4325 ≤ 10000415740787973^4325*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500439013525530017 2500000000000000000 10000415740787973 10000000000000000 1024 4325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000415740787973/10000000000000000 : ℝ)) (X := (2500439013525530017/2500000000000000000 : ℝ)) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2501044753827486243/2500000000000000000 : ℝ) ≤ (10000989278470477/10000000000000000 : ℝ) ^ (4325/1024 : ℝ) := by
    have hpowers : (2501044753827486243/2500000000000000000 : ℝ)^1024 ≤ (10000989278470477/10000000000000000 : ℝ)^4325 := by
      have hnat : (2501044753827486243 : ℕ)^1024*10000000000000000^4325 ≤ 10000989278470477^4325*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501044753827486243 2500000000000000000 10000989278470477 10000000000000000 1024 4325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000989278470477/10000000000000000 : ℝ)) (X := (2501044753827486243/2500000000000000000 : ℝ)) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501650494129442469/2500000000000000000 : ℝ) ≤ (10001562816152981/10000000000000000 : ℝ) ^ (4325/1024 : ℝ) := by
    have hpowers : (2501650494129442469/2500000000000000000 : ℝ)^1024 ≤ (10001562816152981/10000000000000000 : ℝ)^4325 := by
      have hnat : (2501650494129442469 : ℕ)^1024*10000000000000000^4325 ≤ 10001562816152981^4325*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501650494129442469 2500000000000000000 10001562816152981 10000000000000000 1024 4325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001562816152981/10000000000000000 : ℝ)) (X := (2501650494129442469/2500000000000000000 : ℝ)) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(439013525530017/5000000000000000000 : ℝ) ≤ ((806582240695807709/806800000000000000 : ℝ)+2*(71692210313/50425000000000 : ℝ)*(5477/50000 : ℝ))^(4325/1024 : ℝ) := by
    rw [show (806582240695807709/806800000000000000 : ℝ)+2*(71692210313/50425000000000 : ℝ)*(5477/50000 : ℝ)=(10000415740787973/10000000000000000 : ℝ) by norm_num, show 1+2*(439013525530017/5000000000000000000 : ℝ)=(2500439013525530017/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1650494129442469/5000000000000000000 : ℝ)+(439013525530017/5000000000000000000 : ℝ) ≤ ((806582240695807709/806800000000000000 : ℝ)+(71692210313/50425000000000 : ℝ)*((3747/25000 : ℝ)+(5477/50000 : ℝ)))^(4325/1024 : ℝ) := by
    rw [show (806582240695807709/806800000000000000 : ℝ)+(71692210313/50425000000000 : ℝ)*((3747/25000 : ℝ)+(5477/50000 : ℝ))=(10000989278470477/10000000000000000 : ℝ) by norm_num, show 1+(1650494129442469/5000000000000000000 : ℝ)+(439013525530017/5000000000000000000 : ℝ)=(2501044753827486243/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1650494129442469/5000000000000000000 : ℝ) ≤ ((806582240695807709/806800000000000000 : ℝ)+2*(71692210313/50425000000000 : ℝ)*(3747/25000 : ℝ))^(4325/1024 : ℝ) := by
    rw [show (806582240695807709/806800000000000000 : ℝ)+2*(71692210313/50425000000000 : ℝ)*(3747/25000 : ℝ)=(10001562816152981/10000000000000000 : ℝ) by norm_num, show 1+2*(1650494129442469/5000000000000000000 : ℝ)=(2501650494129442469/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (806582240695807709/806800000000000000 : ℝ)*(X 1 0+X 2 0)+(71692210313/50425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4325/1024 : ℝ)) (lo := (5477/50000 : ℝ)) (hi := (3747/25000 : ℝ)) (c := (806582240695807709/806800000000000000 : ℝ)) (alpha := (71692210313/50425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (806582240695807709/806800000000000000 : ℝ)*(X 0 1+X 2 1)+(71692210313/50425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4325/1024 : ℝ)) (lo := (5477/50000 : ℝ)) (hi := (3747/25000 : ℝ)) (c := (806582240695807709/806800000000000000 : ℝ)) (alpha := (71692210313/50425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (806582240695807709/806800000000000000 : ℝ)*(X 0 2+X 1 2)+(71692210313/50425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4325/1024 : ℝ)) (lo := (5477/50000 : ℝ)) (hi := (3747/25000 : ℝ)) (c := (806582240695807709/806800000000000000 : ℝ)) (alpha := (71692210313/50425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-202316751/1000000000 : ℝ)*X 0 0+(5413625527/10000000000 : ℝ)*X 0 1+(5243323741/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069824831/2000000000 : ℝ)*X 1 0+(-1054979001/5000000000 : ℝ)*X 1 1+(2621661927/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337281027/2500000000 : ℝ)*X 2 0+(5243323779/10000000000 : ℝ)*X 2 1+(-527489541/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2160117177/5000000000 : ℝ)*X 0 0+(2071866509/5000000000 : ℝ)*X 0 1+(1125916551/2500000000 : ℝ)*X 0 2+(2160117177/5000000000 : ℝ)*X 1 0+(2071866509/5000000000 : ℝ)*X 1 1+(1125916551/2500000000 : ℝ)*X 1 2+(2160117177/5000000000 : ℝ)*X 2 0+(2071866509/5000000000 : ℝ)*X 2 1+(1125916551/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2023180287/10000000000 : ℝ)*X 0 0+(5243949809/10000000000 : ℝ)*X 0 1+(1353249049/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305139583/10000000000 : ℝ)*X 1 0+(-485071449/2500000000 : ℝ)*X 1 1+(5412995957/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326284889/2500000000 : ℝ)*X 2 0+(2706498039/5000000000 : ℝ)*X 2 1+(-485071417/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4320260761/10000000000 : ℝ)*X 0 0+(4502343521/10000000000 : ℝ)*X 0 1+(2072531717/5000000000 : ℝ)*X 0 2+(4320260761/10000000000 : ℝ)*X 1 0+(4502343521/10000000000 : ℝ)*X 1 1+(2072531717/5000000000 : ℝ)*X 1 2+(4320260761/10000000000 : ℝ)*X 2 0+(4502343521/10000000000 : ℝ)*X 2 1+(2072531717/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52743314120321466813323889/20170000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (833222849/100000000000000 : ℝ)*(base19) + (357794519/50000000000000 : ℝ)*(base23) + (44297101/100000000000000 : ℝ)*(lower2) + (7942657/3125000000000 : ℝ)*(upper3) + (560721/6250000000000 : ℝ)*(lower4) + (2162568172434669/50000000000000 : ℝ)*(major0) + (2162568172434669/50000000000000 : ℝ)*(major1) + (2162568172434669/50000000000000 : ℝ)*(major2) + (733993784470379/12500000000000 : ℝ)*(sp0) + (1174392346482487/20000000000000 : ℝ)*(sp1) + (2935980925023123/50000000000000 : ℝ)*(sp2) + (1389149911563639/50000000000000 : ℝ)*(sp3) + (3072468063/25000000000000 : ℝ)*(sp4) + (10213811479/100000000000000 : ℝ)*(sp7) + (694577509234689/25000000000000 : ℝ)*(f.failure) + (1467990641408821/25000000000000 : ℝ)*(f.sum) + (6937366691781/10085000000000000000000000000 : ℝ)*base65 + (661785767648884679/40340000000000000000000000000000 : ℝ)*base68 + (739856068447264679/40340000000000000000000000000000 : ℝ)*base70 + (343817459049624679/40340000000000000000000000000000 : ℝ)*base72 + (20842677552729/10085000000000000000000000000 : ℝ)*base74 + (71181373538504679/40340000000000000000000000000000 : ℝ)*base76 + (461312999358244679/40340000000000000000000000000000 : ℝ)*base78 + (901952616135564679/40340000000000000000000000000000 : ℝ)*base80 + (27074858422707/5042500000000000000000000000 : ℝ)*base82 + (10384569/2500000000000000000000 : ℝ)*base90 + (10384569/2500000000000000000000 : ℝ)*base92 + (10384569/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (192040425749705875952224989/40340000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (175892613/20000000000000 : ℝ)*(base19) + (559403231/50000000000000 : ℝ)*(base23) + (793303/800000000000 : ℝ)*(upper2) + (75822231/100000000000000 : ℝ)*(upper3) + (18020733/100000000000000 : ℝ)*(upper5) + (4357228456955769/100000000000000 : ℝ)*(major0) + (4357228456955769/100000000000000 : ℝ)*(major1) + (4357228456955769/100000000000000 : ℝ)*(major2) + (2743624561/25000000000000 : ℝ)*(sp1) + (10464461667/50000000000000 : ℝ)*(sp2) + (591553191449749/10000000000000 : ℝ)*(sp4) + (5915520060536181/100000000000000 : ℝ)*(sp5) + (2957754933383847/50000000000000 : ℝ)*(sp6) + (349865605091147/12500000000000 : ℝ)*(sp7) + (349865605091147/12500000000000 : ℝ)*(f.failure) + (591553191449749/10000000000000 : ℝ)*(f.sum) + (118564779111/5042500000000000000000000000 : ℝ)*base66 + (1025510708118704779/80680000000000000000000000000000 : ℝ)*base68 + (598935403774944779/80680000000000000000000000000000 : ℝ)*base70 + (790727968756344779/80680000000000000000000000000000 : ℝ)*base72 + (100805777929/1260625000000000000000000000 : ℝ)*base74 + (665898557510984779/80680000000000000000000000000000 : ℝ)*base76 + (603002034639584779/80680000000000000000000000000000 : ℝ)*base78 + (151970913816144779/80680000000000000000000000000000 : ℝ)*base80 + (1208616162143/2521250000000000000000000000 : ℝ)*base82 + (1074387/1250000000000000000000 : ℝ)*base90 + (1074387/1250000000000000000000 : ℝ)*base92 + (1074387/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1366_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155675079/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3747/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5477/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5581/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1366_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1366_s5_0 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-50584481/250000000 : ℝ)*x 0 + (676472581/1250000000 : ℝ)*x 1 + (2622514611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50584481/250000000 : ℝ)^2163 ≤ (12327681114597/100000000000000 : ℝ)^1651 := by
    have hnat : (50584481 : ℕ)^2163*100000000000000^1651 ≤ 12327681114597^1651*250000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50584481 250000000 12327681114597 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676472581/1250000000 : ℝ)^2163 ≤ (8946948773309/20000000000000 : ℝ)^1651 := by
    have hnat : (676472581 : ℕ)^2163*20000000000000^1651 ≤ 8946948773309^1651*1250000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676472581 1250000000 8946948773309 20000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622514611/5000000000 : ℝ)^2163 ≤ (21468787500833/50000000000000 : ℝ)^1651 := by
    have hnat : (2622514611 : ℕ)^2163*50000000000000^1651 ≤ 21468787500833^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622514611 5000000000 21468787500833 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-50584481/250000000 : ℝ), (676472581/1250000000 : ℝ), (2622514611/5000000000 : ℝ)] ![(12327681114597/100000000000000 : ℝ), (8946948773309/20000000000000 : ℝ), (21468787500833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-50584481/250000000 : ℝ)|^2163 ≤ (12327681114597/100000000000000 : ℝ)^1651
        have hw : |(-50584481/250000000 : ℝ)|=(50584481/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676472581/1250000000 : ℝ)|^2163 ≤ (8946948773309/20000000000000 : ℝ)^1651
        have hw : |(676472581/1250000000 : ℝ)|=(676472581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622514611/5000000000 : ℝ)|^2163 ≤ (21468787500833/50000000000000 : ℝ)^1651
        have hw : |(2622514611/5000000000 : ℝ)|=(2622514611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s5_1 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668581401/1250000000 : ℝ)*x 0 + (-210832723/1000000000 : ℝ)*x 1 + (5245029187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668581401/1250000000 : ℝ)^2163 ≤ (2202615719381/5000000000000 : ℝ)^1651 := by
    have hnat : (668581401 : ℕ)^2163*5000000000000^1651 ≤ 2202615719381^1651*1250000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668581401 1250000000 2202615719381 5000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210832723/1000000000 : ℝ)^2163 ≤ (13010110974337/100000000000000 : ℝ)^1651 := by
    have hnat : (210832723 : ℕ)^2163*100000000000000^1651 ≤ 13010110974337^1651*1000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210832723 1000000000 13010110974337 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245029187/10000000000 : ℝ)^2163 ≤ (42937574626289/100000000000000 : ℝ)^1651 := by
    have hnat : (5245029187 : ℕ)^2163*100000000000000^1651 ≤ 42937574626289^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245029187 10000000000 42937574626289 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668581401/1250000000 : ℝ), (-210832723/1000000000 : ℝ), (5245029187/10000000000 : ℝ)] ![(2202615719381/5000000000000 : ℝ), (13010110974337/100000000000000 : ℝ), (42937574626289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668581401/1250000000 : ℝ)|^2163 ≤ (2202615719381/5000000000000 : ℝ)^1651
        have hw : |(668581401/1250000000 : ℝ)|=(668581401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-210832723/1000000000 : ℝ)|^2163 ≤ (13010110974337/100000000000000 : ℝ)^1651
        have hw : |(-210832723/1000000000 : ℝ)|=(210832723/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245029187/10000000000 : ℝ)|^2163 ≤ (42937574626289/100000000000000 : ℝ)^1651
        have hw : |(5245029187/10000000000 : ℝ)|=(5245029187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s5_2 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674325629/5000000000 : ℝ)*x 0 + (5245029211/10000000000 : ℝ)*x 1 + (-210832713/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674325629/5000000000 : ℝ)^2163 ≤ (8810462985427/20000000000000 : ℝ)^1651 := by
    have hnat : (2674325629 : ℕ)^2163*20000000000000^1651 ≤ 8810462985427^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674325629 5000000000 8810462985427 20000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245029211/10000000000 : ℝ)^2163 ≤ (4293757488369/10000000000000 : ℝ)^1651 := by
    have hnat : (5245029211 : ℕ)^2163*10000000000000^1651 ≤ 4293757488369^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245029211 10000000000 4293757488369 10000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210832713/1000000000 : ℝ)^2163 ≤ (101641485671/781250000000 : ℝ)^1651 := by
    have hnat : (210832713 : ℕ)^2163*781250000000^1651 ≤ 101641485671^1651*1000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210832713 1000000000 101641485671 781250000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674325629/5000000000 : ℝ), (5245029211/10000000000 : ℝ), (-210832713/1000000000 : ℝ)] ![(8810462985427/20000000000000 : ℝ), (4293757488369/10000000000000 : ℝ), (101641485671/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674325629/5000000000 : ℝ)|^2163 ≤ (8810462985427/20000000000000 : ℝ)^1651
        have hw : |(2674325629/5000000000 : ℝ)|=(2674325629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245029211/10000000000 : ℝ)|^2163 ≤ (4293757488369/10000000000000 : ℝ)^1651
        have hw : |(5245029211/10000000000 : ℝ)|=(5245029211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-210832713/1000000000 : ℝ)|^2163 ≤ (101641485671/781250000000 : ℝ)^1651
        have hw : |(-210832713/1000000000 : ℝ)|=(210832713/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s5_3 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4320361109/10000000000 : ℝ)*x 0 + (259216857/625000000 : ℝ)*x 1 + (2249949333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320361109/10000000000 : ℝ)^2163 ≤ (33303457072189/100000000000000 : ℝ)^1651 := by
    have hnat : (4320361109 : ℕ)^2163*100000000000000^1651 ≤ 33303457072189^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320361109 10000000000 33303457072189 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259216857/625000000 : ℝ)^2163 ≤ (31568361133889/100000000000000 : ℝ)^1651 := by
    have hnat : (259216857 : ℕ)^2163*100000000000000^1651 ≤ 31568361133889^1651*625000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259216857 625000000 31568361133889 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249949333/5000000000 : ℝ)^2163 ≤ (35128181774819/100000000000000 : ℝ)^1651 := by
    have hnat : (2249949333 : ℕ)^2163*100000000000000^1651 ≤ 35128181774819^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249949333 5000000000 35128181774819 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320361109/10000000000 : ℝ), (259216857/625000000 : ℝ), (2249949333/5000000000 : ℝ)] ![(33303457072189/100000000000000 : ℝ), (31568361133889/100000000000000 : ℝ), (35128181774819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320361109/10000000000 : ℝ)|^2163 ≤ (33303457072189/100000000000000 : ℝ)^1651
        have hw : |(4320361109/10000000000 : ℝ)|=(4320361109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259216857/625000000 : ℝ)|^2163 ≤ (31568361133889/100000000000000 : ℝ)^1651
        have hw : |(259216857/625000000 : ℝ)|=(259216857/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2249949333/5000000000 : ℝ)|^2163 ≤ (35128181774819/100000000000000 : ℝ)^1651
        have hw : |(2249949333/5000000000 : ℝ)|=(2249949333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s5_4 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2023391451/10000000000 : ℝ)*x 0 + (1049125873/2000000000 : ℝ)*x 1 + (5411177281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2023391451/10000000000 : ℝ)^2163 ≤ (123277785833/1000000000000 : ℝ)^1651 := by
    have hnat : (2023391451 : ℕ)^2163*1000000000000^1651 ≤ 123277785833^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023391451 10000000000 123277785833 1000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049125873/2000000000 : ℝ)^2163 ≤ (21472005837707/50000000000000 : ℝ)^1651 := by
    have hnat : (1049125873 : ℕ)^2163*50000000000000^1651 ≤ 21472005837707^1651*2000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049125873 2000000000 21472005837707 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411177281/10000000000 : ℝ)^2163 ≤ (11182052432291/25000000000000 : ℝ)^1651 := by
    have hnat : (5411177281 : ℕ)^2163*25000000000000^1651 ≤ 11182052432291^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411177281 10000000000 11182052432291 25000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2023391451/10000000000 : ℝ), (1049125873/2000000000 : ℝ), (5411177281/10000000000 : ℝ)] ![(123277785833/1000000000000 : ℝ), (21472005837707/50000000000000 : ℝ), (11182052432291/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2023391451/10000000000 : ℝ)|^2163 ≤ (123277785833/1000000000000 : ℝ)^1651
        have hw : |(-2023391451/10000000000 : ℝ)|=(2023391451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049125873/2000000000 : ℝ)|^2163 ≤ (21472005837707/50000000000000 : ℝ)^1651
        have hw : |(1049125873/2000000000 : ℝ)|=(1049125873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411177281/10000000000 : ℝ)|^2163 ≤ (11182052432291/25000000000000 : ℝ)^1651
        have hw : |(5411177281/10000000000 : ℝ)|=(5411177281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s5_5 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305583529/10000000000 : ℝ)*x 0 + (-1942179097/10000000000 : ℝ)*x 1 + (43289417/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305583529/10000000000 : ℝ)^2163 ≤ (21794091046969/50000000000000 : ℝ)^1651 := by
    have hnat : (5305583529 : ℕ)^2163*50000000000000^1651 ≤ 21794091046969^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305583529 10000000000 21794091046969 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1942179097/10000000000 : ℝ)^2163 ≤ (2336721969979/20000000000000 : ℝ)^1651 := by
    have hnat : (1942179097 : ℕ)^2163*20000000000000^1651 ≤ 2336721969979^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1942179097 10000000000 2336721969979 20000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43289417/80000000 : ℝ)^2163 ≤ (44728208039797/100000000000000 : ℝ)^1651 := by
    have hnat : (43289417 : ℕ)^2163*100000000000000^1651 ≤ 44728208039797^1651*80000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43289417 80000000 44728208039797 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305583529/10000000000 : ℝ), (-1942179097/10000000000 : ℝ), (43289417/80000000 : ℝ)] ![(21794091046969/50000000000000 : ℝ), (2336721969979/20000000000000 : ℝ), (44728208039797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305583529/10000000000 : ℝ)|^2163 ≤ (21794091046969/50000000000000 : ℝ)^1651
        have hw : |(5305583529/10000000000 : ℝ)|=(5305583529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1942179097/10000000000 : ℝ)|^2163 ≤ (2336721969979/20000000000000 : ℝ)^1651
        have hw : |(-1942179097/10000000000 : ℝ)|=(1942179097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43289417/80000000 : ℝ)|^2163 ≤ (44728208039797/100000000000000 : ℝ)^1651
        have hw : |(43289417/80000000 : ℝ)|=(43289417/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s5_6 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (41449873/78125000 : ℝ)*x 0 + (1082235367/2000000000 : ℝ)*x 1 + (-971089601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41449873/78125000 : ℝ)^2163 ≤ (21794092204023/50000000000000 : ℝ)^1651 := by
    have hnat : (41449873 : ℕ)^2163*50000000000000^1651 ≤ 21794092204023^1651*78125000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41449873 78125000 21794092204023 50000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082235367/2000000000 : ℝ)^2163 ≤ (44728204899309/100000000000000 : ℝ)^1651 := by
    have hnat : (1082235367 : ℕ)^2163*100000000000000^1651 ≤ 44728204899309^1651*2000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082235367 2000000000 44728204899309 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (971089601/5000000000 : ℝ)^2163 ≤ (11683610677431/100000000000000 : ℝ)^1651 := by
    have hnat : (971089601 : ℕ)^2163*100000000000000^1651 ≤ 11683610677431^1651*5000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971089601 5000000000 11683610677431 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41449873/78125000 : ℝ), (1082235367/2000000000 : ℝ), (-971089601/5000000000 : ℝ)] ![(21794092204023/50000000000000 : ℝ), (44728204899309/100000000000000 : ℝ), (11683610677431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41449873/78125000 : ℝ)|^2163 ≤ (21794092204023/50000000000000 : ℝ)^1651
        have hw : |(41449873/78125000 : ℝ)|=(41449873/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082235367/2000000000 : ℝ)|^2163 ≤ (44728204899309/100000000000000 : ℝ)^1651
        have hw : |(1082235367/2000000000 : ℝ)|=(1082235367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-971089601/5000000000 : ℝ)|^2163 ≤ (11683610677431/100000000000000 : ℝ)^1651
        have hw : |(-971089601/5000000000 : ℝ)|=(971089601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1366_s5_7 (p : ℝ) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4320386831/10000000000 : ℝ)*x 0 + (562328737/1250000000 : ℝ)*x 1 + (4148744813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320386831/10000000000 : ℝ)^2163 ≤ (4162964604889/12500000000000 : ℝ)^1651 := by
    have hnat : (4320386831 : ℕ)^2163*12500000000000^1651 ≤ 4162964604889^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320386831 10000000000 4162964604889 12500000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562328737/1250000000 : ℝ)^2163 ≤ (35115206209263/100000000000000 : ℝ)^1651 := by
    have hnat : (562328737 : ℕ)^2163*100000000000000^1651 ≤ 35115206209263^1651*1250000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562328737 1250000000 35115206209263 100000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4148744813/10000000000 : ℝ)^2163 ≤ (1579053846487/5000000000000 : ℝ)^1651 := by
    have hnat : (4148744813 : ℕ)^2163*5000000000000^1651 ≤ 1579053846487^1651*10000000000^2163 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148744813 10000000000 1579053846487 5000000000000 2163 1651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2163/512 : ℝ)) 2163 1651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320386831/10000000000 : ℝ), (562328737/1250000000 : ℝ), (4148744813/10000000000 : ℝ)] ![(4162964604889/12500000000000 : ℝ), (35115206209263/100000000000000 : ℝ), (1579053846487/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320386831/10000000000 : ℝ)|^2163 ≤ (4162964604889/12500000000000 : ℝ)^1651
        have hw : |(4320386831/10000000000 : ℝ)|=(4320386831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(562328737/1250000000 : ℝ)|^2163 ≤ (35115206209263/100000000000000 : ℝ)^1651
        have hw : |(562328737/1250000000 : ℝ)|=(562328737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4148744813/10000000000 : ℝ)|^2163 ≤ (1579053846487/5000000000000 : ℝ)^1651
        have hw : |(4148744813/10000000000 : ℝ)|=(4148744813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1366_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155675079/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5581/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5599/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14729/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5581/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5581/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5581/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5581/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5581/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5581/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5581/50000 : ℝ) ^ (4325/1024 : ℝ) ≤ (9506309332933367/100000000000000000000 : ℝ) := by
    have hpowers : (5581/50000 : ℝ)^4325 ≤ (9506309332933367/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5581 : ℕ)^4325*100000000000000000000^1024 ≤ 9506309332933367^1024*50000^4325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5581 50000 9506309332933367 100000000000000000000 4325 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5581/50000 : ℝ)) (X := (9506309332933367/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14767/100000 : ℝ) ^ (4325/1024 : ℝ) ≤ (7750604983689239/25000000000000000000 : ℝ) := by
    have hpowers : (14767/100000 : ℝ)^4325 ≤ (7750604983689239/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14767 : ℕ)^4325*25000000000000000000^1024 ≤ 7750604983689239^1024*100000^4325 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14767 100000 7750604983689239 25000000000000000000 4325 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14767/100000 : ℝ)) (X := (7750604983689239/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009506309332933367/50000000000000000000 : ℝ) ≤ (5000225057908567/5000000000000000 : ℝ) ^ (4325/1024 : ℝ) := by
    have hpowers : (50009506309332933367/50000000000000000000 : ℝ)^1024 ≤ (5000225057908567/5000000000000000 : ℝ)^4325 := by
      have hnat : (50009506309332933367 : ℕ)^1024*5000000000000000^4325 ≤ 5000225057908567^4325*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009506309332933367 50000000000000000000 5000225057908567 5000000000000000 1024 4325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000225057908567/5000000000000000 : ℝ)) (X := (50009506309332933367/50000000000000000000 : ℝ)) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040508729267690323/100000000000000000000 : ℝ) ≤ (1250119868577479/1250000000000000 : ℝ) ^ (4325/1024 : ℝ) := by
    have hpowers : (100040508729267690323/100000000000000000000 : ℝ)^1024 ≤ (1250119868577479/1250000000000000 : ℝ)^4325 := by
      have hnat : (100040508729267690323 : ℕ)^1024*1250000000000000^4325 ≤ 1250119868577479^4325*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040508729267690323 100000000000000000000 1250119868577479 1250000000000000 1024 4325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250119868577479/1250000000000000 : ℝ)) (X := (100040508729267690323/100000000000000000000 : ℝ)) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507750604983689239/12500000000000000000 : ℝ) ≤ (1000146778142253/1000000000000000 : ℝ) ^ (4325/1024 : ℝ) := by
    have hpowers : (12507750604983689239/12500000000000000000 : ℝ)^1024 ≤ (1000146778142253/1000000000000000 : ℝ)^4325 := by
      have hnat : (12507750604983689239 : ℕ)^1024*1000000000000000^4325 ≤ 1000146778142253^4325*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507750604983689239 12500000000000000000 1000146778142253 1000000000000000 1024 4325 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000146778142253/1000000000000000 : ℝ)) (X := (12507750604983689239/12500000000000000000 : ℝ)) (by norm_num) 4325 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9506309332933367/100000000000000000000 : ℝ) ≤ ((18020131742016668959/18025000000000000000 : ℝ)+2*(254416401349/180250000000000 : ℝ)*(5581/50000 : ℝ))^(4325/1024 : ℝ) := by
    rw [show (18020131742016668959/18025000000000000000 : ℝ)+2*(254416401349/180250000000000 : ℝ)*(5581/50000 : ℝ)=(5000225057908567/5000000000000000 : ℝ) by norm_num, show 1+2*(9506309332933367/100000000000000000000 : ℝ)=(50009506309332933367/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7750604983689239/25000000000000000000 : ℝ)+(9506309332933367/100000000000000000000 : ℝ) ≤ ((18020131742016668959/18025000000000000000 : ℝ)+(254416401349/180250000000000 : ℝ)*((14767/100000 : ℝ)+(5581/50000 : ℝ)))^(4325/1024 : ℝ) := by
    rw [show (18020131742016668959/18025000000000000000 : ℝ)+(254416401349/180250000000000 : ℝ)*((14767/100000 : ℝ)+(5581/50000 : ℝ))=(1250119868577479/1250000000000000 : ℝ) by norm_num, show 1+(7750604983689239/25000000000000000000 : ℝ)+(9506309332933367/100000000000000000000 : ℝ)=(100040508729267690323/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7750604983689239/25000000000000000000 : ℝ) ≤ ((18020131742016668959/18025000000000000000 : ℝ)+2*(254416401349/180250000000000 : ℝ)*(14767/100000 : ℝ))^(4325/1024 : ℝ) := by
    rw [show (18020131742016668959/18025000000000000000 : ℝ)+2*(254416401349/180250000000000 : ℝ)*(14767/100000 : ℝ)=(1000146778142253/1000000000000000 : ℝ) by norm_num, show 1+2*(7750604983689239/25000000000000000000 : ℝ)=(12507750604983689239/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18020131742016668959/18025000000000000000 : ℝ)*(X 1 0+X 2 0)+(254416401349/180250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4325/1024 : ℝ)) (lo := (5581/50000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (18020131742016668959/18025000000000000000 : ℝ)) (alpha := (254416401349/180250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18020131742016668959/18025000000000000000 : ℝ)*(X 0 1+X 2 1)+(254416401349/180250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4325/1024 : ℝ)) (lo := (5581/50000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (18020131742016668959/18025000000000000000 : ℝ)) (alpha := (254416401349/180250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18020131742016668959/18025000000000000000 : ℝ)*(X 0 2+X 1 2)+(254416401349/180250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4325/1024 : ℝ)) (lo := (5581/50000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (18020131742016668959/18025000000000000000 : ℝ)) (alpha := (254416401349/180250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-50584481/250000000 : ℝ)*X 0 0+(676472581/1250000000 : ℝ)*X 0 1+(2622514611/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668581401/1250000000 : ℝ)*X 1 0+(-210832723/1000000000 : ℝ)*X 1 1+(5245029187/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674325629/5000000000 : ℝ)*X 2 0+(5245029211/10000000000 : ℝ)*X 2 1+(-210832713/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4320361109/10000000000 : ℝ)*X 0 0+(259216857/625000000 : ℝ)*X 0 1+(2249949333/5000000000 : ℝ)*X 0 2+(4320361109/10000000000 : ℝ)*X 1 0+(259216857/625000000 : ℝ)*X 1 1+(2249949333/5000000000 : ℝ)*X 1 2+(4320361109/10000000000 : ℝ)*X 2 0+(259216857/625000000 : ℝ)*X 2 1+(2249949333/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2023391451/10000000000 : ℝ)*X 0 0+(1049125873/2000000000 : ℝ)*X 0 1+(5411177281/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305583529/10000000000 : ℝ)*X 1 0+(-1942179097/10000000000 : ℝ)*X 1 1+(43289417/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((41449873/78125000 : ℝ)*X 2 0+(1082235367/2000000000 : ℝ)*X 2 1+(-971089601/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4320386831/10000000000 : ℝ)*X 0 0+(562328737/1250000000 : ℝ)*X 0 1+(4148744813/10000000000 : ℝ)*X 0 2+(4320386831/10000000000 : ℝ)*X 1 0+(562328737/1250000000 : ℝ)*X 1 1+(4148744813/10000000000 : ℝ)*X 1 2+(4320386831/10000000000 : ℝ)*X 2 0+(562328737/1250000000 : ℝ)*X 2 1+(4148744813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1366_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (331947102288846097985966991/45062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (255209899/20000000000000 : ℝ)*(base19) + (1275455479/100000000000000 : ℝ)*(base23) + (6060549/20000000000000 : ℝ)*(lower2) + (38224729/50000000000000 : ℝ)*(upper3) + (83593053/50000000000000 : ℝ)*(upper5) + (220862037676817/5000000000000 : ℝ)*(major0) + (220862037676817/5000000000000 : ℝ)*(major1) + (220862037676817/5000000000000 : ℝ)*(major2) + (2998488026508137/50000000000000 : ℝ)*(sp0) + (5997005431482649/100000000000000 : ℝ)*(sp1) + (1199401086415333/20000000000000 : ℝ)*(sp2) + (2837463333732543/100000000000000 : ℝ)*(sp3) + (3065451587/10000000000000 : ℝ)*(sp4) + (11220262281/100000000000000 : ℝ)*(sp7) + (354684319249353/12500000000000 : ℝ)*(f.failure) + (374812919220759/6250000000000 : ℝ)*(f.sum) + (707300324911/225312500000000000000000000 : ℝ)*base66 + (412022051159373503/90125000000000000000000000000000 : ℝ)*base67 + (8089381122498503/90125000000000000000000000000000 : ℝ)*base69 + (379816486880126497/90125000000000000000000000000000 : ℝ)*base72 + (2814139710373/1802500000000000000000000000 : ℝ)*base74 + (1944013309264373503/90125000000000000000000000000000 : ℝ)*base75 + (920548874472376497/90125000000000000000000000000000 : ℝ)*base78 + (130501002837748503/90125000000000000000000000000000 : ℝ)*base79 + (6356159078259/3605000000000000000000000000 : ℝ)*base81 + (1026113/1250000000000000000000 : ℝ)*base90 + (1026113/1250000000000000000000 : ℝ)*base92 + (1026113/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4027900232721810816562918887/450625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (476576369/20000000000000 : ℝ)*(base19) + (1299070737/50000000000000 : ℝ)*(base23) + (37643269/25000000000000 : ℝ)*(upper3) + (810197/5000000000000 : ℝ)*(lower4) + (321933311/100000000000000 : ℝ)*(upper5) + (2224658574065869/50000000000000 : ℝ)*(major0) + (2224658574065869/50000000000000 : ℝ)*(major1) + (2224658574065869/50000000000000 : ℝ)*(major2) + (255391837/500000000000 : ℝ)*(sp1) + (43679014467/100000000000000 : ℝ)*(sp2) + (6040554736872761/100000000000000 : ℝ)*(sp4) + (6040501275623517/100000000000000 : ℝ)*(sp5) + (6040508459716821/100000000000000 : ℝ)*(sp6) + (1429039630720771/50000000000000 : ℝ)*(sp7) + (1429039630720771/50000000000000 : ℝ)*(f.failure) + (6040554736872761/100000000000000 : ℝ)*(f.sum) + (110137382211349/18025000000000000000000000000 : ℝ)*base65 + (2785582419134489629/901250000000000000000000000000000 : ℝ)*base68 + (6117056927253010371/901250000000000000000000000000000 : ℝ)*base69 + (7242952855543010371/901250000000000000000000000000000 : ℝ)*base71 + (71865867798049/18025000000000000000000000000 : ℝ)*base73 + (1339702289673010371/901250000000000000000000000000000 : ℝ)*base75 + (3833851604471760371/901250000000000000000000000000000 : ℝ)*base77 + (8365590958318239629/901250000000000000000000000000000 : ℝ)*base80 + (1078353870113/9012500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (47634091/5000000000000000000000 : ℝ)*base90 + (47634091/5000000000000000000000 : ℝ)*base92 + (47634091/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1366_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155675079/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5581/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5599/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14729/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1366_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1366_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155675079/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4003/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2001/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5599/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14729/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1366_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1366_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1366_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4325/1024 : ℝ) ≤ p) (hpb : p ≤ (2163/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155675079/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4003/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2001/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5599/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14729/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1366_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
