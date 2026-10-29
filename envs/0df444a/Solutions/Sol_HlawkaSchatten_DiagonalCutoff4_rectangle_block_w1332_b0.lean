-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1332_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:02:31.287544+00:00
-- url     : https://prove2.me/submissions/4f8a4bb0-c10e-43e9-98bf-e785f455e9fc

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
theorem support_rectangle_w1332_s0_0 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-363014539/2000000000 : ℝ)*x 0 + (1500311757/2500000000 : ℝ)*x 1 + (601064683/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (363014539/2000000000 : ℝ)^1073 ≤ (10633464125107/100000000000000 : ℝ)^817 := by
    have hnat : (363014539 : ℕ)^1073*100000000000000^817 ≤ 10633464125107^817*2000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363014539 2000000000 10633464125107 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1500311757/2500000000 : ℝ)^1073 ≤ (10227873812991/20000000000000 : ℝ)^817 := by
    have hnat : (1500311757 : ℕ)^1073*20000000000000^817 ≤ 10227873812991^817*2500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1500311757 2500000000 10227873812991 20000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (601064683/1250000000 : ℝ)^1073 ≤ (2389197924931/6250000000000 : ℝ)^817 := by
    have hnat : (601064683 : ℕ)^1073*6250000000000^817 ≤ 2389197924931^817*1250000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601064683 1250000000 2389197924931 6250000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-363014539/2000000000 : ℝ), (1500311757/2500000000 : ℝ), (601064683/1250000000 : ℝ)] ![(10633464125107/100000000000000 : ℝ), (10227873812991/20000000000000 : ℝ), (2389197924931/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-363014539/2000000000 : ℝ)|^1073 ≤ (10633464125107/100000000000000 : ℝ)^817
        have hw : |(-363014539/2000000000 : ℝ)|=(363014539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1500311757/2500000000 : ℝ)|^1073 ≤ (10227873812991/20000000000000 : ℝ)^817
        have hw : |(1500311757/2500000000 : ℝ)|=(1500311757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(601064683/1250000000 : ℝ)|^1073 ≤ (2389197924931/6250000000000 : ℝ)^817
        have hw : |(601064683/1250000000 : ℝ)|=(601064683/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s0_1 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1100586579/2000000000 : ℝ)*x 0 + (-2493508911/10000000000 : ℝ)*x 1 + (300532363/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1100586579/2000000000 : ℝ)^1073 ≤ (45636425576559/100000000000000 : ℝ)^817 := by
    have hnat : (1100586579 : ℕ)^1073*100000000000000^817 ≤ 45636425576559^817*2000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100586579 2000000000 45636425576559 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2493508911/10000000000 : ℝ)^1073 ≤ (504262625457/3125000000000 : ℝ)^817 := by
    have hnat : (2493508911 : ℕ)^1073*3125000000000^817 ≤ 504262625457^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2493508911 10000000000 504262625457 3125000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (300532363/625000000 : ℝ)^1073 ≤ (38227170390571/100000000000000 : ℝ)^817 := by
    have hnat : (300532363 : ℕ)^1073*100000000000000^817 ≤ 38227170390571^817*625000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300532363 625000000 38227170390571 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1100586579/2000000000 : ℝ), (-2493508911/10000000000 : ℝ), (300532363/625000000 : ℝ)] ![(45636425576559/100000000000000 : ℝ), (504262625457/3125000000000 : ℝ), (38227170390571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1100586579/2000000000 : ℝ)|^1073 ≤ (45636425576559/100000000000000 : ℝ)^817
        have hw : |(1100586579/2000000000 : ℝ)|=(1100586579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2493508911/10000000000 : ℝ)|^1073 ≤ (504262625457/3125000000000 : ℝ)^817
        have hw : |(-2493508911/10000000000 : ℝ)|=(2493508911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(300532363/625000000 : ℝ)|^1073 ≤ (38227170390571/100000000000000 : ℝ)^817
        have hw : |(300532363/625000000 : ℝ)|=(300532363/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s0_2 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1375733101/2500000000 : ℝ)*x 0 + (4808517853/10000000000 : ℝ)*x 1 + (-1246754743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1375733101/2500000000 : ℝ)^1073 ≤ (22818210114371/50000000000000 : ℝ)^817 := by
    have hnat : (1375733101 : ℕ)^1073*50000000000000^817 ≤ 22818210114371^817*2500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375733101 2500000000 22818210114371 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4808517853/10000000000 : ℝ)^1073 ≤ (9556792715103/25000000000000 : ℝ)^817 := by
    have hnat : (4808517853 : ℕ)^1073*25000000000000^817 ≤ 9556792715103^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4808517853 10000000000 9556792715103 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1246754743/5000000000 : ℝ)^1073 ≤ (16136408901613/100000000000000 : ℝ)^817 := by
    have hnat : (1246754743 : ℕ)^1073*100000000000000^817 ≤ 16136408901613^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1246754743 5000000000 16136408901613 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1375733101/2500000000 : ℝ), (4808517853/10000000000 : ℝ), (-1246754743/5000000000 : ℝ)] ![(22818210114371/50000000000000 : ℝ), (9556792715103/25000000000000 : ℝ), (16136408901613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1375733101/2500000000 : ℝ)|^1073 ≤ (22818210114371/50000000000000 : ℝ)^817
        have hw : |(1375733101/2500000000 : ℝ)|=(1375733101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4808517853/10000000000 : ℝ)|^1073 ≤ (9556792715103/25000000000000 : ℝ)^817
        have hw : |(4808517853/10000000000 : ℝ)|=(4808517853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1246754743/5000000000 : ℝ)|^1073 ≤ (16136408901613/100000000000000 : ℝ)^817
        have hw : |(-1246754743/5000000000 : ℝ)|=(1246754743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s0_3 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4180247543/10000000000 : ℝ)*x 0 + (621415331/2000000000 : ℝ)*x 1 + (5595937591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4180247543/10000000000 : ℝ)^1073 ≤ (31805986436587/100000000000000 : ℝ)^817 := by
    have hnat : (4180247543 : ℕ)^1073*100000000000000^817 ≤ 31805986436587^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180247543 10000000000 31805986436587 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (621415331/2000000000 : ℝ)^1073 ≤ (5385484547989/25000000000000 : ℝ)^817 := by
    have hnat : (621415331 : ℕ)^1073*25000000000000^817 ≤ 5385484547989^817*2000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621415331 2000000000 5385484547989 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5595937591/10000000000 : ℝ)^1073 ≤ (11663018841427/25000000000000 : ℝ)^817 := by
    have hnat : (5595937591 : ℕ)^1073*25000000000000^817 ≤ 11663018841427^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5595937591 10000000000 11663018841427 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4180247543/10000000000 : ℝ), (621415331/2000000000 : ℝ), (5595937591/10000000000 : ℝ)] ![(31805986436587/100000000000000 : ℝ), (5385484547989/25000000000000 : ℝ), (11663018841427/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4180247543/10000000000 : ℝ)|^1073 ≤ (31805986436587/100000000000000 : ℝ)^817
        have hw : |(4180247543/10000000000 : ℝ)|=(4180247543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(621415331/2000000000 : ℝ)|^1073 ≤ (5385484547989/25000000000000 : ℝ)^817
        have hw : |(621415331/2000000000 : ℝ)|=(621415331/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5595937591/10000000000 : ℝ)|^1073 ≤ (11663018841427/25000000000000 : ℝ)^817
        have hw : |(5595937591/10000000000 : ℝ)|=(5595937591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s0_4 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-909791043/5000000000 : ℝ)*x 0 + (4839233303/10000000000 : ℝ)*x 1 + (5969434973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (909791043/5000000000 : ℝ)^1073 ≤ (10668173374309/100000000000000 : ℝ)^817 := by
    have hnat : (909791043 : ℕ)^1073*100000000000000^817 ≤ 10668173374309^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      909791043 5000000000 10668173374309 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4839233303/10000000000 : ℝ)^1073 ≤ (7709637752229/20000000000000 : ℝ)^817 := by
    have hnat : (4839233303 : ℕ)^1073*20000000000000^817 ≤ 7709637752229^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4839233303 10000000000 7709637752229 20000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5969434973/10000000000 : ℝ)^1073 ≤ (1269590946107/2500000000000 : ℝ)^817 := by
    have hnat : (5969434973 : ℕ)^1073*2500000000000^817 ≤ 1269590946107^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5969434973 10000000000 1269590946107 2500000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-909791043/5000000000 : ℝ), (4839233303/10000000000 : ℝ), (5969434973/10000000000 : ℝ)] ![(10668173374309/100000000000000 : ℝ), (7709637752229/20000000000000 : ℝ), (1269590946107/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-909791043/5000000000 : ℝ)|^1073 ≤ (10668173374309/100000000000000 : ℝ)^817
        have hw : |(-909791043/5000000000 : ℝ)|=(909791043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4839233303/10000000000 : ℝ)|^1073 ≤ (7709637752229/20000000000000 : ℝ)^817
        have hw : |(4839233303/10000000000 : ℝ)|=(4839233303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5969434973/10000000000 : ℝ)|^1073 ≤ (1269590946107/2500000000000 : ℝ)^817
        have hw : |(5969434973/10000000000 : ℝ)|=(5969434973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s0_5 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1294485141/2500000000 : ℝ)*x 0 + (-1332593089/10000000000 : ℝ)*x 1 + (596943413/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1294485141/2500000000 : ℝ)^1073 ≤ (10532479349907/25000000000000 : ℝ)^817 := by
    have hnat : (1294485141 : ℕ)^1073*25000000000000^817 ≤ 10532479349907^817*2500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294485141 2500000000 10532479349907 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1332593089/10000000000 : ℝ)^1073 ≤ (3543227078421/50000000000000 : ℝ)^817 := by
    have hnat : (1332593089 : ℕ)^1073*50000000000000^817 ≤ 3543227078421^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1332593089 10000000000 3543227078421 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (596943413/1000000000 : ℝ)^1073 ≤ (2031345137019/4000000000000 : ℝ)^817 := by
    have hnat : (596943413 : ℕ)^1073*4000000000000^817 ≤ 2031345137019^817*1000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596943413 1000000000 2031345137019 4000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1294485141/2500000000 : ℝ), (-1332593089/10000000000 : ℝ), (596943413/1000000000 : ℝ)] ![(10532479349907/25000000000000 : ℝ), (3543227078421/50000000000000 : ℝ), (2031345137019/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1294485141/2500000000 : ℝ)|^1073 ≤ (10532479349907/25000000000000 : ℝ)^817
        have hw : |(1294485141/2500000000 : ℝ)|=(1294485141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1332593089/10000000000 : ℝ)|^1073 ≤ (3543227078421/50000000000000 : ℝ)^817
        have hw : |(-1332593089/10000000000 : ℝ)|=(1332593089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(596943413/1000000000 : ℝ)|^1073 ≤ (2031345137019/4000000000000 : ℝ)^817
        have hw : |(596943413/1000000000 : ℝ)|=(596943413/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s0_6 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2588970469/5000000000 : ℝ)*x 0 + (1492358613/2500000000 : ℝ)*x 1 + (-666296001/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2588970469/5000000000 : ℝ)^1073 ≤ (8425984279231/20000000000000 : ℝ)^817 := by
    have hnat : (2588970469 : ℕ)^1073*20000000000000^817 ≤ 8425984279231^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588970469 5000000000 8425984279231 20000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1492358613/2500000000 : ℝ)^1073 ≤ (396747125181/781250000000 : ℝ)^817 := by
    have hnat : (1492358613 : ℕ)^1073*781250000000^817 ≤ 396747125181^817*2500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1492358613 2500000000 396747125181 781250000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (666296001/5000000000 : ℝ)^1073 ≤ (141728931303/2000000000000 : ℝ)^817 := by
    have hnat : (666296001 : ℕ)^1073*2000000000000^817 ≤ 141728931303^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      666296001 5000000000 141728931303 2000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2588970469/5000000000 : ℝ), (1492358613/2500000000 : ℝ), (-666296001/5000000000 : ℝ)] ![(8425984279231/20000000000000 : ℝ), (396747125181/781250000000 : ℝ), (141728931303/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2588970469/5000000000 : ℝ)|^1073 ≤ (8425984279231/20000000000000 : ℝ)^817
        have hw : |(2588970469/5000000000 : ℝ)|=(2588970469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1492358613/2500000000 : ℝ)|^1073 ≤ (396747125181/781250000000 : ℝ)^817
        have hw : |(1492358613/2500000000 : ℝ)|=(1492358613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-666296001/5000000000 : ℝ)|^1073 ≤ (141728931303/2000000000000 : ℝ)^817
        have hw : |(-666296001/5000000000 : ℝ)|=(666296001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s0_7 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (837931169/2000000000 : ℝ)*x 0 + (5531843501/10000000000 : ℝ)*x 1 + (1586728991/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (837931169/2000000000 : ℝ)^1073 ≤ (7975008568617/25000000000000 : ℝ)^817 := by
    have hnat : (837931169 : ℕ)^1073*25000000000000^817 ≤ 7975008568617^817*2000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837931169 2000000000 7975008568617 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5531843501/10000000000 : ℝ)^1073 ≤ (45951569658431/100000000000000 : ℝ)^817 := by
    have hnat : (5531843501 : ℕ)^1073*100000000000000^817 ≤ 45951569658431^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5531843501 10000000000 45951569658431 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1586728991/5000000000 : ℝ)^1073 ≤ (11074198023069/50000000000000 : ℝ)^817 := by
    have hnat : (1586728991 : ℕ)^1073*50000000000000^817 ≤ 11074198023069^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1586728991 5000000000 11074198023069 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(837931169/2000000000 : ℝ), (5531843501/10000000000 : ℝ), (1586728991/5000000000 : ℝ)] ![(7975008568617/25000000000000 : ℝ), (45951569658431/100000000000000 : ℝ), (11074198023069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(837931169/2000000000 : ℝ)|^1073 ≤ (7975008568617/25000000000000 : ℝ)^817
        have hw : |(837931169/2000000000 : ℝ)|=(837931169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5531843501/10000000000 : ℝ)|^1073 ≤ (45951569658431/100000000000000 : ℝ)^817
        have hw : |(5531843501/10000000000 : ℝ)|=(5531843501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1586728991/5000000000 : ℝ)|^1073 ≤ (11074198023069/50000000000000 : ℝ)^817
        have hw : |(1586728991/5000000000 : ℝ)|=(1586728991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1332_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (120574/78125 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1339/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26943/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4291/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4291 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4291*1^1024 ≤ 0^1024*1^4291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4291 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4291/1024 : ℝ) ≤ (215010848877428379/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4291 ≤ (215010848877428379/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4291*10000000000000000000^1024 ≤ 215010848877428379^1024*5^4291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 215010848877428379 10000000000000000000 4291 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (215010848877428379/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4291 := by
      have hnat : (1 : ℕ)^1024*1^4291 ≤ 1^4291*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10215010848877428379/10000000000000000000 : ℝ) ≤ (5025447613162327/5000000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (10215010848877428379/10000000000000000000 : ℝ)^1024 ≤ (5025447613162327/5000000000000000 : ℝ)^4291 := by
      have hnat : (10215010848877428379 : ℕ)^1024*5000000000000000^4291 ≤ 5025447613162327^4291*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10215010848877428379 10000000000000000000 5025447613162327 5000000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5025447613162327/5000000000000000 : ℝ)) (X := (10215010848877428379/10000000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5215010848877428379/5000000000000000000 : ℝ) ≤ (2525447613162327/2500000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (5215010848877428379/5000000000000000000 : ℝ)^1024 ≤ (2525447613162327/2500000000000000 : ℝ)^4291 := by
      have hnat : (5215010848877428379 : ℕ)^1024*2500000000000000^4291 ≤ 2525447613162327^4291*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5215010848877428379 5000000000000000000 2525447613162327 2500000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2525447613162327/2500000000000000 : ℝ)) (X := (5215010848877428379/5000000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(25447613162327/2000000000000000 : ℝ)*(0 : ℝ))^(4291/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(25447613162327/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(215010848877428379/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(25447613162327/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4291/1024 : ℝ) := by
    rw [show (1 : ℝ)+(25447613162327/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5025447613162327/5000000000000000 : ℝ) by norm_num, show 1+(215010848877428379/10000000000000000000 : ℝ)+(0 : ℝ)=(10215010848877428379/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(215010848877428379/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(25447613162327/2000000000000000 : ℝ)*(2/5 : ℝ))^(4291/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(25447613162327/2000000000000000 : ℝ)*(2/5 : ℝ)=(2525447613162327/2500000000000000 : ℝ) by norm_num, show 1+2*(215010848877428379/10000000000000000000 : ℝ)=(5215010848877428379/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(25447613162327/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25447613162327/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(25447613162327/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25447613162327/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(25447613162327/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25447613162327/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-363014539/2000000000 : ℝ)*X 0 0+(1500311757/2500000000 : ℝ)*X 0 1+(601064683/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1100586579/2000000000 : ℝ)*X 1 0+(-2493508911/10000000000 : ℝ)*X 1 1+(300532363/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1375733101/2500000000 : ℝ)*X 2 0+(4808517853/10000000000 : ℝ)*X 2 1+(-1246754743/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4180247543/10000000000 : ℝ)*X 0 0+(621415331/2000000000 : ℝ)*X 0 1+(5595937591/10000000000 : ℝ)*X 0 2+(4180247543/10000000000 : ℝ)*X 1 0+(621415331/2000000000 : ℝ)*X 1 1+(5595937591/10000000000 : ℝ)*X 1 2+(4180247543/10000000000 : ℝ)*X 2 0+(621415331/2000000000 : ℝ)*X 2 1+(5595937591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-909791043/5000000000 : ℝ)*X 0 0+(4839233303/10000000000 : ℝ)*X 0 1+(5969434973/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1294485141/2500000000 : ℝ)*X 1 0+(-1332593089/10000000000 : ℝ)*X 1 1+(596943413/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2588970469/5000000000 : ℝ)*X 2 0+(1492358613/2500000000 : ℝ)*X 2 1+(-666296001/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((837931169/2000000000 : ℝ)*X 0 0+(5531843501/10000000000 : ℝ)*X 0 1+(1586728991/5000000000 : ℝ)*X 0 2+(837931169/2000000000 : ℝ)*X 1 0+(5531843501/10000000000 : ℝ)*X 1 1+(1586728991/5000000000 : ℝ)*X 1 2+(837931169/2000000000 : ℝ)*X 2 0+(5531843501/10000000000 : ℝ)*X 2 1+(1586728991/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (206561327360888301362403/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (469253/625000000000 : ℝ)*(base1) + (64206993/6250000000000 : ℝ)*(base19) + (476251923/50000000000000 : ℝ)*(base23) + (187312119/100000000000000 : ℝ)*(upper3) + (17435269/100000000000000 : ℝ)*(upper5) + (310053308291779/50000000000000 : ℝ)*(major0) + (310053308291779/50000000000000 : ℝ)*(major1) + (310053308291779/50000000000000 : ℝ)*(major2) + (838416918828997/100000000000000 : ℝ)*(sp0) + (838418734422403/100000000000000 : ℝ)*(sp1) + (209604702307611/25000000000000 : ℝ)*(sp2) + (3138996010991/781250000000 : ℝ)*(sp3) + (1458992887/50000000000000 : ℝ)*(sp4) + (1769237939/100000000000000 : ℝ)*(sp7) + (100448333431317/25000000000000 : ℝ)*(f.failure) + (83841976173429/10000000000000 : ℝ)*(f.sum) + (216233784609733/50000000000000000000000000000 : ℝ)*base65 + (744073425090267/100000000000000000000000000000 : ℝ)*base68 + (393550609009733/100000000000000000000000000000 : ℝ)*base69 + (43563853790267/100000000000000000000000000000 : ℝ)*base72 + (32489369309733/50000000000000000000000000000 : ℝ)*base73 + (94796882390267/100000000000000000000000000000 : ℝ)*base76 + (526710077109733/100000000000000000000000000000 : ℝ)*base77 + (210165145509733/100000000000000000000000000000 : ℝ)*base79 + (300508082509733/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2459/3906250000000000000 : ℝ)*base90 + (2459/3906250000000000000 : ℝ)*base92 + (2459/3906250000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (303936177671722375026597/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (96819281/12500000000000 : ℝ)*(base19) + (196368347/20000000000000 : ℝ)*(base23) + (107734249/100000000000000 : ℝ)*(base39) + (67442109/100000000000000 : ℝ)*(upper3) + (125833063/100000000000000 : ℝ)*(upper5) + (327204110867489/50000000000000 : ℝ)*(major0) + (327204110867489/50000000000000 : ℝ)*(major1) + (654408114000729/100000000000000 : ℝ)*(major2) + (1465727161/100000000000000 : ℝ)*(sp1) + (2075823181/100000000000000 : ℝ)*(sp2) + (221199359576591/25000000000000 : ℝ)*(sp4) + (176959039604991/20000000000000 : ℝ)*(sp5) + (884794488375697/100000000000000 : ℝ)*(sp6) + (212009398058641/50000000000000 : ℝ)*(sp7) + (212009398058641/50000000000000 : ℝ)*(f.failure) + (884797546040613/100000000000000 : ℝ)*(f.sum) + (173175236089811/200000000000000000000000000000 : ℝ)*base66 + (729006358536383/200000000000000000000000000000 : ℝ)*base67 + (383947234286903/100000000000000000000000000000 : ℝ)*base69 + (463741472336383/200000000000000000000000000000 : ℝ)*base71 + (184405037910189/200000000000000000000000000000 : ℝ)*base73 + (268304327686903/100000000000000000000000000000 : ℝ)*base75 + (200393123886903/100000000000000000000000000000 : ℝ)*base77 + (99403771986903/100000000000000000000000000000 : ℝ)*base79 + (1284815686903/50000000000000000000000000000 : ℝ)*base81 + (1809/3906250000000000000 : ℝ)*base89 + (1809/3906250000000000000 : ℝ)*base91 + (1809/3906250000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1332_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (120574/78125 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1339/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26943/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1332_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1332_s1_0 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-100066687/500000000 : ℝ)*x 0 + (5646644063/10000000000 : ℝ)*x 1 + (1260961681/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100066687/500000000 : ℝ)^1073 ≤ (12089098920697/100000000000000 : ℝ)^817 := by
    have hnat : (100066687 : ℕ)^1073*100000000000000^817 ≤ 12089098920697^817*500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100066687 500000000 12089098920697 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5646644063/10000000000 : ℝ)^1073 ≤ (23604024373593/50000000000000 : ℝ)^817 := by
    have hnat : (5646644063 : ℕ)^1073*50000000000000^817 ≤ 23604024373593^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5646644063 10000000000 23604024373593 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1260961681/2500000000 : ℝ)^1073 ≤ (40702852321669/100000000000000 : ℝ)^817 := by
    have hnat : (1260961681 : ℕ)^1073*100000000000000^817 ≤ 40702852321669^817*2500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1260961681 2500000000 40702852321669 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-100066687/500000000 : ℝ), (5646644063/10000000000 : ℝ), (1260961681/2500000000 : ℝ)] ![(12089098920697/100000000000000 : ℝ), (23604024373593/50000000000000 : ℝ), (40702852321669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-100066687/500000000 : ℝ)|^1073 ≤ (12089098920697/100000000000000 : ℝ)^817
        have hw : |(-100066687/500000000 : ℝ)|=(100066687/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5646644063/10000000000 : ℝ)|^1073 ≤ (23604024373593/50000000000000 : ℝ)^817
        have hw : |(5646644063/10000000000 : ℝ)|=(5646644063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1260961681/2500000000 : ℝ)|^1073 ≤ (40702852321669/100000000000000 : ℝ)^817
        have hw : |(1260961681/2500000000 : ℝ)|=(1260961681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s1_1 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5406761623/10000000000 : ℝ)*x 0 + (-2323277391/10000000000 : ℝ)*x 1 + (31524041/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5406761623/10000000000 : ℝ)^1073 ≤ (22295918970979/50000000000000 : ℝ)^817 := by
    have hnat : (5406761623 : ℕ)^1073*50000000000000^817 ≤ 22295918970979^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406761623 10000000000 22295918970979 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2323277391/10000000000 : ℝ)^1073 ≤ (588212458713/4000000000000 : ℝ)^817 := by
    have hnat : (2323277391 : ℕ)^1073*4000000000000^817 ≤ 588212458713^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2323277391 10000000000 588212458713 4000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31524041/62500000 : ℝ)^1073 ≤ (4070285058353/10000000000000 : ℝ)^817 := by
    have hnat : (31524041 : ℕ)^1073*10000000000000^817 ≤ 4070285058353^817*62500000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31524041 62500000 4070285058353 10000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5406761623/10000000000 : ℝ), (-2323277391/10000000000 : ℝ), (31524041/62500000 : ℝ)] ![(22295918970979/50000000000000 : ℝ), (588212458713/4000000000000 : ℝ), (4070285058353/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5406761623/10000000000 : ℝ)|^1073 ≤ (22295918970979/50000000000000 : ℝ)^817
        have hw : |(5406761623/10000000000 : ℝ)|=(5406761623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2323277391/10000000000 : ℝ)|^1073 ≤ (588212458713/4000000000000 : ℝ)^817
        have hw : |(-2323277391/10000000000 : ℝ)|=(2323277391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(31524041/62500000 : ℝ)|^1073 ≤ (4070285058353/10000000000000 : ℝ)^817
        have hw : |(31524041/62500000 : ℝ)|=(31524041/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s1_2 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5406761741/10000000000 : ℝ)*x 0 + (1260961571/2500000000 : ℝ)*x 1 + (-580819397/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5406761741/10000000000 : ℝ)^1073 ≤ (348373743907/781250000000 : ℝ)^817 := by
    have hnat : (5406761741 : ℕ)^1073*781250000000^817 ≤ 348373743907^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406761741 10000000000 348373743907 781250000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1260961571/2500000000 : ℝ)^1073 ≤ (4070284765837/10000000000000 : ℝ)^817 := by
    have hnat : (1260961571 : ℕ)^1073*10000000000000^817 ≤ 4070284765837^817*2500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1260961571 2500000000 4070284765837 10000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (580819397/2500000000 : ℝ)^1073 ≤ (735265655273/5000000000000 : ℝ)^817 := by
    have hnat : (580819397 : ℕ)^1073*5000000000000^817 ≤ 735265655273^817*2500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      580819397 2500000000 735265655273 5000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5406761741/10000000000 : ℝ), (1260961571/2500000000 : ℝ), (-580819397/2500000000 : ℝ)] ![(348373743907/781250000000 : ℝ), (4070284765837/10000000000000 : ℝ), (735265655273/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5406761741/10000000000 : ℝ)|^1073 ≤ (348373743907/781250000000 : ℝ)^817
        have hw : |(5406761741/10000000000 : ℝ)|=(5406761741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1260961571/2500000000 : ℝ)|^1073 ≤ (4070284765837/10000000000000 : ℝ)^817
        have hw : |(1260961571/2500000000 : ℝ)|=(1260961571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-580819397/2500000000 : ℝ)|^1073 ≤ (735265655273/5000000000000 : ℝ)^817
        have hw : |(-580819397/2500000000 : ℝ)|=(580819397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s1_3 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2147043951/5000000000 : ℝ)*x 0 + (927007553/2500000000 : ℝ)*x 1 + (1241471221/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2147043951/5000000000 : ℝ)^1073 ≤ (16474193541899/50000000000000 : ℝ)^817 := by
    have hnat : (2147043951 : ℕ)^1073*50000000000000^817 ≤ 16474193541899^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147043951 5000000000 16474193541899 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (927007553/2500000000 : ℝ)^1073 ≤ (27173023911513/100000000000000 : ℝ)^817 := by
    have hnat : (927007553 : ℕ)^1073*100000000000000^817 ≤ 27173023911513^817*2500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      927007553 2500000000 27173023911513 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1241471221/2500000000 : ℝ)^1073 ≤ (39878588993093/100000000000000 : ℝ)^817 := by
    have hnat : (1241471221 : ℕ)^1073*100000000000000^817 ≤ 39878588993093^817*2500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1241471221 2500000000 39878588993093 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2147043951/5000000000 : ℝ), (927007553/2500000000 : ℝ), (1241471221/2500000000 : ℝ)] ![(16474193541899/50000000000000 : ℝ), (27173023911513/100000000000000 : ℝ), (39878588993093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2147043951/5000000000 : ℝ)|^1073 ≤ (16474193541899/50000000000000 : ℝ)^817
        have hw : |(2147043951/5000000000 : ℝ)|=(2147043951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(927007553/2500000000 : ℝ)|^1073 ≤ (27173023911513/100000000000000 : ℝ)^817
        have hw : |(927007553/2500000000 : ℝ)|=(927007553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1241471221/2500000000 : ℝ)|^1073 ≤ (39878588993093/100000000000000 : ℝ)^817
        have hw : |(1241471221/2500000000 : ℝ)|=(1241471221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s1_4 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-200188899/1000000000 : ℝ)*x 0 + (252573391/500000000 : ℝ)*x 1 + (2819441617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (200188899/1000000000 : ℝ)^1073 ≤ (6046752029371/50000000000000 : ℝ)^817 := by
    have hnat : (200188899 : ℕ)^1073*50000000000000^817 ≤ 6046752029371^817*1000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200188899 1000000000 6046752029371 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (252573391/500000000 : ℝ)^1073 ≤ (2548977682471/6250000000000 : ℝ)^817 := by
    have hnat : (252573391 : ℕ)^1073*6250000000000^817 ≤ 2548977682471^817*500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252573391 500000000 2548977682471 6250000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2819441617/5000000000 : ℝ)^1073 ≤ (2356142650543/5000000000000 : ℝ)^817 := by
    have hnat : (2819441617 : ℕ)^1073*5000000000000^817 ≤ 2356142650543^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2819441617 5000000000 2356142650543 5000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-200188899/1000000000 : ℝ), (252573391/500000000 : ℝ), (2819441617/5000000000 : ℝ)] ![(6046752029371/50000000000000 : ℝ), (2548977682471/6250000000000 : ℝ), (2356142650543/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-200188899/1000000000 : ℝ)|^1073 ≤ (6046752029371/50000000000000 : ℝ)^817
        have hw : |(-200188899/1000000000 : ℝ)|=(200188899/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(252573391/500000000 : ℝ)|^1073 ≤ (2548977682471/6250000000000 : ℝ)^817
        have hw : |(252573391/500000000 : ℝ)|=(252573391/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2819441617/5000000000 : ℝ)|^1073 ≤ (2356142650543/5000000000000 : ℝ)^817
        have hw : |(2819441617/5000000000 : ℝ)|=(2819441617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s1_5 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (52504759/100000000 : ℝ)*x 0 + (-1728240971/10000000000 : ℝ)*x 1 + (5638882663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52504759/100000000 : ℝ)^1073 ≤ (42906718658931/100000000000000 : ℝ)^817 := by
    have hnat : (52504759 : ℕ)^1073*100000000000000^817 ≤ 42906718658931^817*100000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52504759 100000000 42906718658931 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1728240971/10000000000 : ℝ)^1073 ≤ (9970434585177/100000000000000 : ℝ)^817 := by
    have hnat : (1728240971 : ℕ)^1073*100000000000000^817 ≤ 9970434585177^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1728240971 10000000000 9970434585177 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5638882663/10000000000 : ℝ)^1073 ≤ (47122846743967/100000000000000 : ℝ)^817 := by
    have hnat : (5638882663 : ℕ)^1073*100000000000000^817 ≤ 47122846743967^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5638882663 10000000000 47122846743967 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52504759/100000000 : ℝ), (-1728240971/10000000000 : ℝ), (5638882663/10000000000 : ℝ)] ![(42906718658931/100000000000000 : ℝ), (9970434585177/100000000000000 : ℝ), (47122846743967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52504759/100000000 : ℝ)|^1073 ≤ (42906718658931/100000000000000 : ℝ)^817
        have hw : |(52504759/100000000 : ℝ)|=(52504759/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1728240971/10000000000 : ℝ)|^1073 ≤ (9970434585177/100000000000000 : ℝ)^817
        have hw : |(-1728240971/10000000000 : ℝ)|=(1728240971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5638882663/10000000000 : ℝ)|^1073 ≤ (47122846743967/100000000000000 : ℝ)^817
        have hw : |(5638882663/10000000000 : ℝ)|=(5638882663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s1_6 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2625237733/5000000000 : ℝ)*x 0 + (5638882483/10000000000 : ℝ)*x 1 + (-864120923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625237733/5000000000 : ℝ)^1073 ≤ (42906714000989/100000000000000 : ℝ)^817 := by
    have hnat : (2625237733 : ℕ)^1073*100000000000000^817 ≤ 42906714000989^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625237733 5000000000 42906714000989 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5638882483/10000000000 : ℝ)^1073 ≤ (23561422384207/50000000000000 : ℝ)^817 := by
    have hnat : (5638882483 : ℕ)^1073*50000000000000^817 ≤ 23561422384207^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5638882483 10000000000 23561422384207 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (864120923/5000000000 : ℝ)^1073 ≤ (4985220607451/50000000000000 : ℝ)^817 := by
    have hnat : (864120923 : ℕ)^1073*50000000000000^817 ≤ 4985220607451^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864120923 5000000000 4985220607451 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625237733/5000000000 : ℝ), (5638882483/10000000000 : ℝ), (-864120923/5000000000 : ℝ)] ![(42906714000989/100000000000000 : ℝ), (23561422384207/50000000000000 : ℝ), (4985220607451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625237733/5000000000 : ℝ)|^1073 ≤ (42906714000989/100000000000000 : ℝ)^817
        have hw : |(2625237733/5000000000 : ℝ)|=(2625237733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5638882483/10000000000 : ℝ)|^1073 ≤ (23561422384207/50000000000000 : ℝ)^817
        have hw : |(5638882483/10000000000 : ℝ)|=(5638882483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-864120923/5000000000 : ℝ)|^1073 ≤ (4985220607451/50000000000000 : ℝ)^817
        have hw : |(-864120923/5000000000 : ℝ)|=(864120923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s1_7 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2147622801/5000000000 : ℝ)*x 0 + (4949980821/10000000000 : ℝ)*x 1 + (931056631/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2147622801/5000000000 : ℝ)^1073 ≤ (32960053978291/100000000000000 : ℝ)^817 := by
    have hnat : (2147622801 : ℕ)^1073*100000000000000^817 ≤ 32960053978291^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147622801 5000000000 32960053978291 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4949980821/10000000000 : ℝ)^1073 ≤ (9927734053151/25000000000000 : ℝ)^817 := by
    have hnat : (4949980821 : ℕ)^1073*25000000000000^817 ≤ 9927734053151^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4949980821 10000000000 9927734053151 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (931056631/2500000000 : ℝ)^1073 ≤ (27329009798247/100000000000000 : ℝ)^817 := by
    have hnat : (931056631 : ℕ)^1073*100000000000000^817 ≤ 27329009798247^817*2500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931056631 2500000000 27329009798247 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2147622801/5000000000 : ℝ), (4949980821/10000000000 : ℝ), (931056631/2500000000 : ℝ)] ![(32960053978291/100000000000000 : ℝ), (9927734053151/25000000000000 : ℝ), (27329009798247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2147622801/5000000000 : ℝ)|^1073 ≤ (32960053978291/100000000000000 : ℝ)^817
        have hw : |(2147622801/5000000000 : ℝ)|=(2147622801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4949980821/10000000000 : ℝ)|^1073 ≤ (9927734053151/25000000000000 : ℝ)^817
        have hw : |(4949980821/10000000000 : ℝ)|=(4949980821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(931056631/2500000000 : ℝ)|^1073 ≤ (27329009798247/100000000000000 : ℝ)^817
        have hw : |(931056631/2500000000 : ℝ)|=(931056631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1332_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (120574/78125 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26943/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1699/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19537/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26943/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1339/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26943/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1339/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26943/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1339/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26943/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1339/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26943/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1339/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26943/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1339/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1339/100000 : ℝ) ^ (4291/1024 : ℝ) ≤ (141385775639/10000000000000000000 : ℝ) := by
    have hpowers : (1339/100000 : ℝ)^4291 ≤ (141385775639/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1339 : ℕ)^4291*10000000000000000000^1024 ≤ 141385775639^1024*100000^4291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1339 100000 141385775639 10000000000000000000 4291 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1339/100000 : ℝ)) (X := (141385775639/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (26943/100000 : ℝ) ^ (4291/1024 : ℝ) ≤ (410510060417256773/100000000000000000000 : ℝ) := by
    have hpowers : (26943/100000 : ℝ)^4291 ≤ (410510060417256773/100000000000000000000 : ℝ)^1024 := by
      have hnat : (26943 : ℕ)^4291*100000000000000000000^1024 ≤ 410510060417256773^1024*100000^4291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26943 100000 410510060417256773 100000000000000000000 4291 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26943/100000 : ℝ)) (X := (410510060417256773/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000000141385775639/5000000000000000000 : ℝ) ≤ (10000000067480323/10000000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (5000000141385775639/5000000000000000000 : ℝ)^1024 ≤ (10000000067480323/10000000000000000 : ℝ)^4291 := by
      have hnat : (5000000141385775639 : ℕ)^1024*10000000000000000^4291 ≤ 10000000067480323^4291*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000000141385775639 5000000000000000000 10000000067480323 10000000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000067480323/10000000000000000 : ℝ)) (X := (5000000141385775639/5000000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100410511474275013163/100000000000000000000 : ℝ) ≤ (10009781132846779/10000000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (100410511474275013163/100000000000000000000 : ℝ)^1024 ≤ (10009781132846779/10000000000000000 : ℝ)^4291 := by
      have hnat : (100410511474275013163 : ℕ)^1024*10000000000000000^4291 ≤ 10009781132846779^4291*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100410511474275013163 100000000000000000000 10009781132846779 10000000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009781132846779/10000000000000000 : ℝ)) (X := (100410511474275013163/100000000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50410510060417256773/50000000000000000000 : ℝ) ≤ (2003912439642647/2000000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (50410510060417256773/50000000000000000000 : ℝ)^1024 ≤ (2003912439642647/2000000000000000 : ℝ)^4291 := by
      have hnat : (50410510060417256773 : ℕ)^1024*2000000000000000^4291 ≤ 2003912439642647^4291*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50410510060417256773 50000000000000000000 2003912439642647 2000000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2003912439642647/2000000000000000 : ℝ)) (X := (50410510060417256773/50000000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(141385775639/10000000000000000000 : ℝ) ≤ ((64003452008678705231/64010000000000000000 : ℝ)+2*(1222633170807/320050000000000 : ℝ)*(1339/100000 : ℝ))^(4291/1024 : ℝ) := by
    rw [show (64003452008678705231/64010000000000000000 : ℝ)+2*(1222633170807/320050000000000 : ℝ)*(1339/100000 : ℝ)=(10000000067480323/10000000000000000 : ℝ) by norm_num, show 1+2*(141385775639/10000000000000000000 : ℝ)=(5000000141385775639/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(410510060417256773/100000000000000000000 : ℝ)+(141385775639/10000000000000000000 : ℝ) ≤ ((64003452008678705231/64010000000000000000 : ℝ)+(1222633170807/320050000000000 : ℝ)*((26943/100000 : ℝ)+(1339/100000 : ℝ)))^(4291/1024 : ℝ) := by
    rw [show (64003452008678705231/64010000000000000000 : ℝ)+(1222633170807/320050000000000 : ℝ)*((26943/100000 : ℝ)+(1339/100000 : ℝ))=(10009781132846779/10000000000000000 : ℝ) by norm_num, show 1+(410510060417256773/100000000000000000000 : ℝ)+(141385775639/10000000000000000000 : ℝ)=(100410511474275013163/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(410510060417256773/100000000000000000000 : ℝ) ≤ ((64003452008678705231/64010000000000000000 : ℝ)+2*(1222633170807/320050000000000 : ℝ)*(26943/100000 : ℝ))^(4291/1024 : ℝ) := by
    rw [show (64003452008678705231/64010000000000000000 : ℝ)+2*(1222633170807/320050000000000 : ℝ)*(26943/100000 : ℝ)=(2003912439642647/2000000000000000 : ℝ) by norm_num, show 1+2*(410510060417256773/100000000000000000000 : ℝ)=(50410510060417256773/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (64003452008678705231/64010000000000000000 : ℝ)*(X 1 0+X 2 0)+(1222633170807/320050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (1339/100000 : ℝ)) (hi := (26943/100000 : ℝ)) (c := (64003452008678705231/64010000000000000000 : ℝ)) (alpha := (1222633170807/320050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (64003452008678705231/64010000000000000000 : ℝ)*(X 0 1+X 2 1)+(1222633170807/320050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (1339/100000 : ℝ)) (hi := (26943/100000 : ℝ)) (c := (64003452008678705231/64010000000000000000 : ℝ)) (alpha := (1222633170807/320050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (64003452008678705231/64010000000000000000 : ℝ)*(X 0 2+X 1 2)+(1222633170807/320050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (1339/100000 : ℝ)) (hi := (26943/100000 : ℝ)) (c := (64003452008678705231/64010000000000000000 : ℝ)) (alpha := (1222633170807/320050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-100066687/500000000 : ℝ)*X 0 0+(5646644063/10000000000 : ℝ)*X 0 1+(1260961681/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5406761623/10000000000 : ℝ)*X 1 0+(-2323277391/10000000000 : ℝ)*X 1 1+(31524041/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5406761741/10000000000 : ℝ)*X 2 0+(1260961571/2500000000 : ℝ)*X 2 1+(-580819397/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2147043951/5000000000 : ℝ)*X 0 0+(927007553/2500000000 : ℝ)*X 0 1+(1241471221/2500000000 : ℝ)*X 0 2+(2147043951/5000000000 : ℝ)*X 1 0+(927007553/2500000000 : ℝ)*X 1 1+(1241471221/2500000000 : ℝ)*X 1 2+(2147043951/5000000000 : ℝ)*X 2 0+(927007553/2500000000 : ℝ)*X 2 1+(1241471221/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-200188899/1000000000 : ℝ)*X 0 0+(252573391/500000000 : ℝ)*X 0 1+(2819441617/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((52504759/100000000 : ℝ)*X 1 0+(-1728240971/10000000000 : ℝ)*X 1 1+(5638882663/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2625237733/5000000000 : ℝ)*X 2 0+(5638882483/10000000000 : ℝ)*X 2 1+(-864120923/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2147622801/5000000000 : ℝ)*X 0 0+(4949980821/10000000000 : ℝ)*X 0 1+(931056631/2500000000 : ℝ)*X 0 2+(2147622801/5000000000 : ℝ)*X 1 0+(4949980821/10000000000 : ℝ)*X 1 1+(931056631/2500000000 : ℝ)*X 1 2+(2147622801/5000000000 : ℝ)*X 2 0+(4949980821/10000000000 : ℝ)*X 2 1+(931056631/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3645979015240245198744372663/400062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30517571/25000000000000 : ℝ)*(base1) + (1515792403/100000000000000 : ℝ)*(base19) + (775999051/50000000000000 : ℝ)*(base23) + (116782943/50000000000000 : ℝ)*(upper3) + (162234679/100000000000000 : ℝ)*(upper5) + (306744957567291/25000000000000 : ℝ)*(major0) + (306744957567291/25000000000000 : ℝ)*(major1) + (306744957567291/25000000000000 : ℝ)*(major2) + (207367510671017/12500000000000 : ℝ)*(sp0) + (829472827791853/50000000000000 : ℝ)*(sp1) + (1658945619378007/100000000000000 : ℝ)*(sp2) + (795007993124509/100000000000000 : ℝ)*(sp3) + (7208078257/100000000000000 : ℝ)*(sp4) + (4070183301/100000000000000 : ℝ)*(sp7) + (159002437075619/20000000000000 : ℝ)*(f.failure) + (1658947171376109/100000000000000 : ℝ)*(f.sum) + (5418099387223/16002500000000000000000000000 : ℝ)*base65 + (4415126411419349221/1600250000000000000000000000000000 : ℝ)*base67 + (5232660731816900779/1600250000000000000000000000000000 : ℝ)*base70 + (6787095375885900779/1600250000000000000000000000000000 : ℝ)*base72 + (173739673009781/32005000000000000000000000000 : ℝ)*base73 + (12346286875056400779/1600250000000000000000000000000000 : ℝ)*base76 + (5506119813123150779/1600250000000000000000000000000000 : ℝ)*base78 + (13839420904000650779/1600250000000000000000000000000000 : ℝ)*base80 + (30316504172469/8001250000000000000000000000 : ℝ)*base81 + (1097/781250000000000000 : ℝ)*base90 + (1097/781250000000000000 : ℝ)*base92 + (1097/781250000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (263540111396909210798031/32005000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1321233557/100000000000000 : ℝ)*(base19) + (67869389/6250000000000 : ℝ)*(base23) + (5102149/100000000000000 : ℝ)*(upper2) + (93179817/100000000000000 : ℝ)*(upper3) + (22024099/10000000000000 : ℝ)*(upper5) + (1259098609583951/100000000000000 : ℝ)*(major0) + (1259098609583951/100000000000000 : ℝ)*(major1) + (1259098609583951/100000000000000 : ℝ)*(major2) + (1620994523/25000000000000 : ℝ)*(sp1) + (744790163/25000000000000 : ℝ)*(sp2) + (851186821102751/50000000000000 : ℝ)*(sp4) + (1702365836993853/100000000000000 : ℝ)*(sp5) + (851184788567313/50000000000000 : ℝ)*(sp6) + (163164660496867/20000000000000 : ℝ)*(sp7) + (163164660496867/20000000000000 : ℝ)*(f.failure) + (851186821102751/50000000000000 : ℝ)*(f.sum) + (11330260834471/2000312500000000000000000000 : ℝ)*base66 + (19714000158706252319/6401000000000000000000000000000000 : ℝ)*base68 + (20134996060239252319/6401000000000000000000000000000000 : ℝ)*base70 + (10264660804882747681/6401000000000000000000000000000000 : ℝ)*base71 + (74301103556043/16002500000000000000000000000 : ℝ)*base74 + (4454569676769747681/6401000000000000000000000000000000 : ℝ)*base75 + (28751321414749252319/6401000000000000000000000000000000 : ℝ)*base78 + (1195327943007747681/6401000000000000000000000000000000 : ℝ)*base79 + (1320178355963/16002500000000000000000000000 : ℝ)*base82 + (7283/1562500000000000000 : ℝ)*base89 + (7283/1562500000000000000 : ℝ)*base91 + (7283/1562500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1332_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (120574/78125 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26943/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1699/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19537/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1332_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1332_s2_0 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2042365213/10000000000 : ℝ)*x 0 + (342657307/625000000 : ℝ)*x 1 + (1036341147/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2042365213/10000000000 : ℝ)^1073 ≤ (2483130653417/20000000000000 : ℝ)^817 := by
    have hnat : (2042365213 : ℕ)^1073*20000000000000^817 ≤ 2483130653417^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042365213 10000000000 2483130653417 20000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (342657307/625000000 : ℝ)^1073 ≤ (11353547620411/25000000000000 : ℝ)^817 := by
    have hnat : (342657307 : ℕ)^1073*25000000000000^817 ≤ 11353547620411^817*625000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342657307 625000000 11353547620411 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036341147/2000000000 : ℝ)^1073 ≤ (21085078116581/50000000000000 : ℝ)^817 := by
    have hnat : (1036341147 : ℕ)^1073*50000000000000^817 ≤ 21085078116581^817*2000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036341147 2000000000 21085078116581 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2042365213/10000000000 : ℝ), (342657307/625000000 : ℝ), (1036341147/2000000000 : ℝ)] ![(2483130653417/20000000000000 : ℝ), (11353547620411/25000000000000 : ℝ), (21085078116581/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2042365213/10000000000 : ℝ)|^1073 ≤ (2483130653417/20000000000000 : ℝ)^817
        have hw : |(-2042365213/10000000000 : ℝ)|=(2042365213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(342657307/625000000 : ℝ)|^1073 ≤ (11353547620411/25000000000000 : ℝ)^817
        have hw : |(342657307/625000000 : ℝ)|=(342657307/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036341147/2000000000 : ℝ)|^1073 ≤ (21085078116581/50000000000000 : ℝ)^817
        have hw : |(1036341147/2000000000 : ℝ)|=(1036341147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s2_1 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2683330713/5000000000 : ℝ)*x 0 + (-1098941941/5000000000 : ℝ)*x 1 + (207268211/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683330713/5000000000 : ℝ)^1073 ≤ (8831598202409/20000000000000 : ℝ)^817 := by
    have hnat : (2683330713 : ℕ)^1073*20000000000000^817 ≤ 8831598202409^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683330713 5000000000 8831598202409 20000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098941941/5000000000 : ℝ)^1073 ≤ (1367185765737/10000000000000 : ℝ)^817 := by
    have hnat : (1098941941 : ℕ)^1073*10000000000000^817 ≤ 1367185765737^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098941941 5000000000 1367185765737 10000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207268211/400000000 : ℝ)^1073 ≤ (42170151316527/100000000000000 : ℝ)^817 := by
    have hnat : (207268211 : ℕ)^1073*100000000000000^817 ≤ 42170151316527^817*400000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207268211 400000000 42170151316527 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683330713/5000000000 : ℝ), (-1098941941/5000000000 : ℝ), (207268211/400000000 : ℝ)] ![(8831598202409/20000000000000 : ℝ), (1367185765737/10000000000000 : ℝ), (42170151316527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683330713/5000000000 : ℝ)|^1073 ≤ (8831598202409/20000000000000 : ℝ)^817
        have hw : |(2683330713/5000000000 : ℝ)|=(2683330713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1098941941/5000000000 : ℝ)|^1073 ≤ (1367185765737/10000000000000 : ℝ)^817
        have hw : |(-1098941941/5000000000 : ℝ)|=(1098941941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207268211/400000000 : ℝ)|^1073 ≤ (42170151316527/100000000000000 : ℝ)^817
        have hw : |(207268211/400000000 : ℝ)|=(207268211/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s2_2 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2683330427/5000000000 : ℝ)*x 0 + (647713229/1250000000 : ℝ)*x 1 + (-2197883909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683330427/5000000000 : ℝ)^1073 ≤ (1103949620769/2500000000000 : ℝ)^817 := by
    have hnat : (2683330427 : ℕ)^1073*2500000000000^817 ≤ 1103949620769^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683330427 5000000000 1103949620769 2500000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647713229/1250000000 : ℝ)^1073 ≤ (4217015726993/10000000000000 : ℝ)^817 := by
    have hnat : (647713229 : ℕ)^1073*10000000000000^817 ≤ 4217015726993^817*1250000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647713229 1250000000 4217015726993 10000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2197883909/10000000000 : ℝ)^1073 ≤ (13671857877949/100000000000000 : ℝ)^817 := by
    have hnat : (2197883909 : ℕ)^1073*100000000000000^817 ≤ 13671857877949^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197883909 10000000000 13671857877949 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683330427/5000000000 : ℝ), (647713229/1250000000 : ℝ), (-2197883909/10000000000 : ℝ)] ![(1103949620769/2500000000000 : ℝ), (4217015726993/10000000000000 : ℝ), (13671857877949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683330427/5000000000 : ℝ)|^1073 ≤ (1103949620769/2500000000000 : ℝ)^817
        have hw : |(2683330427/5000000000 : ℝ)|=(2683330427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(647713229/1250000000 : ℝ)|^1073 ≤ (4217015726993/10000000000000 : ℝ)^817
        have hw : |(647713229/1250000000 : ℝ)|=(647713229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2197883909/10000000000 : ℝ)|^1073 ≤ (13671857877949/100000000000000 : ℝ)^817
        have hw : |(-2197883909/10000000000 : ℝ)|=(2197883909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s2_3 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (135085901/312500000 : ℝ)*x 0 + (803911371/2000000000 : ℝ)*x 1 + (4647267649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135085901/312500000 : ℝ)^1073 ≤ (3323751124543/10000000000000 : ℝ)^817 := by
    have hnat : (135085901 : ℕ)^1073*10000000000000^817 ≤ 3323751124543^817*312500000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135085901 312500000 3323751124543 10000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (803911371/2000000000 : ℝ)^1073 ≤ (6042000685527/20000000000000 : ℝ)^817 := by
    have hnat : (803911371 : ℕ)^1073*20000000000000^817 ≤ 6042000685527^817*2000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803911371 2000000000 6042000685527 20000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4647267649/10000000000 : ℝ)^1073 ≤ (9138121326677/25000000000000 : ℝ)^817 := by
    have hnat : (4647267649 : ℕ)^1073*25000000000000^817 ≤ 9138121326677^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4647267649 10000000000 9138121326677 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135085901/312500000 : ℝ), (803911371/2000000000 : ℝ), (4647267649/10000000000 : ℝ)] ![(3323751124543/10000000000000 : ℝ), (6042000685527/20000000000000 : ℝ), (9138121326677/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135085901/312500000 : ℝ)|^1073 ≤ (3323751124543/10000000000000 : ℝ)^817
        have hw : |(135085901/312500000 : ℝ)|=(135085901/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(803911371/2000000000 : ℝ)|^1073 ≤ (6042000685527/20000000000000 : ℝ)^817
        have hw : |(803911371/2000000000 : ℝ)|=(803911371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4647267649/10000000000 : ℝ)|^1073 ≤ (9138121326677/25000000000000 : ℝ)^817
        have hw : |(4647267649/10000000000 : ℝ)|=(4647267649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s2_4 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2042433789/10000000000 : ℝ)*x 0 + (1295903167/2500000000 : ℝ)*x 1 + (5480592861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2042433789/10000000000 : ℝ)^1073 ≤ (12416200772313/100000000000000 : ℝ)^817 := by
    have hnat : (2042433789 : ℕ)^1073*100000000000000^817 ≤ 12416200772313^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042433789 10000000000 12416200772313 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295903167/2500000000 : ℝ)^1073 ≤ (42190539350329/100000000000000 : ℝ)^817 := by
    have hnat : (1295903167 : ℕ)^1073*100000000000000^817 ≤ 42190539350329^817*2500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295903167 2500000000 42190539350329 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5480592861/10000000000 : ℝ)^1073 ≤ (11348314967003/25000000000000 : ℝ)^817 := by
    have hnat : (5480592861 : ℕ)^1073*25000000000000^817 ≤ 11348314967003^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480592861 10000000000 11348314967003 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2042433789/10000000000 : ℝ), (1295903167/2500000000 : ℝ), (5480592861/10000000000 : ℝ)] ![(12416200772313/100000000000000 : ℝ), (42190539350329/100000000000000 : ℝ), (11348314967003/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2042433789/10000000000 : ℝ)|^1073 ≤ (12416200772313/100000000000000 : ℝ)^817
        have hw : |(-2042433789/10000000000 : ℝ)|=(2042433789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295903167/2500000000 : ℝ)|^1073 ≤ (42190539350329/100000000000000 : ℝ)^817
        have hw : |(1295903167/2500000000 : ℝ)|=(1295903167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5480592861/10000000000 : ℝ)|^1073 ≤ (11348314967003/25000000000000 : ℝ)^817
        have hw : |(5480592861/10000000000 : ℝ)|=(5480592861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s2_5 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1322302943/2500000000 : ℝ)*x 0 + (-474748909/2500000000 : ℝ)*x 1 + (5480592889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322302943/2500000000 : ℝ)^1073 ≤ (5415366797761/12500000000000 : ℝ)^817 := by
    have hnat : (1322302943 : ℕ)^1073*12500000000000^817 ≤ 5415366797761^817*2500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322302943 2500000000 5415366797761 12500000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (474748909/2500000000 : ℝ)^1073 ≤ (5641902717539/50000000000000 : ℝ)^817 := by
    have hnat : (474748909 : ℕ)^1073*50000000000000^817 ≤ 5641902717539^817*2500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474748909 2500000000 5641902717539 50000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5480592889/10000000000 : ℝ)^1073 ≤ (4539326017259/10000000000000 : ℝ)^817 := by
    have hnat : (5480592889 : ℕ)^1073*10000000000000^817 ≤ 4539326017259^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480592889 10000000000 4539326017259 10000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322302943/2500000000 : ℝ), (-474748909/2500000000 : ℝ), (5480592889/10000000000 : ℝ)] ![(5415366797761/12500000000000 : ℝ), (5641902717539/50000000000000 : ℝ), (4539326017259/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322302943/2500000000 : ℝ)|^1073 ≤ (5415366797761/12500000000000 : ℝ)^817
        have hw : |(1322302943/2500000000 : ℝ)|=(1322302943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-474748909/2500000000 : ℝ)|^1073 ≤ (5641902717539/50000000000000 : ℝ)^817
        have hw : |(-474748909/2500000000 : ℝ)|=(474748909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5480592889/10000000000 : ℝ)|^1073 ≤ (4539326017259/10000000000000 : ℝ)^817
        have hw : |(5480592889/10000000000 : ℝ)|=(5480592889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s2_6 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (264460591/500000000 : ℝ)*x 0 + (1370148217/2500000000 : ℝ)*x 1 + (-949497799/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264460591/500000000 : ℝ)^1073 ≤ (1083073372461/2500000000000 : ℝ)^817 := by
    have hnat : (264460591 : ℕ)^1073*2500000000000^817 ≤ 1083073372461^817*500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264460591 500000000 1083073372461 2500000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1370148217/2500000000 : ℝ)^1073 ≤ (11348314986039/25000000000000 : ℝ)^817 := by
    have hnat : (1370148217 : ℕ)^1073*25000000000000^817 ≤ 11348314986039^817*2500000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370148217 2500000000 11348314986039 25000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (949497799/5000000000 : ℝ)^1073 ≤ (11283805138531/100000000000000 : ℝ)^817 := by
    have hnat : (949497799 : ℕ)^1073*100000000000000^817 ≤ 11283805138531^817*5000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949497799 5000000000 11283805138531 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264460591/500000000 : ℝ), (1370148217/2500000000 : ℝ), (-949497799/5000000000 : ℝ)] ![(1083073372461/2500000000000 : ℝ), (11348314986039/25000000000000 : ℝ), (11283805138531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264460591/500000000 : ℝ)|^1073 ≤ (1083073372461/2500000000000 : ℝ)^817
        have hw : |(264460591/500000000 : ℝ)|=(264460591/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1370148217/2500000000 : ℝ)|^1073 ≤ (11348314986039/25000000000000 : ℝ)^817
        have hw : |(1370148217/2500000000 : ℝ)|=(1370148217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-949497799/5000000000 : ℝ)|^1073 ≤ (11283805138531/100000000000000 : ℝ)^817
        have hw : |(-949497799/5000000000 : ℝ)|=(949497799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1332_s2_7 (p : ℝ) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4322889983/10000000000 : ℝ)*x 0 + (580410729/1250000000 : ℝ)*x 1 + (62868411/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322889983/10000000000 : ℝ)^1073 ≤ (33238936630947/100000000000000 : ℝ)^817 := by
    have hnat : (4322889983 : ℕ)^1073*100000000000000^817 ≤ 33238936630947^817*10000000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322889983 10000000000 33238936630947 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (580410729/1250000000 : ℝ)^1073 ≤ (4563919873059/12500000000000 : ℝ)^817 := by
    have hnat : (580410729 : ℕ)^1073*12500000000000^817 ≤ 4563919873059^817*1250000000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      580410729 1250000000 4563919873059 12500000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62868411/156250000 : ℝ)^1073 ≤ (30249704376049/100000000000000 : ℝ)^817 := by
    have hnat : (62868411 : ℕ)^1073*100000000000000^817 ≤ 30249704376049^817*156250000^1073 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62868411 156250000 30249704376049 100000000000000 1073 817 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1073/256 : ℝ)) 1073 817 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322889983/10000000000 : ℝ), (580410729/1250000000 : ℝ), (62868411/156250000 : ℝ)] ![(33238936630947/100000000000000 : ℝ), (4563919873059/12500000000000 : ℝ), (30249704376049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322889983/10000000000 : ℝ)|^1073 ≤ (33238936630947/100000000000000 : ℝ)^817
        have hw : |(4322889983/10000000000 : ℝ)|=(4322889983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(580410729/1250000000 : ℝ)|^1073 ≤ (4563919873059/12500000000000 : ℝ)^817
        have hw : |(580410729/1250000000 : ℝ)|=(580410729/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(62868411/156250000 : ℝ)|^1073 ≤ (30249704376049/100000000000000 : ℝ)^817
        have hw : |(62868411/156250000 : ℝ)|=(62868411/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1332_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (120574/78125 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19537/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1699/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1957/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1009/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19537/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1699/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19537/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1699/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19537/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1699/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19537/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1699/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19537/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1699/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19537/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1699/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1699/25000 : ℝ) ^ (4291/1024 : ℝ) ≤ (255664159683341/20000000000000000000 : ℝ) := by
    have hpowers : (1699/25000 : ℝ)^4291 ≤ (255664159683341/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1699 : ℕ)^4291*20000000000000000000^1024 ≤ 255664159683341^1024*25000^4291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1699 25000 255664159683341 20000000000000000000 4291 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1699/25000 : ℝ)) (X := (255664159683341/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19537/100000 : ℝ) ^ (4291/1024 : ℝ) ≤ (53377692736782177/50000000000000000000 : ℝ) := by
    have hpowers : (19537/100000 : ℝ)^4291 ≤ (53377692736782177/50000000000000000000 : ℝ)^1024 := by
      have hnat : (19537 : ℕ)^4291*50000000000000000000^1024 ≤ 53377692736782177^1024*100000^4291 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19537 100000 53377692736782177 50000000000000000000 4291 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19537/100000 : ℝ)) (X := (53377692736782177/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000255664159683341/10000000000000000000 : ℝ) ≤ (10000061010848649/10000000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (10000255664159683341/10000000000000000000 : ℝ)^1024 ≤ (10000061010848649/10000000000000000 : ℝ)^4291 := by
      have hnat : (10000255664159683341 : ℕ)^1024*10000000000000000^4291 ≤ 10000061010848649^4291*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000255664159683341 10000000000000000000 10000061010848649 10000000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000061010848649/10000000000000000 : ℝ)) (X := (10000255664159683341/10000000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100108033706271981059/100000000000000000000 : ℝ) ≤ (10002577046083411/10000000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (100108033706271981059/100000000000000000000 : ℝ)^1024 ≤ (10002577046083411/10000000000000000 : ℝ)^4291 := by
      have hnat : (100108033706271981059 : ℕ)^1024*10000000000000000^4291 ≤ 10002577046083411^4291*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100108033706271981059 100000000000000000000 10002577046083411 10000000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002577046083411/10000000000000000 : ℝ)) (X := (100108033706271981059/100000000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25053377692736782177/25000000000000000000 : ℝ) ≤ (10005093081318173/10000000000000000 : ℝ) ^ (4291/1024 : ℝ) := by
    have hpowers : (25053377692736782177/25000000000000000000 : ℝ)^1024 ≤ (10005093081318173/10000000000000000 : ℝ)^4291 := by
      have hnat : (25053377692736782177 : ℕ)^1024*10000000000000000^4291 ≤ 10005093081318173^4291*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25053377692736782177 25000000000000000000 10005093081318173 10000000000000000 1024 4291 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005093081318173/10000000000000000 : ℝ)) (X := (25053377692736782177/25000000000000000000 : ℝ)) (by norm_num) 4291 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(255664159683341/20000000000000000000 : ℝ) ≤ ((25475315877662350361/25482000000000000000 : ℝ)+2*(1258017617381/637050000000000 : ℝ)*(1699/25000 : ℝ))^(4291/1024 : ℝ) := by
    rw [show (25475315877662350361/25482000000000000000 : ℝ)+2*(1258017617381/637050000000000 : ℝ)*(1699/25000 : ℝ)=(10000061010848649/10000000000000000 : ℝ) by norm_num, show 1+2*(255664159683341/20000000000000000000 : ℝ)=(10000255664159683341/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(53377692736782177/50000000000000000000 : ℝ)+(255664159683341/20000000000000000000 : ℝ) ≤ ((25475315877662350361/25482000000000000000 : ℝ)+(1258017617381/637050000000000 : ℝ)*((19537/100000 : ℝ)+(1699/25000 : ℝ)))^(4291/1024 : ℝ) := by
    rw [show (25475315877662350361/25482000000000000000 : ℝ)+(1258017617381/637050000000000 : ℝ)*((19537/100000 : ℝ)+(1699/25000 : ℝ))=(10002577046083411/10000000000000000 : ℝ) by norm_num, show 1+(53377692736782177/50000000000000000000 : ℝ)+(255664159683341/20000000000000000000 : ℝ)=(100108033706271981059/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(53377692736782177/50000000000000000000 : ℝ) ≤ ((25475315877662350361/25482000000000000000 : ℝ)+2*(1258017617381/637050000000000 : ℝ)*(19537/100000 : ℝ))^(4291/1024 : ℝ) := by
    rw [show (25475315877662350361/25482000000000000000 : ℝ)+2*(1258017617381/637050000000000 : ℝ)*(19537/100000 : ℝ)=(10005093081318173/10000000000000000 : ℝ) by norm_num, show 1+2*(53377692736782177/50000000000000000000 : ℝ)=(25053377692736782177/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (25475315877662350361/25482000000000000000 : ℝ)*(X 1 0+X 2 0)+(1258017617381/637050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (1699/25000 : ℝ)) (hi := (19537/100000 : ℝ)) (c := (25475315877662350361/25482000000000000000 : ℝ)) (alpha := (1258017617381/637050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (25475315877662350361/25482000000000000000 : ℝ)*(X 0 1+X 2 1)+(1258017617381/637050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (1699/25000 : ℝ)) (hi := (19537/100000 : ℝ)) (c := (25475315877662350361/25482000000000000000 : ℝ)) (alpha := (1258017617381/637050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (25475315877662350361/25482000000000000000 : ℝ)*(X 0 2+X 1 2)+(1258017617381/637050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4291/1024 : ℝ)) (lo := (1699/25000 : ℝ)) (hi := (19537/100000 : ℝ)) (c := (25475315877662350361/25482000000000000000 : ℝ)) (alpha := (1258017617381/637050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2042365213/10000000000 : ℝ)*X 0 0+(342657307/625000000 : ℝ)*X 0 1+(1036341147/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2683330713/5000000000 : ℝ)*X 1 0+(-1098941941/5000000000 : ℝ)*X 1 1+(207268211/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2683330427/5000000000 : ℝ)*X 2 0+(647713229/1250000000 : ℝ)*X 2 1+(-2197883909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((135085901/312500000 : ℝ)*X 0 0+(803911371/2000000000 : ℝ)*X 0 1+(4647267649/10000000000 : ℝ)*X 0 2+(135085901/312500000 : ℝ)*X 1 0+(803911371/2000000000 : ℝ)*X 1 1+(4647267649/10000000000 : ℝ)*X 1 2+(135085901/312500000 : ℝ)*X 2 0+(803911371/2000000000 : ℝ)*X 2 1+(4647267649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2042433789/10000000000 : ℝ)*X 0 0+(1295903167/2500000000 : ℝ)*X 0 1+(5480592861/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1322302943/2500000000 : ℝ)*X 1 0+(-474748909/2500000000 : ℝ)*X 1 1+(5480592889/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((264460591/500000000 : ℝ)*X 2 0+(1370148217/2500000000 : ℝ)*X 2 1+(-949497799/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4322889983/10000000000 : ℝ)*X 0 0+(580410729/1250000000 : ℝ)*X 0 1+(62868411/156250000 : ℝ)*X 0 2+(4322889983/10000000000 : ℝ)*X 1 0+(580410729/1250000000 : ℝ)*X 1 1+(62868411/156250000 : ℝ)*X 1 2+(4322889983/10000000000 : ℝ)*X 2 0+(580410729/1250000000 : ℝ)*X 2 1+(62868411/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1332_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27770237490355168239063219/3397600000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2755396479/100000000000000 : ℝ)*(base19) + (1664593373/100000000000000 : ℝ)*(base23) + (395242927/100000000000000 : ℝ)*(lower2) + (892701991/100000000000000 : ℝ)*(upper3) + (96951623/50000000000000 : ℝ)*(upper5) + (19670022080821/800000000000 : ℝ)*(major0) + (19670022080821/800000000000 : ℝ)*(major1) + (19670022080821/800000000000 : ℝ)*(major2) + (831091447393309/25000000000000 : ℝ)*(sp0) + (1662186234721843/50000000000000 : ℝ)*(sp1) + (415546695030849/12500000000000 : ℝ)*(sp2) + (1593106444297341/100000000000000 : ℝ)*(sp3) + (9435266929/100000000000000 : ℝ)*(sp4) + (23578618193/100000000000000 : ℝ)*(sp7) + (796565011457767/50000000000000 : ℝ)*(f.failure) + (664875044968033/20000000000000 : ℝ)*(f.sum) + (2339240484547/3185250000000000000000000000 : ℝ)*base65 + (73947188144830381/20385600000000000000000000000000 : ℝ)*base67 + (42265417131769619/20385600000000000000000000000000 : ℝ)*base70 + (110537612832171181/20385600000000000000000000000000 : ℝ)*base71 + (42744983088511/12741000000000000000000000000 : ℝ)*base73 + (137716164354852781/20385600000000000000000000000000 : ℝ)*base75 + (9126351113128019/20385600000000000000000000000000 : ℝ)*base78 + (141071523135646381/20385600000000000000000000000000 : ℝ)*base79 + (26206008661223/12741000000000000000000000000 : ℝ)*base82 + (18391/7812500000000000000 : ℝ)*base89 + (18391/7812500000000000000 : ℝ)*base91 + (18391/7812500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6647241215077843257087651/1698800000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42211861/5000000000000 : ℝ)*(base19) + (102700341/10000000000000 : ℝ)*(base23) + (5910097/5000000000000 : ℝ)*(upper3) + (7037473/12500000000000 : ℝ)*(lower4) + (213429/625000000000 : ℝ)*(upper5) + (9961781768697/400000000000 : ℝ)*(major0) + (9961781768697/400000000000 : ℝ)*(major1) + (9961781768697/400000000000 : ℝ)*(major2) + (9126221637/100000000000000 : ℝ)*(sp1) + (12251762471/100000000000000 : ℝ)*(sp2) + (1683612850171219/50000000000000 : ℝ)*(sp4) + (1683607864941791/50000000000000 : ℝ)*(sp5) + (1683606210788279/50000000000000 : ℝ)*(sp6) + (1613665053575923/100000000000000 : ℝ)*(sp7) + (1613665053575923/100000000000000 : ℝ)*(f.failure) + (1683612850171219/50000000000000 : ℝ)*(f.sum) + (4331072062669/4247000000000000000000000000 : ℝ)*base66 + (4039662042375461/3397600000000000000000000000000 : ℝ)*base68 + (4097700491119461/3397600000000000000000000000000 : ℝ)*base70 + (27163909261083461/3397600000000000000000000000000 : ℝ)*base72 + (49788874497/16988000000000000000000000 : ℝ)*base73 + (40149458961827461/3397600000000000000000000000000 : ℝ)*base76 + (29583422198376261/3397600000000000000000000000000 : ℝ)*base78 + (30525362796058661/3397600000000000000000000000000 : ℝ)*base80 + (21100974544957/4247000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (7319/976562500000000000 : ℝ)*base89 + (7319/976562500000000000 : ℝ)*base91 + (7319/976562500000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1332_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (120574/78125 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19537/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1699/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1957/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1009/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1332_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1332_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (120574/78125 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1957/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1009/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1332_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1332_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1332_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4291/1024 : ℝ) ≤ p) (hpb : p ≤ (1073/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (120574/78125 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1957/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1009/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1332_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
