-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1238_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:18:00.540258+00:00
-- url     : https://prove2.me/submissions/094e89a9-a840-4acf-b21a-fc73f6cb99bf

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
theorem support_rectangle_w1238_box_0 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1997984967/10000000000 : ℝ)*x 0 + (1343726017/2500000000 : ℝ)*x 1 + (1074980887/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1997984967/10000000000 : ℝ)^8431 ≤ (11917513305581/100000000000000 : ℝ)^6383 := by
    have hnat : (1997984967 : ℕ)^8431*100000000000000^6383 ≤ 11917513305581^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997984967 10000000000 11917513305581 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1343726017/2500000000 : ℝ)^8431 ≤ (44041241353577/100000000000000 : ℝ)^6383 := by
    have hnat : (1343726017 : ℕ)^8431*100000000000000^6383 ≤ 44041241353577^6383*2500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343726017 2500000000 44041241353577 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1074980887/2000000000 : ℝ)^8431 ≤ (5505155665697/12500000000000 : ℝ)^6383 := by
    have hnat : (1074980887 : ℕ)^8431*12500000000000^6383 ≤ 5505155665697^6383*2000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074980887 2000000000 5505155665697 12500000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1997984967/10000000000 : ℝ), (1343726017/2500000000 : ℝ), (1074980887/2000000000 : ℝ)] ![(11917513305581/100000000000000 : ℝ), (44041241353577/100000000000000 : ℝ), (5505155665697/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1997984967/10000000000 : ℝ)|^8431 ≤ (11917513305581/100000000000000 : ℝ)^6383
        have hw : |(-1997984967/10000000000 : ℝ)|=(1997984967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1343726017/2500000000 : ℝ)|^8431 ≤ (44041241353577/100000000000000 : ℝ)^6383
        have hw : |(1343726017/2500000000 : ℝ)|=(1343726017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1074980887/2000000000 : ℝ)|^8431 ≤ (5505155665697/12500000000000 : ℝ)^6383
        have hw : |(1074980887/2000000000 : ℝ)|=(1074980887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_box_1 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296766331/10000000000 : ℝ)*x 0 + (-2104178161/10000000000 : ℝ)*x 1 + (5374904073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296766331/10000000000 : ℝ)^8431 ≤ (43197544356443/100000000000000 : ℝ)^6383 := by
    have hnat : (5296766331 : ℕ)^8431*100000000000000^6383 ≤ 43197544356443^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296766331 10000000000 43197544356443 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2104178161/10000000000 : ℝ)^8431 ≤ (6380607112639/50000000000000 : ℝ)^6383 := by
    have hnat : (2104178161 : ℕ)^8431*50000000000000^6383 ≤ 6380607112639^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104178161 10000000000 6380607112639 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5374904073/10000000000 : ℝ)^8431 ≤ (44041241407691/100000000000000 : ℝ)^6383 := by
    have hnat : (5374904073 : ℕ)^8431*100000000000000^6383 ≤ 44041241407691^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374904073 10000000000 44041241407691 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296766331/10000000000 : ℝ), (-2104178161/10000000000 : ℝ), (5374904073/10000000000 : ℝ)] ![(43197544356443/100000000000000 : ℝ), (6380607112639/50000000000000 : ℝ), (44041241407691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296766331/10000000000 : ℝ)|^8431 ≤ (43197544356443/100000000000000 : ℝ)^6383
        have hw : |(5296766331/10000000000 : ℝ)|=(5296766331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2104178161/10000000000 : ℝ)|^8431 ≤ (6380607112639/50000000000000 : ℝ)^6383
        have hw : |(-2104178161/10000000000 : ℝ)|=(2104178161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5374904073/10000000000 : ℝ)|^8431 ≤ (44041241407691/100000000000000 : ℝ)^6383
        have hw : |(5374904073/10000000000 : ℝ)|=(5374904073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_box_2 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2648383347/5000000000 : ℝ)*x 0 + (1343726019/2500000000 : ℝ)*x 1 + (-2104177669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648383347/5000000000 : ℝ)^8431 ≤ (21598774133367/50000000000000 : ℝ)^6383 := by
    have hnat : (2648383347 : ℕ)^8431*50000000000000^6383 ≤ 21598774133367^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648383347 5000000000 21598774133367 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1343726019/2500000000 : ℝ)^8431 ≤ (275257759001/625000000000 : ℝ)^6383 := by
    have hnat : (1343726019 : ℕ)^8431*625000000000^6383 ≤ 275257759001^6383*2500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343726019 2500000000 275257759001 625000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2104177669/10000000000 : ℝ)^8431 ≤ (510448411363/4000000000000 : ℝ)^6383 := by
    have hnat : (2104177669 : ℕ)^8431*4000000000000^6383 ≤ 510448411363^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104177669 10000000000 510448411363 4000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648383347/5000000000 : ℝ), (1343726019/2500000000 : ℝ), (-2104177669/10000000000 : ℝ)] ![(21598774133367/50000000000000 : ℝ), (275257759001/625000000000 : ℝ), (510448411363/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648383347/5000000000 : ℝ)|^8431 ≤ (21598774133367/50000000000000 : ℝ)^6383
        have hw : |(2648383347/5000000000 : ℝ)|=(2648383347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1343726019/2500000000 : ℝ)|^8431 ≤ (275257759001/625000000000 : ℝ)^6383
        have hw : |(1343726019/2500000000 : ℝ)|=(1343726019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2104177669/10000000000 : ℝ)|^8431 ≤ (510448411363/4000000000000 : ℝ)^6383
        have hw : |(-2104177669/10000000000 : ℝ)|=(2104177669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_box_3 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2228947181/5000000000 : ℝ)*x 0 + (2150041807/5000000000 : ℝ)*x 1 + (2150041419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2228947181/5000000000 : ℝ)^8431 ≤ (17199755388803/50000000000000 : ℝ)^6383 := by
    have hnat : (2228947181 : ℕ)^8431*50000000000000^6383 ≤ 17199755388803^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228947181 5000000000 17199755388803 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2150041807/5000000000 : ℝ)^8431 ≤ (16400124255471/50000000000000 : ℝ)^6383 := by
    have hnat : (2150041807 : ℕ)^8431*50000000000000^6383 ≤ 16400124255471^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150041807 5000000000 16400124255471 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2150041419/5000000000 : ℝ)^8431 ≤ (32800240692573/100000000000000 : ℝ)^6383 := by
    have hnat : (2150041419 : ℕ)^8431*100000000000000^6383 ≤ 32800240692573^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150041419 5000000000 32800240692573 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2228947181/5000000000 : ℝ), (2150041807/5000000000 : ℝ), (2150041419/5000000000 : ℝ)] ![(17199755388803/50000000000000 : ℝ), (16400124255471/50000000000000 : ℝ), (32800240692573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2228947181/5000000000 : ℝ)|^8431 ≤ (17199755388803/50000000000000 : ℝ)^6383
        have hw : |(2228947181/5000000000 : ℝ)|=(2228947181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2150041807/5000000000 : ℝ)|^8431 ≤ (16400124255471/50000000000000 : ℝ)^6383
        have hw : |(2150041807/5000000000 : ℝ)|=(2150041807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2150041419/5000000000 : ℝ)|^8431 ≤ (32800240692573/100000000000000 : ℝ)^6383
        have hw : |(2150041419/5000000000 : ℝ)|=(2150041419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_box_4 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-112350629/500000000 : ℝ)*x 0 + (5282242741/10000000000 : ℝ)*x 1 + (5282242753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (112350629/500000000 : ℝ)^8431 ≤ (13917674073629/100000000000000 : ℝ)^6383 := by
    have hnat : (112350629 : ℕ)^8431*100000000000000^6383 ≤ 13917674073629^6383*500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112350629 500000000 13917674073629 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5282242741/10000000000 : ℝ)^8431 ≤ (43041162894047/100000000000000 : ℝ)^6383 := by
    have hnat : (5282242741 : ℕ)^8431*100000000000000^6383 ≤ 43041162894047^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282242741 10000000000 43041162894047 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282242753/10000000000 : ℝ)^8431 ≤ (43041163023199/100000000000000 : ℝ)^6383 := by
    have hnat : (5282242753 : ℕ)^8431*100000000000000^6383 ≤ 43041163023199^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282242753 10000000000 43041163023199 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-112350629/500000000 : ℝ), (5282242741/10000000000 : ℝ), (5282242753/10000000000 : ℝ)] ![(13917674073629/100000000000000 : ℝ), (43041162894047/100000000000000 : ℝ), (43041163023199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-112350629/500000000 : ℝ)|^8431 ≤ (13917674073629/100000000000000 : ℝ)^6383
        have hw : |(-112350629/500000000 : ℝ)|=(112350629/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5282242741/10000000000 : ℝ)|^8431 ≤ (43041162894047/100000000000000 : ℝ)^6383
        have hw : |(5282242741/10000000000 : ℝ)|=(5282242741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282242753/10000000000 : ℝ)|^8431 ≤ (43041163023199/100000000000000 : ℝ)^6383
        have hw : |(5282242753/10000000000 : ℝ)|=(5282242753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_box_5 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5362091363/10000000000 : ℝ)*x 0 + (-267612747/1250000000 : ℝ)*x 1 + (52822427/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362091363/10000000000 : ℝ)^8431 ≤ (43902623969111/100000000000000 : ℝ)^6383 := by
    have hnat : (5362091363 : ℕ)^8431*100000000000000^6383 ≤ 43902623969111^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362091363 10000000000 43902623969111 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (267612747/1250000000 : ℝ)^8431 ≤ (652810678327/5000000000000 : ℝ)^6383 := by
    have hnat : (267612747 : ℕ)^8431*5000000000000^6383 ≤ 652810678327^6383*1250000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267612747 1250000000 652810678327 5000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52822427/100000000 : ℝ)^8431 ≤ (43041162452777/100000000000000 : ℝ)^6383 := by
    have hnat : (52822427 : ℕ)^8431*100000000000000^6383 ≤ 43041162452777^6383*100000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52822427 100000000 43041162452777 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362091363/10000000000 : ℝ), (-267612747/1250000000 : ℝ), (52822427/100000000 : ℝ)] ![(43902623969111/100000000000000 : ℝ), (652810678327/5000000000000 : ℝ), (43041162452777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362091363/10000000000 : ℝ)|^8431 ≤ (43902623969111/100000000000000 : ℝ)^6383
        have hw : |(5362091363/10000000000 : ℝ)|=(5362091363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-267612747/1250000000 : ℝ)|^8431 ≤ (652810678327/5000000000000 : ℝ)^6383
        have hw : |(-267612747/1250000000 : ℝ)|=(267612747/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52822427/100000000 : ℝ)|^8431 ≤ (43041162452777/100000000000000 : ℝ)^6383
        have hw : |(52822427/100000000 : ℝ)|=(52822427/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_box_6 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (53620913/100000000 : ℝ)*x 0 + (528224281/1000000000 : ℝ)*x 1 + (-2140901913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53620913/100000000 : ℝ)^8431 ≤ (2743913955487/6250000000000 : ℝ)^6383 := by
    have hnat : (53620913 : ℕ)^8431*6250000000000^6383 ≤ 2743913955487^6383*100000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53620913 100000000 2743913955487 6250000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528224281/1000000000 : ℝ)^8431 ≤ (43041163636671/100000000000000 : ℝ)^6383 := by
    have hnat : (528224281 : ℕ)^8431*100000000000000^6383 ≤ 43041163636671^6383*1000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528224281 1000000000 43041163636671 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2140901913/10000000000 : ℝ)^8431 ≤ (1632026632383/12500000000000 : ℝ)^6383 := by
    have hnat : (2140901913 : ℕ)^8431*12500000000000^6383 ≤ 1632026632383^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140901913 10000000000 1632026632383 12500000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53620913/100000000 : ℝ), (528224281/1000000000 : ℝ), (-2140901913/10000000000 : ℝ)] ![(2743913955487/6250000000000 : ℝ), (43041163636671/100000000000000 : ℝ), (1632026632383/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53620913/100000000 : ℝ)|^8431 ≤ (2743913955487/6250000000000 : ℝ)^6383
        have hw : |(53620913/100000000 : ℝ)|=(53620913/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528224281/1000000000 : ℝ)|^8431 ≤ (43041163636671/100000000000000 : ℝ)^6383
        have hw : |(528224281/1000000000 : ℝ)|=(528224281/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2140901913/10000000000 : ℝ)|^8431 ≤ (1632026632383/12500000000000 : ℝ)^6383
        have hw : |(-2140901913/10000000000 : ℝ)|=(2140901913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_box_7 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (33954823/80000000 : ℝ)*x 0 + (881366739/2000000000 : ℝ)*x 1 + (2203416993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33954823/80000000 : ℝ)^8431 ≤ (16119960018237/50000000000000 : ℝ)^6383 := by
    have hnat : (33954823 : ℕ)^8431*50000000000000^6383 ≤ 16119960018237^6383*80000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33954823 80000000 16119960018237 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (881366739/2000000000 : ℝ)^8431 ≤ (8470009623641/25000000000000 : ℝ)^6383 := by
    have hnat : (881366739 : ℕ)^8431*25000000000000^6383 ≤ 8470009623641^6383*2000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881366739 2000000000 8470009623641 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2203416993/5000000000 : ℝ)^8431 ≤ (8470010362403/25000000000000 : ℝ)^6383 := by
    have hnat : (2203416993 : ℕ)^8431*25000000000000^6383 ≤ 8470010362403^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203416993 5000000000 8470010362403 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33954823/80000000 : ℝ), (881366739/2000000000 : ℝ), (2203416993/5000000000 : ℝ)] ![(16119960018237/50000000000000 : ℝ), (8470009623641/25000000000000 : ℝ), (8470010362403/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33954823/80000000 : ℝ)|^8431 ≤ (16119960018237/50000000000000 : ℝ)^6383
        have hw : |(33954823/80000000 : ℝ)|=(33954823/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(881366739/2000000000 : ℝ)|^8431 ≤ (8470009623641/25000000000000 : ℝ)^6383
        have hw : |(881366739/2000000000 : ℝ)|=(881366739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2203416993/5000000000 : ℝ)|^8431 ≤ (8470010362403/25000000000000 : ℝ)^6383
        have hw : |(2203416993/5000000000 : ℝ)|=(2203416993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_box_8 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2194833333/10000000000 : ℝ)*x 0 + (5219044987/10000000000 : ℝ)*x 1 + (5384517737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2194833333/10000000000 : ℝ)^8431 ≤ (6746192772937/50000000000000 : ℝ)^6383 := by
    have hnat : (2194833333 : ℕ)^8431*50000000000000^6383 ≤ 6746192772937^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194833333 10000000000 6746192772937 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219044987/10000000000 : ℝ)^8431 ≤ (10590573900447/25000000000000 : ℝ)^6383 := by
    have hnat : (5219044987 : ℕ)^8431*25000000000000^6383 ≤ 10590573900447^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219044987 10000000000 10590573900447 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384517737/10000000000 : ℝ)^8431 ≤ (11036329709893/25000000000000 : ℝ)^6383 := by
    have hnat : (5384517737 : ℕ)^8431*25000000000000^6383 ≤ 11036329709893^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384517737 10000000000 11036329709893 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2194833333/10000000000 : ℝ), (5219044987/10000000000 : ℝ), (5384517737/10000000000 : ℝ)] ![(6746192772937/50000000000000 : ℝ), (10590573900447/25000000000000 : ℝ), (11036329709893/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2194833333/10000000000 : ℝ)|^8431 ≤ (6746192772937/50000000000000 : ℝ)^6383
        have hw : |(-2194833333/10000000000 : ℝ)|=(2194833333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219044987/10000000000 : ℝ)|^8431 ≤ (10590573900447/25000000000000 : ℝ)^6383
        have hw : |(5219044987/10000000000 : ℝ)|=(5219044987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384517737/10000000000 : ℝ)|^8431 ≤ (11036329709893/25000000000000 : ℝ)^6383
        have hw : |(5384517737/10000000000 : ℝ)|=(5384517737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_box_9 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644992763/5000000000 : ℝ)*x 0 + (-2100301149/10000000000 : ℝ)*x 1 + (1346129419/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644992763/5000000000 : ℝ)^8431 ≤ (43124515497111/100000000000000 : ℝ)^6383 := by
    have hnat : (2644992763 : ℕ)^8431*100000000000000^6383 ≤ 43124515497111^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644992763 5000000000 43124515497111 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2100301149/10000000000 : ℝ)^8431 ≤ (2546033262139/20000000000000 : ℝ)^6383 := by
    have hnat : (2100301149 : ℕ)^8431*20000000000000^6383 ≤ 2546033262139^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100301149 10000000000 2546033262139 20000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346129419/2500000000 : ℝ)^8431 ≤ (44145318178997/100000000000000 : ℝ)^6383 := by
    have hnat : (1346129419 : ℕ)^8431*100000000000000^6383 ≤ 44145318178997^6383*2500000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346129419 2500000000 44145318178997 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644992763/5000000000 : ℝ), (-2100301149/10000000000 : ℝ), (1346129419/2500000000 : ℝ)] ![(43124515497111/100000000000000 : ℝ), (2546033262139/20000000000000 : ℝ), (44145318178997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644992763/5000000000 : ℝ)|^8431 ≤ (43124515497111/100000000000000 : ℝ)^6383
        have hw : |(2644992763/5000000000 : ℝ)|=(2644992763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2100301149/10000000000 : ℝ)|^8431 ≤ (2546033262139/20000000000000 : ℝ)^6383
        have hw : |(-2100301149/10000000000 : ℝ)|=(2100301149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346129419/2500000000 : ℝ)|^8431 ≤ (44145318178997/100000000000000 : ℝ)^6383
        have hw : |(1346129419/2500000000 : ℝ)|=(1346129419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_box_10 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644992753/5000000000 : ℝ)*x 0 + (538451777/1000000000 : ℝ)*x 1 + (-2100301049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644992753/5000000000 : ℝ)^8431 ≤ (10781128820439/25000000000000 : ℝ)^6383 := by
    have hnat : (2644992753 : ℕ)^8431*25000000000000^6383 ≤ 10781128820439^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644992753 5000000000 10781128820439 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538451777/1000000000 : ℝ)^8431 ≤ (11036329799233/25000000000000 : ℝ)^6383 := by
    have hnat : (538451777 : ℕ)^8431*25000000000000^6383 ≤ 11036329799233^6383*1000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538451777 1000000000 11036329799233 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2100301049/10000000000 : ℝ)^8431 ≤ (12730165510111/100000000000000 : ℝ)^6383 := by
    have hnat : (2100301049 : ℕ)^8431*100000000000000^6383 ≤ 12730165510111^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100301049 10000000000 12730165510111 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644992753/5000000000 : ℝ), (538451777/1000000000 : ℝ), (-2100301049/10000000000 : ℝ)] ![(10781128820439/25000000000000 : ℝ), (11036329799233/25000000000000 : ℝ), (12730165510111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644992753/5000000000 : ℝ)|^8431 ≤ (10781128820439/25000000000000 : ℝ)^6383
        have hw : |(2644992753/5000000000 : ℝ)|=(2644992753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538451777/1000000000 : ℝ)|^8431 ≤ (11036329799233/25000000000000 : ℝ)^6383
        have hw : |(538451777/1000000000 : ℝ)|=(538451777/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2100301049/10000000000 : ℝ)|^8431 ≤ (12730165510111/100000000000000 : ℝ)^6383
        have hw : |(-2100301049/10000000000 : ℝ)|=(2100301049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_box_11 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2239888071/5000000000 : ℝ)*x 0 + (4289001753/10000000000 : ℝ)*x 1 + (171560073/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2239888071/5000000000 : ℝ)^8431 ≤ (34622714206021/100000000000000 : ℝ)^6383 := by
    have hnat : (2239888071 : ℕ)^8431*100000000000000^6383 ≤ 34622714206021^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239888071 5000000000 34622714206021 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4289001753/10000000000 : ℝ)^8431 ≤ (16344321263453/50000000000000 : ℝ)^6383 := by
    have hnat : (4289001753 : ℕ)^8431*50000000000000^6383 ≤ 16344321263453^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4289001753 10000000000 16344321263453 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (171560073/400000000 : ℝ)^8431 ≤ (32688643251721/100000000000000 : ℝ)^6383 := by
    have hnat : (171560073 : ℕ)^8431*100000000000000^6383 ≤ 32688643251721^6383*400000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171560073 400000000 32688643251721 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2239888071/5000000000 : ℝ), (4289001753/10000000000 : ℝ), (171560073/400000000 : ℝ)] ![(34622714206021/100000000000000 : ℝ), (16344321263453/50000000000000 : ℝ), (32688643251721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2239888071/5000000000 : ℝ)|^8431 ≤ (34622714206021/100000000000000 : ℝ)^6383
        have hw : |(2239888071/5000000000 : ℝ)|=(2239888071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4289001753/10000000000 : ℝ)|^8431 ≤ (16344321263453/50000000000000 : ℝ)^6383
        have hw : |(4289001753/10000000000 : ℝ)|=(4289001753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(171560073/400000000 : ℝ)|^8431 ≤ (32688643251721/100000000000000 : ℝ)^6383
        have hw : |(171560073/400000000 : ℝ)|=(171560073/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_box_12 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-410085287/2000000000 : ℝ)*x 0 + (2718445303/5000000000 : ℝ)*x 1 + (5274164479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410085287/2000000000 : ℝ)^8431 ≤ (12332406843423/100000000000000 : ℝ)^6383 := by
    have hnat : (410085287 : ℕ)^8431*100000000000000^6383 ≤ 12332406843423^6383*2000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410085287 2000000000 12332406843423 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718445303/5000000000 : ℝ)^8431 ≤ (22356676278439/50000000000000 : ℝ)^6383 := by
    have hnat : (2718445303 : ℕ)^8431*50000000000000^6383 ≤ 22356676278439^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718445303 5000000000 22356676278439 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274164479/10000000000 : ℝ)^8431 ≤ (21477120296001/50000000000000 : ℝ)^6383 := by
    have hnat : (5274164479 : ℕ)^8431*50000000000000^6383 ≤ 21477120296001^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274164479 10000000000 21477120296001 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-410085287/2000000000 : ℝ), (2718445303/5000000000 : ℝ), (5274164479/10000000000 : ℝ)] ![(12332406843423/100000000000000 : ℝ), (22356676278439/50000000000000 : ℝ), (21477120296001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-410085287/2000000000 : ℝ)|^8431 ≤ (12332406843423/100000000000000 : ℝ)^6383
        have hw : |(-410085287/2000000000 : ℝ)|=(410085287/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718445303/5000000000 : ℝ)|^8431 ≤ (22356676278439/50000000000000 : ℝ)^6383
        have hw : |(2718445303/5000000000 : ℝ)|=(2718445303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274164479/10000000000 : ℝ)|^8431 ≤ (21477120296001/50000000000000 : ℝ)^6383
        have hw : |(5274164479/10000000000 : ℝ)|=(5274164479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_box_13 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5367785647/10000000000 : ℝ)*x 0 + (-2144046499/10000000000 : ℝ)*x 1 + (329635247/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367785647/10000000000 : ℝ)^8431 ≤ (21982107934541/50000000000000 : ℝ)^6383 := by
    have hnat : (5367785647 : ℕ)^8431*50000000000000^6383 ≤ 21982107934541^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367785647 10000000000 21982107934541 50000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2144046499/10000000000 : ℝ)^8431 ≤ (13081549200173/100000000000000 : ℝ)^6383 := by
    have hnat : (2144046499 : ℕ)^8431*100000000000000^6383 ≤ 13081549200173^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144046499 10000000000 13081549200173 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329635247/625000000 : ℝ)^8431 ≤ (42954234922861/100000000000000 : ℝ)^6383 := by
    have hnat : (329635247 : ℕ)^8431*100000000000000^6383 ≤ 42954234922861^6383*625000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329635247 625000000 42954234922861 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367785647/10000000000 : ℝ), (-2144046499/10000000000 : ℝ), (329635247/625000000 : ℝ)] ![(21982107934541/50000000000000 : ℝ), (13081549200173/100000000000000 : ℝ), (42954234922861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367785647/10000000000 : ℝ)|^8431 ≤ (21982107934541/50000000000000 : ℝ)^6383
        have hw : |(5367785647/10000000000 : ℝ)|=(5367785647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2144046499/10000000000 : ℝ)|^8431 ≤ (13081549200173/100000000000000 : ℝ)^6383
        have hw : |(-2144046499/10000000000 : ℝ)|=(2144046499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329635247/625000000 : ℝ)|^8431 ≤ (42954234922861/100000000000000 : ℝ)^6383
        have hw : |(329635247/625000000 : ℝ)|=(329635247/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_box_14 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5367785021/10000000000 : ℝ)*x 0 + (5274163989/10000000000 : ℝ)*x 1 + (-2144047289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367785021/10000000000 : ℝ)^8431 ≤ (10991052274209/25000000000000 : ℝ)^6383 := by
    have hnat : (5367785021 : ℕ)^8431*25000000000000^6383 ≤ 10991052274209^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367785021 10000000000 10991052274209 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5274163989/10000000000 : ℝ)^8431 ≤ (10738558830221/25000000000000 : ℝ)^6383 := by
    have hnat : (5274163989 : ℕ)^8431*25000000000000^6383 ≤ 10738558830221^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274163989 10000000000 10738558830221 25000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2144047289/10000000000 : ℝ)^8431 ≤ (2616311113351/20000000000000 : ℝ)^6383 := by
    have hnat : (2144047289 : ℕ)^8431*20000000000000^6383 ≤ 2616311113351^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144047289 10000000000 2616311113351 20000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367785021/10000000000 : ℝ), (5274163989/10000000000 : ℝ), (-2144047289/10000000000 : ℝ)] ![(10991052274209/25000000000000 : ℝ), (10738558830221/25000000000000 : ℝ), (2616311113351/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367785021/10000000000 : ℝ)|^8431 ≤ (10991052274209/25000000000000 : ℝ)^6383
        have hw : |(5367785021/10000000000 : ℝ)|=(5367785021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5274163989/10000000000 : ℝ)|^8431 ≤ (10738558830221/25000000000000 : ℝ)^6383
        have hw : |(5274163989/10000000000 : ℝ)|=(5274163989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2144047289/10000000000 : ℝ)|^8431 ≤ (2616311113351/20000000000000 : ℝ)^6383
        have hw : |(-2144047289/10000000000 : ℝ)|=(2144047289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1238_box_15 (p : ℝ) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2112752341/5000000000 : ℝ)*x 0 + (4416134679/10000000000 : ℝ)*x 1 + (4416135797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2112752341/5000000000 : ℝ)^8431 ≤ (4006368550389/12500000000000 : ℝ)^6383 := by
    have hnat : (2112752341 : ℕ)^8431*12500000000000^6383 ≤ 4006368550389^6383*5000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112752341 5000000000 4006368550389 12500000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4416134679/10000000000 : ℝ)^8431 ≤ (3397452011423/10000000000000 : ℝ)^6383 := by
    have hnat : (4416134679 : ℕ)^8431*10000000000000^6383 ≤ 3397452011423^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4416134679 10000000000 3397452011423 10000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4416135797/10000000000 : ℝ)^8431 ≤ (33974531474983/100000000000000 : ℝ)^6383 := by
    have hnat : (4416135797 : ℕ)^8431*100000000000000^6383 ≤ 33974531474983^6383*10000000000^8431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4416135797 10000000000 33974531474983 100000000000000 8431 6383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8431/2048 : ℝ)) 8431 6383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2112752341/5000000000 : ℝ), (4416134679/10000000000 : ℝ), (4416135797/10000000000 : ℝ)] ![(4006368550389/12500000000000 : ℝ), (3397452011423/10000000000000 : ℝ), (33974531474983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2112752341/5000000000 : ℝ)|^8431 ≤ (4006368550389/12500000000000 : ℝ)^6383
        have hw : |(2112752341/5000000000 : ℝ)|=(2112752341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4416134679/10000000000 : ℝ)|^8431 ≤ (3397452011423/10000000000000 : ℝ)^6383
        have hw : |(4416134679/10000000000 : ℝ)|=(4416134679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4416135797/10000000000 : ℝ)|^8431 ≤ (33974531474983/100000000000000 : ℝ)^6383
        have hw : |(4416135797/10000000000 : ℝ)|=(4416135797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1238_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5737/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31123/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29687/50000 : ℝ) ∧ (80097/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83337/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7051/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5737/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7051/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5737/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7051/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5737/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7051/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5737/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7051/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5737/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7051/50000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (5737/50000 : ℝ) ^ (4215/1024 : ℝ) ≤ (13476836602356767/100000000000000000000 : ℝ) := by
    have hpowers : (5737/50000 : ℝ)^4215 ≤ (13476836602356767/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5737 : ℕ)^4215*100000000000000000000^1024 ≤ 13476836602356767^1024*50000^4215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5737 50000 13476836602356767 100000000000000000000 4215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5737/50000 : ℝ)) (X := (13476836602356767/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7051/50000 : ℝ) ^ (4215/1024 : ℝ) ≤ (7874082555763299/25000000000000000000 : ℝ) := by
    have hpowers : (7051/50000 : ℝ)^4215 ≤ (7874082555763299/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7051 : ℕ)^4215*25000000000000000000^1024 ≤ 7874082555763299^1024*50000^4215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7051 50000 7874082555763299 25000000000000000000 4215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7051/50000 : ℝ)) (X := (7874082555763299/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013476836602356767/50000000000000000000 : ℝ) ≤ (10000654750789803/10000000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (50013476836602356767/50000000000000000000 : ℝ)^1024 ≤ (10000654750789803/10000000000000000 : ℝ)^4215 := by
      have hnat : (50013476836602356767 : ℕ)^1024*10000000000000000^4215 ≤ 10000654750789803^4215*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013476836602356767 50000000000000000000 10000654750789803 10000000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000654750789803/10000000000000000 : ℝ)) (X := (50013476836602356767/50000000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044973166825409963/100000000000000000000 : ℝ) ≤ (2500273100148713/2500000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (100044973166825409963/100000000000000000000 : ℝ)^1024 ≤ (2500273100148713/2500000000000000 : ℝ)^4215 := by
      have hnat : (100044973166825409963 : ℕ)^1024*2500000000000000^4215 ≤ 2500273100148713^4215*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044973166825409963 100000000000000000000 2500273100148713 2500000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500273100148713/2500000000000000 : ℝ)) (X := (100044973166825409963/100000000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507874082555763299/12500000000000000000 : ℝ) ≤ (10001530050399901/10000000000000000 : ℝ) ^ (4215/1024 : ℝ) := by
    have hpowers : (12507874082555763299/12500000000000000000 : ℝ)^1024 ≤ (10001530050399901/10000000000000000 : ℝ)^4215 := by
      have hnat : (12507874082555763299 : ℕ)^1024*10000000000000000^4215 ≤ 10001530050399901^4215*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507874082555763299 12500000000000000000 10001530050399901 10000000000000000 1024 4215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001530050399901/10000000000000000 : ℝ)) (X := (12507874082555763299/12500000000000000000 : ℝ)) (by norm_num) 4215 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13476836602356767/100000000000000000000 : ℝ) ≤ ((3283959687168667229/3285000000000000000 : ℝ)+2*(437649805049/262800000000000 : ℝ)*(5737/50000 : ℝ))^(4215/1024 : ℝ) := by
    rw [show (3283959687168667229/3285000000000000000 : ℝ)+2*(437649805049/262800000000000 : ℝ)*(5737/50000 : ℝ)=(10000654750789803/10000000000000000 : ℝ) by norm_num, show 1+2*(13476836602356767/100000000000000000000 : ℝ)=(50013476836602356767/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7874082555763299/25000000000000000000 : ℝ)+(13476836602356767/100000000000000000000 : ℝ) ≤ ((3283959687168667229/3285000000000000000 : ℝ)+(437649805049/262800000000000 : ℝ)*((7051/50000 : ℝ)+(5737/50000 : ℝ)))^(4215/1024 : ℝ) := by
    rw [show (3283959687168667229/3285000000000000000 : ℝ)+(437649805049/262800000000000 : ℝ)*((7051/50000 : ℝ)+(5737/50000 : ℝ))=(2500273100148713/2500000000000000 : ℝ) by norm_num, show 1+(7874082555763299/25000000000000000000 : ℝ)+(13476836602356767/100000000000000000000 : ℝ)=(100044973166825409963/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7874082555763299/25000000000000000000 : ℝ) ≤ ((3283959687168667229/3285000000000000000 : ℝ)+2*(437649805049/262800000000000 : ℝ)*(7051/50000 : ℝ))^(4215/1024 : ℝ) := by
    rw [show (3283959687168667229/3285000000000000000 : ℝ)+2*(437649805049/262800000000000 : ℝ)*(7051/50000 : ℝ)=(10001530050399901/10000000000000000 : ℝ) by norm_num, show 1+2*(7874082555763299/25000000000000000000 : ℝ)=(12507874082555763299/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3283959687168667229/3285000000000000000 : ℝ)*(X 1 0+X 2 0)+(437649805049/262800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (5737/50000 : ℝ)) (hi := (7051/50000 : ℝ)) (c := (3283959687168667229/3285000000000000000 : ℝ)) (alpha := (437649805049/262800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3283959687168667229/3285000000000000000 : ℝ)*(X 0 1+X 2 1)+(437649805049/262800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (5737/50000 : ℝ)) (hi := (7051/50000 : ℝ)) (c := (3283959687168667229/3285000000000000000 : ℝ)) (alpha := (437649805049/262800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3283959687168667229/3285000000000000000 : ℝ)*(X 0 2+X 1 2)+(437649805049/262800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4215/1024 : ℝ)) (lo := (5737/50000 : ℝ)) (hi := (7051/50000 : ℝ)) (c := (3283959687168667229/3285000000000000000 : ℝ)) (alpha := (437649805049/262800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1997984967/10000000000 : ℝ)*X 0 0+(1343726017/2500000000 : ℝ)*X 0 1+(1074980887/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296766331/10000000000 : ℝ)*X 1 0+(-2104178161/10000000000 : ℝ)*X 1 1+(5374904073/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2648383347/5000000000 : ℝ)*X 2 0+(1343726019/2500000000 : ℝ)*X 2 1+(-2104177669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2228947181/5000000000 : ℝ)*X 0 0+(2150041807/5000000000 : ℝ)*X 0 1+(2150041419/5000000000 : ℝ)*X 0 2+(2228947181/5000000000 : ℝ)*X 1 0+(2150041807/5000000000 : ℝ)*X 1 1+(2150041419/5000000000 : ℝ)*X 1 2+(2228947181/5000000000 : ℝ)*X 2 0+(2150041807/5000000000 : ℝ)*X 2 1+(2150041419/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-112350629/500000000 : ℝ)*X 0 0+(5282242741/10000000000 : ℝ)*X 0 1+(5282242753/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5362091363/10000000000 : ℝ)*X 1 0+(-267612747/1250000000 : ℝ)*X 1 1+(52822427/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((53620913/100000000 : ℝ)*X 2 0+(528224281/1000000000 : ℝ)*X 2 1+(-2140901913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((33954823/80000000 : ℝ)*X 0 0+(881366739/2000000000 : ℝ)*X 0 1+(2203416993/5000000000 : ℝ)*X 0 2+(33954823/80000000 : ℝ)*X 1 0+(881366739/2000000000 : ℝ)*X 1 1+(2203416993/5000000000 : ℝ)*X 1 2+(33954823/80000000 : ℝ)*X 2 0+(881366739/2000000000 : ℝ)*X 2 1+(2203416993/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2194833333/10000000000 : ℝ)*X 0 0+(5219044987/10000000000 : ℝ)*X 0 1+(5384517737/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644992763/5000000000 : ℝ)*X 1 0+(-2100301149/10000000000 : ℝ)*X 1 1+(1346129419/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2644992753/5000000000 : ℝ)*X 2 0+(538451777/1000000000 : ℝ)*X 2 1+(-2100301049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2239888071/5000000000 : ℝ)*X 0 0+(4289001753/10000000000 : ℝ)*X 0 1+(171560073/400000000 : ℝ)*X 0 2+(2239888071/5000000000 : ℝ)*X 1 0+(4289001753/10000000000 : ℝ)*X 1 1+(171560073/400000000 : ℝ)*X 1 2+(2239888071/5000000000 : ℝ)*X 2 0+(4289001753/10000000000 : ℝ)*X 2 1+(171560073/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-410085287/2000000000 : ℝ)*X 0 0+(2718445303/5000000000 : ℝ)*X 0 1+(5274164479/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5367785647/10000000000 : ℝ)*X 1 0+(-2144046499/10000000000 : ℝ)*X 1 1+(329635247/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5367785021/10000000000 : ℝ)*X 2 0+(5274163989/10000000000 : ℝ)*X 2 1+(-2144047289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2112752341/5000000000 : ℝ)*X 0 0+(4416134679/10000000000 : ℝ)*X 0 1+(4416135797/10000000000 : ℝ)*X 0 2+(2112752341/5000000000 : ℝ)*X 1 0+(4416134679/10000000000 : ℝ)*X 1 1+(4416135797/10000000000 : ℝ)*X 1 2+(2112752341/5000000000 : ℝ)*X 2 0+(4416134679/10000000000 : ℝ)*X 2 1+(4416135797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1238_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31123/50000 : ℝ) ≤ (-34078292485030476827992311957749/54750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1791473/1250000000000 : ℝ)*(upper0) + (57660057/50000000000000 : ℝ)*(upper1) + (5310273/25000000000000 : ℝ)*(upper2) + (104744817/100000000000000 : ℝ)*(upper3) + (18042271/10000000000000 : ℝ)*(upper5) + (3999736569249373/100000000000000 : ℝ)*(major0) + (3999736569249373/100000000000000 : ℝ)*(major1) + (3999736569249373/100000000000000 : ℝ)*(major2) + (193452183/10000000000000 : ℝ)*(sp1) + (10433624133/100000000000000 : ℝ)*(sp3) + (2688758829390269/50000000000000 : ℝ)*(sp4) + (1344378931064677/25000000000000 : ℝ)*(sp5) + (2688758829390269/50000000000000 : ℝ)*(sp6) + (528538572991721/20000000000000 : ℝ)*(sp7) + (1321351649291369/50000000000000 : ℝ)*(f.failure) + (2688758829390269/50000000000000 : ℝ)*(f.sum) + (18391465096063/13140000000000000000000000000 : ℝ)*base66 + (2320034016416713361/109500000000000000000000000000000 : ℝ)*base68 + (5861898383095213361/109500000000000000000000000000000 : ℝ)*base70 + (483105319286713361/109500000000000000000000000000000 : ℝ)*base72 + (875328141672583/13140000000000000000000000000 : ℝ)*base74 + (3995022379417213361/109500000000000000000000000000000 : ℝ)*base76 + (1353222395213713361/109500000000000000000000000000000 : ℝ)*base78 + (4340950371275713361/109500000000000000000000000000000 : ℝ)*base80 + (71863248843677/13140000000000000000000000000 : ℝ)*base81 + (5337793/2500000000000000000000 : ℝ)*base89 + (5337793/2500000000000000000000 : ℝ)*base91 + (5337793/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29687/50000 : ℝ) ≤ (866897421914157924657643807/1460000000000000000000000000 : ℝ) := by norm_num
    linear_combination (190667683/100000000000000 : ℝ)*(lower0) + (194597293/100000000000000 : ℝ)*(lower1) + (374371769/100000000000000 : ℝ)*(lower2) + (139410307/100000000000000 : ℝ)*(lower3) + (93163829/50000000000000 : ℝ)*(lower5) + (4065482964900277/100000000000000 : ℝ)*(major0) + (4065482964900277/100000000000000 : ℝ)*(major1) + (4065482964900277/100000000000000 : ℝ)*(major2) + (5425030537618783/100000000000000 : ℝ)*(sp0) + (5424768853114301/100000000000000 : ℝ)*(sp1) + (5425030537618783/100000000000000 : ℝ)*(sp2) + (2686135090399919/100000000000000 : ℝ)*(sp3) + (2030799829/25000000000000 : ℝ)*(sp7) + (261684504483/100000000000000 : ℝ)*(sp9) + (537228642719847/20000000000000 : ℝ)*(f.failure) + (5425030537618783/100000000000000 : ℝ)*(f.sum) + (84461559175193/13140000000000000000000000000 : ℝ)*base65 + (362702451670028311/109500000000000000000000000000000 : ℝ)*base67 + (5308692058773471689/109500000000000000000000000000000 : ℝ)*base70 + (1412622552531471689/109500000000000000000000000000000 : ℝ)*base72 + (172238159360453/13140000000000000000000000000 : ℝ)*base73 + (8386538521695471689/109500000000000000000000000000000 : ℝ)*base76 + (89750219395028311/109500000000000000000000000000000 : ℝ)*base77 + (986748397762028311/109500000000000000000000000000000 : ℝ)*base79 + (90525250613633/13140000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (4449841/1000000000000000000000 : ℝ)*base90 + (4449841/1000000000000000000000 : ℝ)*base92 + (4449841/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80097/100000 : ℝ) ≤ (2923629997637934044281931681197/3650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1342323/2000000000000 : ℝ)*(lower3) + (4978597/25000000000000 : ℝ)*(upper4) + (427177/12500000000000 : ℝ)*(lower5) + (906456173339193/20000000000000 : ℝ)*(major0) + (906456173339193/20000000000000 : ℝ)*(major1) + (906456173339193/20000000000000 : ℝ)*(major2) + (2027754739/100000000000000 : ℝ)*(sp0) + (33495647369/100000000000000 : ℝ)*(sp1) + (80684573127/100000000000000 : ℝ)*(sp2) + (9023307447/25000000000000 : ℝ)*(sp3) + (94426473031407/1562500000000 : ℝ)*(sp8) + (3021631403058709/50000000000000 : ℝ)*(sp9) + (302160780859583/5000000000000 : ℝ)*(sp10) + (74863238026683/2500000000000 : ℝ)*(sp11) + (748641403574277/25000000000000 : ℝ)*(f.failure) + (3021648150882393/50000000000000 : ℝ)*(f.sum) + (786908375819/175200000000000000000000000 : ℝ)*base65 + (458260335042367/7300000000000000000000000000000 : ℝ)*base68 + (147754103519542367/7300000000000000000000000000000 : ℝ)*base70 + (32257398200942367/7300000000000000000000000000000 : ℝ)*base72 + (982344789343/876000000000000000000000000 : ℝ)*base73 + (61955200866742367/7300000000000000000000000000000 : ℝ)*base76 + (31386413965242367/7300000000000000000000000000000 : ℝ)*base78 + (3661180770242367/7300000000000000000000000000000 : ℝ)*base80 + (2757124834097/876000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3820131/1250000000000000000000 : ℝ)*base90 + (3820131/1250000000000000000000 : ℝ)*base92 + (3820131/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-83337/100000 : ℝ) ≤ (-7604280494328238030178026255963/9125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16151573/100000000000000 : ℝ)*(lower0) + (18915341/100000000000000 : ℝ)*(lower1) + (657658901/100000000000000 : ℝ)*(lower4) + (2283893835593541/50000000000000 : ℝ)*(major0) + (2283893835593541/50000000000000 : ℝ)*(major1) + (2283893835593541/50000000000000 : ℝ)*(major2) + (3926994663/50000000000000 : ℝ)*(sp0) + (261114206247/50000000000000 : ℝ)*(sp5) + (125210970289/12500000000000 : ℝ)*(sp6) + (139880265621/50000000000000 : ℝ)*(sp7) + (1229064007062623/20000000000000 : ℝ)*(sp12) + (6144805660889947/100000000000000 : ℝ)*(sp13) + (614432620154013/10000000000000 : ℝ)*(sp14) + (3017745886127051/100000000000000 : ℝ)*(sp15) + (3018025646658293/100000000000000 : ℝ)*(f.failure) + (6145327889302441/100000000000000 : ℝ)*(f.sum) + (3321364090847/2190000000000000000000000000 : ℝ)*base66 + (146067462421097821/18250000000000000000000000000000 : ℝ)*base67 + (36247509534152179/18250000000000000000000000000000 : ℝ)*base70 + (188263709251597821/18250000000000000000000000000000 : ℝ)*base71 + (18425467467677/2190000000000000000000000000 : ℝ)*base74 + (33267079021597821/18250000000000000000000000000000 : ℝ)*base75 + (141624040294847821/18250000000000000000000000000000 : ℝ)*base77 + (1240517887212902179/18250000000000000000000000000000 : ℝ)*base80 + (5575492145233/2190000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (51370579/5000000000000000000000 : ℝ)*base90 + (51370579/5000000000000000000000 : ℝ)*base92 + (51370579/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1238_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5737/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31123/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29687/50000 : ℝ) else (80097/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83337/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1238_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1238_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5737/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31123/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29687/50000 : ℝ) else (80097/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83337/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1238_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4215/1024 : ℝ) ≤ p) (hpb : p ≤ (8431/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75675097/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5737/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31123/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29687/50000 : ℝ) else (80097/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83337/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1238_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
