-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1050_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:54:40.340127+00:00
-- url     : https://prove2.me/submissions/d4c75d36-a4f2-4ec8-9d4c-52f4951366d0

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
theorem support_rectangle_w1050_s0_0 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1921273477/10000000000 : ℝ)*x 0 + (1518959719/2500000000 : ℝ)*x 1 + (4768727903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1921273477/10000000000 : ℝ)^8243 ≤ (2784142946527/25000000000000 : ℝ)^6195 := by
    have hnat : (1921273477 : ℕ)^8243*25000000000000^6195 ≤ 2784142946527^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1921273477 10000000000 2784142946527 25000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1518959719/2500000000 : ℝ)^8243 ≤ (6441378619663/12500000000000 : ℝ)^6195 := by
    have hnat : (1518959719 : ℕ)^8243*12500000000000^6195 ≤ 6441378619663^6195*2500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1518959719 2500000000 6441378619663 12500000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4768727903/10000000000 : ℝ)^8243 ≤ (37332399248901/100000000000000 : ℝ)^6195 := by
    have hnat : (4768727903 : ℕ)^8243*100000000000000^6195 ≤ 37332399248901^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4768727903 10000000000 37332399248901 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1921273477/10000000000 : ℝ), (1518959719/2500000000 : ℝ), (4768727903/10000000000 : ℝ)] ![(2784142946527/25000000000000 : ℝ), (6441378619663/12500000000000 : ℝ), (37332399248901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1921273477/10000000000 : ℝ)|^8243 ≤ (2784142946527/25000000000000 : ℝ)^6195
        have hw : |(-1921273477/10000000000 : ℝ)|=(1921273477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1518959719/2500000000 : ℝ)|^8243 ≤ (6441378619663/12500000000000 : ℝ)^6195
        have hw : |(1518959719/2500000000 : ℝ)|=(1518959719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4768727903/10000000000 : ℝ)|^8243 ≤ (37332399248901/100000000000000 : ℝ)^6195
        have hw : |(4768727903/10000000000 : ℝ)|=(4768727903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s0_1 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5521973303/10000000000 : ℝ)*x 0 + (-668533539/2500000000 : ℝ)*x 1 + (4768727903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5521973303/10000000000 : ℝ)^8243 ≤ (22688379231889/50000000000000 : ℝ)^6195 := by
    have hnat : (5521973303 : ℕ)^8243*50000000000000^6195 ≤ 22688379231889^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5521973303 10000000000 22688379231889 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (668533539/2500000000 : ℝ)^8243 ≤ (3458168455371/20000000000000 : ℝ)^6195 := by
    have hnat : (668533539 : ℕ)^8243*20000000000000^6195 ≤ 3458168455371^6195*2500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668533539 2500000000 3458168455371 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4768727903/10000000000 : ℝ)^8243 ≤ (37332399248901/100000000000000 : ℝ)^6195 := by
    have hnat : (4768727903 : ℕ)^8243*100000000000000^6195 ≤ 37332399248901^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4768727903 10000000000 37332399248901 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5521973303/10000000000 : ℝ), (-668533539/2500000000 : ℝ), (4768727903/10000000000 : ℝ)] ![(22688379231889/50000000000000 : ℝ), (3458168455371/20000000000000 : ℝ), (37332399248901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5521973303/10000000000 : ℝ)|^8243 ≤ (22688379231889/50000000000000 : ℝ)^6195
        have hw : |(5521973303/10000000000 : ℝ)|=(5521973303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-668533539/2500000000 : ℝ)|^8243 ≤ (3458168455371/20000000000000 : ℝ)^6195
        have hw : |(-668533539/2500000000 : ℝ)|=(668533539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4768727903/10000000000 : ℝ)|^8243 ≤ (37332399248901/100000000000000 : ℝ)^6195
        have hw : |(4768727903/10000000000 : ℝ)|=(4768727903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s0_2 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5521973303/10000000000 : ℝ)*x 0 + (4768727903/10000000000 : ℝ)*x 1 + (-668533539/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5521973303/10000000000 : ℝ)^8243 ≤ (22688379231889/50000000000000 : ℝ)^6195 := by
    have hnat : (5521973303 : ℕ)^8243*50000000000000^6195 ≤ 22688379231889^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5521973303 10000000000 22688379231889 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4768727903/10000000000 : ℝ)^8243 ≤ (37332399248901/100000000000000 : ℝ)^6195 := by
    have hnat : (4768727903 : ℕ)^8243*100000000000000^6195 ≤ 37332399248901^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4768727903 10000000000 37332399248901 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (668533539/2500000000 : ℝ)^8243 ≤ (3458168455371/20000000000000 : ℝ)^6195 := by
    have hnat : (668533539 : ℕ)^8243*20000000000000^6195 ≤ 3458168455371^6195*2500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668533539 2500000000 3458168455371 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5521973303/10000000000 : ℝ), (4768727903/10000000000 : ℝ), (-668533539/2500000000 : ℝ)] ![(22688379231889/50000000000000 : ℝ), (37332399248901/100000000000000 : ℝ), (3458168455371/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5521973303/10000000000 : ℝ)|^8243 ≤ (22688379231889/50000000000000 : ℝ)^6195
        have hw : |(5521973303/10000000000 : ℝ)|=(5521973303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4768727903/10000000000 : ℝ)|^8243 ≤ (37332399248901/100000000000000 : ℝ)^6195
        have hw : |(4768727903/10000000000 : ℝ)|=(4768727903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-668533539/2500000000 : ℝ)|^8243 ≤ (3458168455371/20000000000000 : ℝ)^6195
        have hw : |(-668533539/2500000000 : ℝ)|=(668533539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s0_3 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1052134411/2500000000 : ℝ)*x 0 + (97679169/312500000 : ℝ)*x 1 + (1419838651/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052134411/2500000000 : ℝ)^8243 ≤ (31613535020701/100000000000000 : ℝ)^6195 := by
    have hnat : (1052134411 : ℕ)^8243*100000000000000^6195 ≤ 31613535020701^6195*2500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052134411 2500000000 31613535020701 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97679169/312500000 : ℝ)^8243 ≤ (10640413624713/50000000000000 : ℝ)^6195 := by
    have hnat : (97679169 : ℕ)^8243*50000000000000^6195 ≤ 10640413624713^6195*312500000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97679169 312500000 10640413624713 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1419838651/2500000000 : ℝ)^8243 ≤ (23552818862043/50000000000000 : ℝ)^6195 := by
    have hnat : (1419838651 : ℕ)^8243*50000000000000^6195 ≤ 23552818862043^6195*2500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1419838651 2500000000 23552818862043 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052134411/2500000000 : ℝ), (97679169/312500000 : ℝ), (1419838651/2500000000 : ℝ)] ![(31613535020701/100000000000000 : ℝ), (10640413624713/50000000000000 : ℝ), (23552818862043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052134411/2500000000 : ℝ)|^8243 ≤ (31613535020701/100000000000000 : ℝ)^6195
        have hw : |(1052134411/2500000000 : ℝ)|=(1052134411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(97679169/312500000 : ℝ)|^8243 ≤ (10640413624713/50000000000000 : ℝ)^6195
        have hw : |(97679169/312500000 : ℝ)|=(97679169/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1419838651/2500000000 : ℝ)|^8243 ≤ (23552818862043/50000000000000 : ℝ)^6195
        have hw : |(1419838651/2500000000 : ℝ)|=(1419838651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s0_4 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1926694957/10000000000 : ℝ)*x 0 + (2401242531/5000000000 : ℝ)*x 1 + (6040903021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1926694957/10000000000 : ℝ)^8243 ≤ (2794601378721/25000000000000 : ℝ)^6195 := by
    have hnat : (1926694957 : ℕ)^8243*25000000000000^6195 ≤ 2794601378721^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926694957 10000000000 2794601378721 25000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2401242531/5000000000 : ℝ)^8243 ≤ (9421111493287/25000000000000 : ℝ)^6195 := by
    have hnat : (2401242531 : ℕ)^8243*25000000000000^6195 ≤ 9421111493287^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2401242531 5000000000 9421111493287 25000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6040903021/10000000000 : ℝ)^8243 ≤ (51137148499563/100000000000000 : ℝ)^6195 := by
    have hnat : (6040903021 : ℕ)^8243*100000000000000^6195 ≤ 51137148499563^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6040903021 10000000000 51137148499563 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1926694957/10000000000 : ℝ), (2401242531/5000000000 : ℝ), (6040903021/10000000000 : ℝ)] ![(2794601378721/25000000000000 : ℝ), (9421111493287/25000000000000 : ℝ), (51137148499563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1926694957/10000000000 : ℝ)|^8243 ≤ (2794601378721/25000000000000 : ℝ)^6195
        have hw : |(-1926694957/10000000000 : ℝ)|=(1926694957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2401242531/5000000000 : ℝ)|^8243 ≤ (9421111493287/25000000000000 : ℝ)^6195
        have hw : |(2401242531/5000000000 : ℝ)|=(2401242531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6040903021/10000000000 : ℝ)|^8243 ≤ (51137148499563/100000000000000 : ℝ)^6195
        have hw : |(6040903021/10000000000 : ℝ)|=(6040903021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s0_5 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2583646089/5000000000 : ℝ)*x 0 + (-700979673/5000000000 : ℝ)*x 1 + (6040903007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2583646089/5000000000 : ℝ)^8243 ≤ (10385104780181/25000000000000 : ℝ)^6195 := by
    have hnat : (2583646089 : ℕ)^8243*25000000000000^6195 ≤ 10385104780181^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583646089 5000000000 10385104780181 25000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (700979673/5000000000 : ℝ)^8243 ≤ (1830608130541/25000000000000 : ℝ)^6195 := by
    have hnat : (700979673 : ℕ)^8243*25000000000000^6195 ≤ 1830608130541^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      700979673 5000000000 1830608130541 25000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6040903007/10000000000 : ℝ)^8243 ≤ (3196071771367/6250000000000 : ℝ)^6195 := by
    have hnat : (6040903007 : ℕ)^8243*6250000000000^6195 ≤ 3196071771367^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6040903007 10000000000 3196071771367 6250000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2583646089/5000000000 : ℝ), (-700979673/5000000000 : ℝ), (6040903007/10000000000 : ℝ)] ![(10385104780181/25000000000000 : ℝ), (1830608130541/25000000000000 : ℝ), (3196071771367/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2583646089/5000000000 : ℝ)|^8243 ≤ (10385104780181/25000000000000 : ℝ)^6195
        have hw : |(2583646089/5000000000 : ℝ)|=(2583646089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-700979673/5000000000 : ℝ)|^8243 ≤ (1830608130541/25000000000000 : ℝ)^6195
        have hw : |(-700979673/5000000000 : ℝ)|=(700979673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6040903007/10000000000 : ℝ)|^8243 ≤ (3196071771367/6250000000000 : ℝ)^6195
        have hw : |(6040903007/10000000000 : ℝ)|=(6040903007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s0_6 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (161477893/312500000 : ℝ)*x 0 + (1510225671/2500000000 : ℝ)*x 1 + (-175244907/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (161477893/312500000 : ℝ)^8243 ≤ (4154042337803/10000000000000 : ℝ)^6195 := by
    have hnat : (161477893 : ℕ)^8243*10000000000000^6195 ≤ 4154042337803^6195*312500000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161477893 312500000 4154042337803 10000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1510225671/2500000000 : ℝ)^8243 ≤ (25568572351859/50000000000000 : ℝ)^6195 := by
    have hnat : (1510225671 : ℕ)^8243*50000000000000^6195 ≤ 25568572351859^6195*2500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1510225671 2500000000 25568572351859 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (175244907/1250000000 : ℝ)^8243 ≤ (3661215948347/50000000000000 : ℝ)^6195 := by
    have hnat : (175244907 : ℕ)^8243*50000000000000^6195 ≤ 3661215948347^6195*1250000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175244907 1250000000 3661215948347 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(161477893/312500000 : ℝ), (1510225671/2500000000 : ℝ), (-175244907/1250000000 : ℝ)] ![(4154042337803/10000000000000 : ℝ), (25568572351859/50000000000000 : ℝ), (3661215948347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(161477893/312500000 : ℝ)|^8243 ≤ (4154042337803/10000000000000 : ℝ)^6195
        have hw : |(161477893/312500000 : ℝ)|=(161477893/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1510225671/2500000000 : ℝ)|^8243 ≤ (25568572351859/50000000000000 : ℝ)^6195
        have hw : |(1510225671/2500000000 : ℝ)|=(1510225671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-175244907/1250000000 : ℝ)|^8243 ≤ (3661215948347/50000000000000 : ℝ)^6195
        have hw : |(-175244907/1250000000 : ℝ)|=(175244907/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s0_7 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (659239/1562500 : ℝ)*x 0 + (5613405091/10000000000 : ℝ)*x 1 + (127759421/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659239/1562500 : ℝ)^8243 ≤ (6343889275621/20000000000000 : ℝ)^6195 := by
    have hnat : (659239 : ℕ)^8243*20000000000000^6195 ≤ 6343889275621^6195*1562500^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659239 1562500 6343889275621 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5613405091/10000000000 : ℝ)^8243 ≤ (46379209160727/100000000000000 : ℝ)^6195 := by
    have hnat : (5613405091 : ℕ)^8243*100000000000000^6195 ≤ 46379209160727^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5613405091 10000000000 46379209160727 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127759421/400000000 : ℝ)^8243 ≤ (5475336111817/25000000000000 : ℝ)^6195 := by
    have hnat : (127759421 : ℕ)^8243*25000000000000^6195 ≤ 5475336111817^6195*400000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127759421 400000000 5475336111817 25000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659239/1562500 : ℝ), (5613405091/10000000000 : ℝ), (127759421/400000000 : ℝ)] ![(6343889275621/20000000000000 : ℝ), (46379209160727/100000000000000 : ℝ), (5475336111817/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659239/1562500 : ℝ)|^8243 ≤ (6343889275621/20000000000000 : ℝ)^6195
        have hw : |(659239/1562500 : ℝ)|=(659239/1562500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5613405091/10000000000 : ℝ)|^8243 ≤ (46379209160727/100000000000000 : ℝ)^6195
        have hw : |(5613405091/10000000000 : ℝ)|=(5613405091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(127759421/400000000 : ℝ)|^8243 ≤ (5475336111817/25000000000000 : ℝ)^6195
        have hw : |(127759421/400000000 : ℝ)|=(127759421/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1050_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73840941/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (29/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7043/25000 : ℝ)*pair X 0 0 := by
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
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (4121/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4121 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4121*1^1024 ≤ 0^1024*1^4121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4121 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4121/1024 : ℝ) ≤ (500673526942154073/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4121 ≤ (500673526942154073/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4121*20000000000000000000^1024 ≤ 500673526942154073^1024*5^4121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 500673526942154073 20000000000000000000 4121 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (500673526942154073/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4121/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4121 := by
      have hnat : (1 : ℕ)^1024*1^4121 ≤ 1^4121*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20500673526942154073/20000000000000000000 : ℝ) ≤ (2012325559660313/2000000000000000 : ℝ) ^ (4121/1024 : ℝ) := by
    have hpowers : (20500673526942154073/20000000000000000000 : ℝ)^1024 ≤ (2012325559660313/2000000000000000 : ℝ)^4121 := by
      have hnat : (20500673526942154073 : ℕ)^1024*2000000000000000^4121 ≤ 2012325559660313^4121*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20500673526942154073 20000000000000000000 2012325559660313 2000000000000000 1024 4121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2012325559660313/2000000000000000 : ℝ)) (X := (20500673526942154073/20000000000000000000 : ℝ)) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10500673526942154073/10000000000000000000 : ℝ) ≤ (1012325559660313/1000000000000000 : ℝ) ^ (4121/1024 : ℝ) := by
    have hpowers : (10500673526942154073/10000000000000000000 : ℝ)^1024 ≤ (1012325559660313/1000000000000000 : ℝ)^4121 := by
      have hnat : (10500673526942154073 : ℕ)^1024*1000000000000000^4121 ≤ 1012325559660313^4121*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10500673526942154073 10000000000000000000 1012325559660313 1000000000000000 1024 4121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1012325559660313/1000000000000000 : ℝ)) (X := (10500673526942154073/10000000000000000000 : ℝ)) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(12325559660313/800000000000000 : ℝ)*(0 : ℝ))^(4121/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(12325559660313/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(500673526942154073/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(12325559660313/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4121/1024 : ℝ) := by
    rw [show (1 : ℝ)+(12325559660313/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2012325559660313/2000000000000000 : ℝ) by norm_num, show 1+(500673526942154073/20000000000000000000 : ℝ)+(0 : ℝ)=(20500673526942154073/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(500673526942154073/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(12325559660313/800000000000000 : ℝ)*(2/5 : ℝ))^(4121/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(12325559660313/800000000000000 : ℝ)*(2/5 : ℝ)=(1012325559660313/1000000000000000 : ℝ) by norm_num, show 1+2*(500673526942154073/20000000000000000000 : ℝ)=(10500673526942154073/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(12325559660313/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4121/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12325559660313/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(12325559660313/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4121/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12325559660313/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(12325559660313/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4121/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12325559660313/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1921273477/10000000000 : ℝ)*X 0 0+(1518959719/2500000000 : ℝ)*X 0 1+(4768727903/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5521973303/10000000000 : ℝ)*X 1 0+(-668533539/2500000000 : ℝ)*X 1 1+(4768727903/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5521973303/10000000000 : ℝ)*X 2 0+(4768727903/10000000000 : ℝ)*X 2 1+(-668533539/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1052134411/2500000000 : ℝ)*X 0 0+(97679169/312500000 : ℝ)*X 0 1+(1419838651/2500000000 : ℝ)*X 0 2+(1052134411/2500000000 : ℝ)*X 1 0+(97679169/312500000 : ℝ)*X 1 1+(1419838651/2500000000 : ℝ)*X 1 2+(1052134411/2500000000 : ℝ)*X 2 0+(97679169/312500000 : ℝ)*X 2 1+(1419838651/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1926694957/10000000000 : ℝ)*X 0 0+(2401242531/5000000000 : ℝ)*X 0 1+(6040903021/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2583646089/5000000000 : ℝ)*X 1 0+(-700979673/5000000000 : ℝ)*X 1 1+(6040903007/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((161477893/312500000 : ℝ)*X 2 0+(1510225671/2500000000 : ℝ)*X 2 1+(-175244907/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((659239/1562500 : ℝ)*X 0 0+(5613405091/10000000000 : ℝ)*X 0 1+(127759421/400000000 : ℝ)*X 0 2+(659239/1562500 : ℝ)*X 1 0+(5613405091/10000000000 : ℝ)*X 1 1+(127759421/400000000 : ℝ)*X 1 2+(659239/1562500 : ℝ)*X 2 0+(5613405091/10000000000 : ℝ)*X 2 1+(127759421/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3350401596673193569503/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28791379/100000000000000 : ℝ)*(base1) + (135042519/20000000000000 : ℝ)*(base19) + (125947117/20000000000000 : ℝ)*(base23) + (4547701/10000000000000 : ℝ)*(base24) + (151590033/100000000000000 : ℝ)*(upper3) + (18072693917541/3125000000000 : ℝ)*(major0) + (18072693917541/3125000000000 : ℝ)*(major1) + (18072693917541/3125000000000 : ℝ)*(major2) + (765048194796703/100000000000000 : ℝ)*(sp0) + (47815560488007/6250000000000 : ℝ)*(sp1) + (47815560488007/6250000000000 : ℝ)*(sp2) + (195800732844303/50000000000000 : ℝ)*(sp3) + (184626923/12500000000000 : ℝ)*(sp4) + (1183877887/100000000000000 : ℝ)*(sp7) + (24475167397367/6250000000000 : ℝ)*(f.failure) + (765049643020707/100000000000000 : ℝ)*(f.sum) + (75598944083/1250000000000000000000000000 : ℝ)*base65 + (8819536752167/2500000000000000000000000000 : ℝ)*base68 + (4370175820333/2500000000000000000000000000 : ℝ)*base69 + (3842008750333/2500000000000000000000000000 : ℝ)*base71 + (973555865917/1250000000000000000000000000 : ℝ)*base74 + (3953750162833/2500000000000000000000000000 : ℝ)*base75 + (3842008750333/2500000000000000000000000000 : ℝ)*base77 + (2590639497833/2500000000000000000000000000 : ℝ)*base79 + (2207999466583/1250000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (202347/312500000000000000000 : ℝ)*base89 + (202347/312500000000000000000 : ℝ)*base91 + (202347/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37326556584006336512037/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50753853/50000000000000 : ℝ)*(base1) + (228557997/12500000000000 : ℝ)*(base19) + (94615227/5000000000000 : ℝ)*(base23) + (228346983/50000000000000 : ℝ)*(base45) + (102381183/50000000000000 : ℝ)*(upper3) + (44055233/20000000000000 : ℝ)*(upper5) + (152599865710661/25000000000000 : ℝ)*(major0) + (152599865710661/25000000000000 : ℝ)*(major1) + (152599865710661/25000000000000 : ℝ)*(major2) + (2398573/10000000000000 : ℝ)*(sp2) + (80747829883193/10000000000000 : ℝ)*(sp4) + (100934546107531/12500000000000 : ℝ)*(sp5) + (403738140516977/50000000000000 : ℝ)*(sp6) + (206660189004821/50000000000000 : ℝ)*(sp7) + (103330119879337/25000000000000 : ℝ)*(f.failure) + (12616846833191/1562500000000 : ℝ)*(f.sum) + (7048759203107/10000000000000000000000000000 : ℝ)*base66 + (110258838943107/20000000000000000000000000000 : ℝ)*base68 + (127122348903107/20000000000000000000000000000 : ℝ)*base70 + (134051364183107/20000000000000000000000000000 : ℝ)*base72 + (3772593443107/10000000000000000000000000000 : ℝ)*base74 + (259076453023107/20000000000000000000000000000 : ℝ)*base76 + (105162395183107/20000000000000000000000000000 : ℝ)*base78 + (211557380263107/20000000000000000000000000000 : ℝ)*base80 + (55271096763107/10000000000000000000000000000 : ℝ)*base82 + (536117/1250000000000000000000 : ℝ)*base89 + (536117/1250000000000000000000 : ℝ)*base91 + (536117/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1050_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73840941/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (29/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7043/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1050_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1050_s1_0 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-266568143/1250000000 : ℝ)*x 0 + (5726834437/10000000000 : ℝ)*x 1 + (4982419823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266568143/1250000000 : ℝ)^8243 ≤ (12794969283911/100000000000000 : ℝ)^6195 := by
    have hnat : (266568143 : ℕ)^8243*100000000000000^6195 ≤ 12794969283911^6195*1250000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266568143 1250000000 12794969283911 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5726834437/10000000000 : ℝ)^8243 ≤ (47630355390301/100000000000000 : ℝ)^6195 := by
    have hnat : (5726834437 : ℕ)^8243*100000000000000^6195 ≤ 47630355390301^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5726834437 10000000000 47630355390301 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4982419823/10000000000 : ℝ)^8243 ≤ (4946834413831/12500000000000 : ℝ)^6195 := by
    have hnat : (4982419823 : ℕ)^8243*12500000000000^6195 ≤ 4946834413831^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4982419823 10000000000 4946834413831 12500000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-266568143/1250000000 : ℝ), (5726834437/10000000000 : ℝ), (4982419823/10000000000 : ℝ)] ![(12794969283911/100000000000000 : ℝ), (47630355390301/100000000000000 : ℝ), (4946834413831/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-266568143/1250000000 : ℝ)|^8243 ≤ (12794969283911/100000000000000 : ℝ)^6195
        have hw : |(-266568143/1250000000 : ℝ)|=(266568143/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5726834437/10000000000 : ℝ)|^8243 ≤ (47630355390301/100000000000000 : ℝ)^6195
        have hw : |(5726834437/10000000000 : ℝ)|=(5726834437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4982419823/10000000000 : ℝ)|^8243 ≤ (4946834413831/12500000000000 : ℝ)^6195
        have hw : |(4982419823/10000000000 : ℝ)|=(4982419823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s1_1 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (84753107/156250000 : ℝ)*x 0 + (-507243297/2000000000 : ℝ)*x 1 + (1245605037/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84753107/156250000 : ℝ)^8243 ≤ (44310823918561/100000000000000 : ℝ)^6195 := by
    have hnat : (84753107 : ℕ)^8243*100000000000000^6195 ≤ 44310823918561^6195*156250000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84753107 156250000 44310823918561 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (507243297/2000000000 : ℝ)^8243 ≤ (8057248661471/50000000000000 : ℝ)^6195 := by
    have hnat : (507243297 : ℕ)^8243*50000000000000^6195 ≤ 8057248661471^6195*2000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507243297 2000000000 8057248661471 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1245605037/2500000000 : ℝ)^8243 ≤ (39574678745471/100000000000000 : ℝ)^6195 := by
    have hnat : (1245605037 : ℕ)^8243*100000000000000^6195 ≤ 39574678745471^6195*2500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1245605037 2500000000 39574678745471 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84753107/156250000 : ℝ), (-507243297/2000000000 : ℝ), (1245605037/2500000000 : ℝ)] ![(44310823918561/100000000000000 : ℝ), (8057248661471/50000000000000 : ℝ), (39574678745471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84753107/156250000 : ℝ)|^8243 ≤ (44310823918561/100000000000000 : ℝ)^6195
        have hw : |(84753107/156250000 : ℝ)|=(84753107/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-507243297/2000000000 : ℝ)|^8243 ≤ (8057248661471/50000000000000 : ℝ)^6195
        have hw : |(-507243297/2000000000 : ℝ)|=(507243297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1245605037/2500000000 : ℝ)|^8243 ≤ (39574678745471/100000000000000 : ℝ)^6195
        have hw : |(1245605037/2500000000 : ℝ)|=(1245605037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s1_2 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2712099643/5000000000 : ℝ)*x 0 + (4982419617/10000000000 : ℝ)*x 1 + (-507243317/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2712099643/5000000000 : ℝ)^8243 ≤ (5538853584937/12500000000000 : ℝ)^6195 := by
    have hnat : (2712099643 : ℕ)^8243*12500000000000^6195 ≤ 5538853584937^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712099643 5000000000 5538853584937 12500000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4982419617/10000000000 : ℝ)^8243 ≤ (19787336566749/50000000000000 : ℝ)^6195 := by
    have hnat : (4982419617 : ℕ)^8243*50000000000000^6195 ≤ 19787336566749^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4982419617 10000000000 19787336566749 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (507243317/2000000000 : ℝ)^8243 ≤ (8057249084183/50000000000000 : ℝ)^6195 := by
    have hnat : (507243317 : ℕ)^8243*50000000000000^6195 ≤ 8057249084183^6195*2000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507243317 2000000000 8057249084183 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2712099643/5000000000 : ℝ), (4982419617/10000000000 : ℝ), (-507243317/2000000000 : ℝ)] ![(5538853584937/12500000000000 : ℝ), (19787336566749/50000000000000 : ℝ), (8057249084183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2712099643/5000000000 : ℝ)|^8243 ≤ (5538853584937/12500000000000 : ℝ)^6195
        have hw : |(2712099643/5000000000 : ℝ)|=(2712099643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4982419617/10000000000 : ℝ)|^8243 ≤ (19787336566749/50000000000000 : ℝ)^6195
        have hw : |(4982419617/10000000000 : ℝ)|=(4982419617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-507243317/2000000000 : ℝ)|^8243 ≤ (8057249084183/50000000000000 : ℝ)^6195
        have hw : |(-507243317/2000000000 : ℝ)|=(507243317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s1_3 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1730049/4000000 : ℝ)*x 0 + (1829717113/5000000000 : ℝ)*x 1 + (639218663/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1730049/4000000 : ℝ)^8243 ≤ (4098013996369/12500000000000 : ℝ)^6195 := by
    have hnat : (1730049 : ℕ)^8243*12500000000000^6195 ≤ 4098013996369^6195*4000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1730049 4000000 4098013996369 12500000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1829717113/5000000000 : ℝ)^8243 ≤ (3280902548071/12500000000000 : ℝ)^6195 := by
    have hnat : (1829717113 : ℕ)^8243*12500000000000^6195 ≤ 3280902548071^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1829717113 5000000000 3280902548071 12500000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (639218663/1250000000 : ℝ)^8243 ≤ (40968667622127/100000000000000 : ℝ)^6195 := by
    have hnat : (639218663 : ℕ)^8243*100000000000000^6195 ≤ 40968667622127^6195*1250000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639218663 1250000000 40968667622127 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1730049/4000000 : ℝ), (1829717113/5000000000 : ℝ), (639218663/1250000000 : ℝ)] ![(4098013996369/12500000000000 : ℝ), (3280902548071/12500000000000 : ℝ), (40968667622127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1730049/4000000 : ℝ)|^8243 ≤ (4098013996369/12500000000000 : ℝ)^6195
        have hw : |(1730049/4000000 : ℝ)|=(1730049/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1829717113/5000000000 : ℝ)|^8243 ≤ (3280902548071/12500000000000 : ℝ)^6195
        have hw : |(1829717113/5000000000 : ℝ)|=(1829717113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(639218663/1250000000 : ℝ)|^8243 ≤ (40968667622127/100000000000000 : ℝ)^6195
        have hw : |(639218663/1250000000 : ℝ)|=(639218663/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s1_4 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-42669853/200000000 : ℝ)*x 0 + (4992944531/10000000000 : ℝ)*x 1 + (714511603/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42669853/200000000 : ℝ)^8243 ≤ (12802534108513/100000000000000 : ℝ)^6195 := by
    have hnat : (42669853 : ℕ)^8243*100000000000000^6195 ≤ 12802534108513^6195*200000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42669853 200000000 12802534108513 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4992944531/10000000000 : ℝ)^8243 ≤ (7937189294767/20000000000000 : ℝ)^6195 := by
    have hnat : (4992944531 : ℕ)^8243*20000000000000^6195 ≤ 7937189294767^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4992944531 10000000000 7937189294767 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (714511603/1250000000 : ℝ)^8243 ≤ (5938939926009/12500000000000 : ℝ)^6195 := by
    have hnat : (714511603 : ℕ)^8243*12500000000000^6195 ≤ 5938939926009^6195*1250000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      714511603 1250000000 5938939926009 12500000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42669853/200000000 : ℝ), (4992944531/10000000000 : ℝ), (714511603/1250000000 : ℝ)] ![(12802534108513/100000000000000 : ℝ), (7937189294767/20000000000000 : ℝ), (5938939926009/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42669853/200000000 : ℝ)|^8243 ≤ (12802534108513/100000000000000 : ℝ)^6195
        have hw : |(-42669853/200000000 : ℝ)|=(42669853/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4992944531/10000000000 : ℝ)|^8243 ≤ (7937189294767/20000000000000 : ℝ)^6195
        have hw : |(4992944531/10000000000 : ℝ)|=(4992944531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(714511603/1250000000 : ℝ)|^8243 ≤ (5938939926009/12500000000000 : ℝ)^6195
        have hw : |(714511603/1250000000 : ℝ)|=(714511603/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s1_5 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5234246949/10000000000 : ℝ)*x 0 + (-1802542051/10000000000 : ℝ)*x 1 + (114321883/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5234246949/10000000000 : ℝ)^8243 ≤ (1690325884053/4000000000000 : ℝ)^6195 := by
    have hnat : (5234246949 : ℕ)^8243*4000000000000^6195 ≤ 1690325884053^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234246949 10000000000 1690325884053 4000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1802542051/10000000000 : ℝ)^8243 ≤ (511515940181/5000000000000 : ℝ)^6195 := by
    have hnat : (1802542051 : ℕ)^8243*5000000000000^6195 ≤ 511515940181^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1802542051 10000000000 511515940181 5000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114321883/200000000 : ℝ)^8243 ≤ (9502306814649/20000000000000 : ℝ)^6195 := by
    have hnat : (114321883 : ℕ)^8243*20000000000000^6195 ≤ 9502306814649^6195*200000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114321883 200000000 9502306814649 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5234246949/10000000000 : ℝ), (-1802542051/10000000000 : ℝ), (114321883/200000000 : ℝ)] ![(1690325884053/4000000000000 : ℝ), (511515940181/5000000000000 : ℝ), (9502306814649/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5234246949/10000000000 : ℝ)|^8243 ≤ (1690325884053/4000000000000 : ℝ)^6195
        have hw : |(5234246949/10000000000 : ℝ)|=(5234246949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1802542051/10000000000 : ℝ)|^8243 ≤ (511515940181/5000000000000 : ℝ)^6195
        have hw : |(-1802542051/10000000000 : ℝ)|=(1802542051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(114321883/200000000 : ℝ)|^8243 ≤ (9502306814649/20000000000000 : ℝ)^6195
        have hw : |(114321883/200000000 : ℝ)|=(114321883/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s1_6 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2617122507/5000000000 : ℝ)*x 0 + (5716096277/10000000000 : ℝ)*x 1 + (-180254169/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2617122507/5000000000 : ℝ)^8243 ≤ (8451625262967/20000000000000 : ℝ)^6195 := by
    have hnat : (2617122507 : ℕ)^8243*20000000000000^6195 ≤ 8451625262967^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617122507 5000000000 8451625262967 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5716096277/10000000000 : ℝ)^8243 ≤ (23755778798623/50000000000000 : ℝ)^6195 := by
    have hnat : (5716096277 : ℕ)^8243*50000000000000^6195 ≤ 23755778798623^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5716096277 10000000000 23755778798623 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (180254169/1000000000 : ℝ)^8243 ≤ (10230316077437/100000000000000 : ℝ)^6195 := by
    have hnat : (180254169 : ℕ)^8243*100000000000000^6195 ≤ 10230316077437^6195*1000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180254169 1000000000 10230316077437 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2617122507/5000000000 : ℝ), (5716096277/10000000000 : ℝ), (-180254169/1000000000 : ℝ)] ![(8451625262967/20000000000000 : ℝ), (23755778798623/50000000000000 : ℝ), (10230316077437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2617122507/5000000000 : ℝ)|^8243 ≤ (8451625262967/20000000000000 : ℝ)^6195
        have hw : |(2617122507/5000000000 : ℝ)|=(2617122507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5716096277/10000000000 : ℝ)|^8243 ≤ (23755778798623/50000000000000 : ℝ)^6195
        have hw : |(5716096277/10000000000 : ℝ)|=(5716096277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-180254169/1000000000 : ℝ)|^8243 ≤ (10230316077437/100000000000000 : ℝ)^6195
        have hw : |(-180254169/1000000000 : ℝ)|=(180254169/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s1_7 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4326970253/10000000000 : ℝ)*x 0 + (5093184449/10000000000 : ℝ)*x 1 + (3680416633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4326970253/10000000000 : ℝ)^8243 ≤ (3280274929607/10000000000000 : ℝ)^6195 := by
    have hnat : (4326970253 : ℕ)^8243*10000000000000^6195 ≤ 3280274929607^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326970253 10000000000 3280274929607 10000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5093184449/10000000000 : ℝ)^8243 ≤ (8149918505939/20000000000000 : ℝ)^6195 := by
    have hnat : (5093184449 : ℕ)^8243*20000000000000^6195 ≤ 8149918505939^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5093184449 10000000000 8149918505939 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3680416633/10000000000 : ℝ)^8243 ≤ (6611914538017/25000000000000 : ℝ)^6195 := by
    have hnat : (3680416633 : ℕ)^8243*25000000000000^6195 ≤ 6611914538017^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3680416633 10000000000 6611914538017 25000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4326970253/10000000000 : ℝ), (5093184449/10000000000 : ℝ), (3680416633/10000000000 : ℝ)] ![(3280274929607/10000000000000 : ℝ), (8149918505939/20000000000000 : ℝ), (6611914538017/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4326970253/10000000000 : ℝ)|^8243 ≤ (3280274929607/10000000000000 : ℝ)^6195
        have hw : |(4326970253/10000000000 : ℝ)|=(4326970253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5093184449/10000000000 : ℝ)|^8243 ≤ (8149918505939/20000000000000 : ℝ)^6195
        have hw : |(5093184449/10000000000 : ℝ)|=(5093184449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3680416633/10000000000 : ℝ)|^8243 ≤ (6611914538017/25000000000000 : ℝ)^6195
        have hw : |(3680416633/10000000000 : ℝ)|=(3680416633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1050_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73840941/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7043/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (29/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2559/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5217/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7043/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (29/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7043/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (29/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7043/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (29/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7043/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (29/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7043/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (29/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7043/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (29/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (29/100000 : ℝ) ^ (4121/1024 : ℝ) ≤ (579729/100000000000000000000 : ℝ) := by
    have hpowers : (29/100000 : ℝ)^4121 ≤ (579729/100000000000000000000 : ℝ)^1024 := by
      have hnat : (29 : ℕ)^4121*100000000000000000000^1024 ≤ 579729^1024*100000^4121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29 100000 579729 100000000000000000000 4121 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29/100000 : ℝ)) (X := (579729/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7043/25000 : ℝ) ^ (4121/1024 : ℝ) ≤ (122142984905901679/20000000000000000000 : ℝ) := by
    have hpowers : (7043/25000 : ℝ)^4121 ≤ (122142984905901679/20000000000000000000 : ℝ)^1024 := by
      have hnat : (7043 : ℕ)^4121*20000000000000000000^1024 ≤ 122142984905901679^1024*25000^4121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7043 25000 122142984905901679 20000000000000000000 4121 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7043/25000 : ℝ)) (X := (122142984905901679/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000000000579729/50000000000000000000 : ℝ) ≤ (10000000000000029/10000000000000000 : ℝ) ^ (4121/1024 : ℝ) := by
    have hpowers : (50000000000000579729/50000000000000000000 : ℝ)^1024 ≤ (10000000000000029/10000000000000000 : ℝ)^4121 := by
      have hnat : (50000000000000579729 : ℕ)^1024*10000000000000000^4121 ≤ 10000000000000029^4121*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000000000579729 50000000000000000000 10000000000000029 10000000000000000 1024 4121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000000029/10000000000000000 : ℝ)) (X := (50000000000000579729/50000000000000000000 : ℝ)) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25152678731132522031/25000000000000000000 : ℝ) ≤ (10015140550034633/10000000000000000 : ℝ) ^ (4121/1024 : ℝ) := by
    have hpowers : (25152678731132522031/25000000000000000000 : ℝ)^1024 ≤ (10015140550034633/10000000000000000 : ℝ)^4121 := by
      have hnat : (25152678731132522031 : ℕ)^1024*10000000000000000^4121 ≤ 10015140550034633^4121*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25152678731132522031 25000000000000000000 10015140550034633 10000000000000000 1024 4121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10015140550034633/10000000000000000 : ℝ)) (X := (25152678731132522031/25000000000000000000 : ℝ)) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10122142984905901679/10000000000000000000 : ℝ) ≤ (10030281100069237/10000000000000000 : ℝ) ^ (4121/1024 : ℝ) := by
    have hpowers : (10122142984905901679/10000000000000000000 : ℝ)^1024 ≤ (10030281100069237/10000000000000000 : ℝ)^4121 := by
      have hnat : (10122142984905901679 : ℕ)^1024*10000000000000000^4121 ≤ 10030281100069237^4121*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10122142984905901679 10000000000000000000 10030281100069237 10000000000000000 1024 4121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10030281100069237/10000000000000000 : ℝ)) (X := (10122142984905901679/10000000000000000000 : ℝ)) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(579729/100000000000000000000 : ℝ) ≤ ((56285824369619761823/56286000000000000000 : ℝ)+2*(3785137508651/703575000000000 : ℝ)*(29/100000 : ℝ))^(4121/1024 : ℝ) := by
    rw [show (56285824369619761823/56286000000000000000 : ℝ)+2*(3785137508651/703575000000000 : ℝ)*(29/100000 : ℝ)=(10000000000000029/10000000000000000 : ℝ) by norm_num, show 1+2*(579729/100000000000000000000 : ℝ)=(50000000000000579729/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(122142984905901679/20000000000000000000 : ℝ)+(579729/100000000000000000000 : ℝ) ≤ ((56285824369619761823/56286000000000000000 : ℝ)+(3785137508651/703575000000000 : ℝ)*((7043/25000 : ℝ)+(29/100000 : ℝ)))^(4121/1024 : ℝ) := by
    rw [show (56285824369619761823/56286000000000000000 : ℝ)+(3785137508651/703575000000000 : ℝ)*((7043/25000 : ℝ)+(29/100000 : ℝ))=(10015140550034633/10000000000000000 : ℝ) by norm_num, show 1+(122142984905901679/20000000000000000000 : ℝ)+(579729/100000000000000000000 : ℝ)=(25152678731132522031/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(122142984905901679/20000000000000000000 : ℝ) ≤ ((56285824369619761823/56286000000000000000 : ℝ)+2*(3785137508651/703575000000000 : ℝ)*(7043/25000 : ℝ))^(4121/1024 : ℝ) := by
    rw [show (56285824369619761823/56286000000000000000 : ℝ)+2*(3785137508651/703575000000000 : ℝ)*(7043/25000 : ℝ)=(10030281100069237/10000000000000000 : ℝ) by norm_num, show 1+2*(122142984905901679/20000000000000000000 : ℝ)=(10122142984905901679/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (56285824369619761823/56286000000000000000 : ℝ)*(X 1 0+X 2 0)+(3785137508651/703575000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4121/1024 : ℝ)) (lo := (29/100000 : ℝ)) (hi := (7043/25000 : ℝ)) (c := (56285824369619761823/56286000000000000000 : ℝ)) (alpha := (3785137508651/703575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (56285824369619761823/56286000000000000000 : ℝ)*(X 0 1+X 2 1)+(3785137508651/703575000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4121/1024 : ℝ)) (lo := (29/100000 : ℝ)) (hi := (7043/25000 : ℝ)) (c := (56285824369619761823/56286000000000000000 : ℝ)) (alpha := (3785137508651/703575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (56285824369619761823/56286000000000000000 : ℝ)*(X 0 2+X 1 2)+(3785137508651/703575000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4121/1024 : ℝ)) (lo := (29/100000 : ℝ)) (hi := (7043/25000 : ℝ)) (c := (56285824369619761823/56286000000000000000 : ℝ)) (alpha := (3785137508651/703575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-266568143/1250000000 : ℝ)*X 0 0+(5726834437/10000000000 : ℝ)*X 0 1+(4982419823/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((84753107/156250000 : ℝ)*X 1 0+(-507243297/2000000000 : ℝ)*X 1 1+(1245605037/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2712099643/5000000000 : ℝ)*X 2 0+(4982419617/10000000000 : ℝ)*X 2 1+(-507243317/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1730049/4000000 : ℝ)*X 0 0+(1829717113/5000000000 : ℝ)*X 0 1+(639218663/1250000000 : ℝ)*X 0 2+(1730049/4000000 : ℝ)*X 1 0+(1829717113/5000000000 : ℝ)*X 1 1+(639218663/1250000000 : ℝ)*X 1 2+(1730049/4000000 : ℝ)*X 2 0+(1829717113/5000000000 : ℝ)*X 2 1+(639218663/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-42669853/200000000 : ℝ)*X 0 0+(4992944531/10000000000 : ℝ)*X 0 1+(714511603/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5234246949/10000000000 : ℝ)*X 1 0+(-1802542051/10000000000 : ℝ)*X 1 1+(114321883/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2617122507/5000000000 : ℝ)*X 2 0+(5716096277/10000000000 : ℝ)*X 2 1+(-180254169/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4326970253/10000000000 : ℝ)*X 0 0+(5093184449/10000000000 : ℝ)*X 0 1+(3680416633/10000000000 : ℝ)*X 0 2+(4326970253/10000000000 : ℝ)*X 1 0+(5093184449/10000000000 : ℝ)*X 1 1+(3680416633/10000000000 : ℝ)*X 1 2+(4326970253/10000000000 : ℝ)*X 2 0+(5093184449/10000000000 : ℝ)*X 2 1+(3680416633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26202020560693437107101/3127000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32682573/25000000000000 : ℝ)*(base1) + (932696373/50000000000000 : ℝ)*(base19) + (986933801/50000000000000 : ℝ)*(base23) + (100206067/50000000000000 : ℝ)*(upper3) + (196477791/100000000000000 : ℝ)*(upper5) + (203097465812569/20000000000000 : ℝ)*(major0) + (203097465812569/20000000000000 : ℝ)*(major1) + (203097465812569/20000000000000 : ℝ)*(major2) + (1343346691390161/100000000000000 : ℝ)*(sp0) + (83959651769591/6250000000000 : ℝ)*(sp1) + (6716771599193/500000000000 : ℝ)*(sp2) + (343806650943613/50000000000000 : ℝ)*(sp3) + (9733046333/100000000000000 : ℝ)*(sp4) + (2326246253/50000000000000 : ℝ)*(sp7) + (85952260638753/12500000000000 : ℝ)*(f.failure) + (671678146853101/50000000000000 : ℝ)*(f.sum) + (18126272056691/7035750000000000000000000000 : ℝ)*base65 + (205870413106424429/375240000000000000000000000000000 : ℝ)*base67 + (35654106345855571/375240000000000000000000000000000 : ℝ)*base70 + (85440040964984429/375240000000000000000000000000000 : ℝ)*base71 + (83777829069973/14071500000000000000000000000 : ℝ)*base73 + (1356324642263175571/375240000000000000000000000000000 : ℝ)*base76 + (1091740714853895571/375240000000000000000000000000000 : ℝ)*base78 + (515785999721624429/375240000000000000000000000000000 : ℝ)*base79 + (22438347021539/2814300000000000000000000000 : ℝ)*base81 + (1336573/625000000000000000000 : ℝ)*base89 + (1336573/625000000000000000000 : ℝ)*base91 + (1336573/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (563942518879337352020201001/156350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2482638369/100000000000000 : ℝ)*(base19) + (73486909/3125000000000 : ℝ)*(base23) + (46107747/25000000000000 : ℝ)*(upper2) + (92465001/25000000000000 : ℝ)*(upper3) + (254505687/50000000000000 : ℝ)*(upper5) + (522667740178887/50000000000000 : ℝ)*(major0) + (522667740178887/50000000000000 : ℝ)*(major1) + (522667740178887/50000000000000 : ℝ)*(major2) + (2390826713/20000000000000 : ℝ)*(sp1) + (12719947399/100000000000000 : ℝ)*(sp2) + (1382841642887059/100000000000000 : ℝ)*(sp4) + (11062617648921/800000000000 : ℝ)*(sp5) + (345706642839643/25000000000000 : ℝ)*(sp6) + (141565839519539/20000000000000 : ℝ)*(sp7) + (141565839519539/20000000000000 : ℝ)*(f.failure) + (1382841642887059/100000000000000 : ℝ)*(f.sum) + (162429479695093/46905000000000000000000000000 : ℝ)*base66 + (678710083658112111/312700000000000000000000000000000 : ℝ)*base68 + (1968740227079012111/312700000000000000000000000000000 : ℝ)*base70 + (1509533406747312111/312700000000000000000000000000000 : ℝ)*base72 + (141700010538943/46905000000000000000000000000 : ℝ)*base74 + (1276335419554812111/312700000000000000000000000000000 : ℝ)*base76 + (1830169850635212111/312700000000000000000000000000000 : ℝ)*base78 + (660647999442712111/312700000000000000000000000000000 : ℝ)*base80 + (23296407800171/5863125000000000000000000000 : ℝ)*base82 + (7646199/1000000000000000000000 : ℝ)*base89 + (7646199/1000000000000000000000 : ℝ)*base91 + (7646199/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1050_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73840941/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7043/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (29/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2559/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5217/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1050_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1050_s2_0 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-547719247/2500000000 : ℝ)*x 0 + (1382313899/2500000000 : ℝ)*x 1 + (1285751861/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547719247/2500000000 : ℝ)^8243 ≤ (26525490867/200000000000 : ℝ)^6195 := by
    have hnat : (547719247 : ℕ)^8243*200000000000^6195 ≤ 26525490867^6195*2500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547719247 2500000000 26525490867 200000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1382313899/2500000000 : ℝ)^8243 ≤ (11364100289179/25000000000000 : ℝ)^6195 := by
    have hnat : (1382313899 : ℕ)^8243*25000000000000^6195 ≤ 11364100289179^6195*2500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1382313899 2500000000 11364100289179 25000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1285751861/2500000000 : ℝ)^8243 ≤ (4128085340199/10000000000000 : ℝ)^6195 := by
    have hnat : (1285751861 : ℕ)^8243*10000000000000^6195 ≤ 4128085340199^6195*2500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285751861 2500000000 4128085340199 10000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-547719247/2500000000 : ℝ), (1382313899/2500000000 : ℝ), (1285751861/2500000000 : ℝ)] ![(26525490867/200000000000 : ℝ), (11364100289179/25000000000000 : ℝ), (4128085340199/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-547719247/2500000000 : ℝ)|^8243 ≤ (26525490867/200000000000 : ℝ)^6195
        have hw : |(-547719247/2500000000 : ℝ)|=(547719247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1382313899/2500000000 : ℝ)|^8243 ≤ (11364100289179/25000000000000 : ℝ)^6195
        have hw : |(1382313899/2500000000 : ℝ)|=(1382313899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1285751861/2500000000 : ℝ)|^8243 ≤ (4128085340199/10000000000000 : ℝ)^6195
        have hw : |(1285751861/2500000000 : ℝ)|=(1285751861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s2_1 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (537792519/1000000000 : ℝ)*x 0 + (-2392449541/10000000000 : ℝ)*x 1 + (1285751863/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537792519/1000000000 : ℝ)^8243 ≤ (10952138250189/25000000000000 : ℝ)^6195 := by
    have hnat : (537792519 : ℕ)^8243*25000000000000^6195 ≤ 10952138250189^6195*1000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537792519 1000000000 10952138250189 25000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2392449541/10000000000 : ℝ)^8243 ≤ (3727648372531/25000000000000 : ℝ)^6195 := by
    have hnat : (2392449541 : ℕ)^8243*25000000000000^6195 ≤ 3727648372531^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2392449541 10000000000 3727648372531 25000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1285751863/2500000000 : ℝ)^8243 ≤ (41280853487431/100000000000000 : ℝ)^6195 := by
    have hnat : (1285751863 : ℕ)^8243*100000000000000^6195 ≤ 41280853487431^6195*2500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285751863 2500000000 41280853487431 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537792519/1000000000 : ℝ), (-2392449541/10000000000 : ℝ), (1285751863/2500000000 : ℝ)] ![(10952138250189/25000000000000 : ℝ), (3727648372531/25000000000000 : ℝ), (41280853487431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537792519/1000000000 : ℝ)|^8243 ≤ (10952138250189/25000000000000 : ℝ)^6195
        have hw : |(537792519/1000000000 : ℝ)|=(537792519/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2392449541/10000000000 : ℝ)|^8243 ≤ (3727648372531/25000000000000 : ℝ)^6195
        have hw : |(-2392449541/10000000000 : ℝ)|=(2392449541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1285751863/2500000000 : ℝ)|^8243 ≤ (41280853487431/100000000000000 : ℝ)^6195
        have hw : |(1285751863/2500000000 : ℝ)|=(1285751863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s2_2 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5377925149/10000000000 : ℝ)*x 0 + (5143007487/10000000000 : ℝ)*x 1 + (-47848991/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377925149/10000000000 : ℝ)^8243 ≤ (21904276278179/50000000000000 : ℝ)^6195 := by
    have hnat : (5377925149 : ℕ)^8243*50000000000000^6195 ≤ 21904276278179^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377925149 10000000000 21904276278179 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5143007487/10000000000 : ℝ)^8243 ≤ (20640426930617/50000000000000 : ℝ)^6195 := by
    have hnat : (5143007487 : ℕ)^8243*50000000000000^6195 ≤ 20640426930617^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5143007487 10000000000 20640426930617 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47848991/200000000 : ℝ)^8243 ≤ (7455296782379/50000000000000 : ℝ)^6195 := by
    have hnat : (47848991 : ℕ)^8243*50000000000000^6195 ≤ 7455296782379^6195*200000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47848991 200000000 7455296782379 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377925149/10000000000 : ℝ), (5143007487/10000000000 : ℝ), (-47848991/200000000 : ℝ)] ![(21904276278179/50000000000000 : ℝ), (20640426930617/50000000000000 : ℝ), (7455296782379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377925149/10000000000 : ℝ)|^8243 ≤ (21904276278179/50000000000000 : ℝ)^6195
        have hw : |(5377925149/10000000000 : ℝ)|=(5377925149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5143007487/10000000000 : ℝ)|^8243 ≤ (20640426930617/50000000000000 : ℝ)^6195
        have hw : |(5143007487/10000000000 : ℝ)|=(5143007487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-47848991/200000000 : ℝ)|^8243 ≤ (7455296782379/50000000000000 : ℝ)^6195
        have hw : |(-47848991/200000000 : ℝ)|=(47848991/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s2_3 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364875483/10000000000 : ℝ)*x 0 + (4004086351/10000000000 : ℝ)*x 1 + (594834391/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364875483/10000000000 : ℝ)^8243 ≤ (33185659243439/100000000000000 : ℝ)^6195 := by
    have hnat : (4364875483 : ℕ)^8243*100000000000000^6195 ≤ 33185659243439^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364875483 10000000000 33185659243439 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4004086351/10000000000 : ℝ)^8243 ≤ (14793310527331/50000000000000 : ℝ)^6195 := by
    have hnat : (4004086351 : ℕ)^8243*50000000000000^6195 ≤ 14793310527331^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4004086351 10000000000 14793310527331 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (594834391/1250000000 : ℝ)^8243 ≤ (18613859845213/50000000000000 : ℝ)^6195 := by
    have hnat : (594834391 : ℕ)^8243*50000000000000^6195 ≤ 18613859845213^6195*1250000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      594834391 1250000000 18613859845213 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364875483/10000000000 : ℝ), (4004086351/10000000000 : ℝ), (594834391/1250000000 : ℝ)] ![(33185659243439/100000000000000 : ℝ), (14793310527331/50000000000000 : ℝ), (18613859845213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364875483/10000000000 : ℝ)|^8243 ≤ (33185659243439/100000000000000 : ℝ)^6195
        have hw : |(4364875483/10000000000 : ℝ)|=(4364875483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4004086351/10000000000 : ℝ)|^8243 ≤ (14793310527331/50000000000000 : ℝ)^6195
        have hw : |(4004086351/10000000000 : ℝ)|=(4004086351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(594834391/1250000000 : ℝ)|^8243 ≤ (18613859845213/50000000000000 : ℝ)^6195
        have hw : |(594834391/1250000000 : ℝ)|=(594834391/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s2_4 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-273876087/1250000000 : ℝ)*x 0 + (5145848941/10000000000 : ℝ)*x 1 + (552638383/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273876087/1250000000 : ℝ)^8243 ≤ (6631903168521/50000000000000 : ℝ)^6195 := by
    have hnat : (273876087 : ℕ)^8243*50000000000000^6195 ≤ 6631903168521^6195*1250000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273876087 1250000000 6631903168521 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5145848941/10000000000 : ℝ)^8243 ≤ (8262240731619/20000000000000 : ℝ)^6195 := by
    have hnat : (5145848941 : ℕ)^8243*20000000000000^6195 ≤ 8262240731619^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5145848941 10000000000 8262240731619 20000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (552638383/1000000000 : ℝ)^8243 ≤ (45424989985411/100000000000000 : ℝ)^6195 := by
    have hnat : (552638383 : ℕ)^8243*100000000000000^6195 ≤ 45424989985411^6195*1000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552638383 1000000000 45424989985411 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-273876087/1250000000 : ℝ), (5145848941/10000000000 : ℝ), (552638383/1000000000 : ℝ)] ![(6631903168521/50000000000000 : ℝ), (8262240731619/20000000000000 : ℝ), (45424989985411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-273876087/1250000000 : ℝ)|^8243 ≤ (6631903168521/50000000000000 : ℝ)^6195
        have hw : |(-273876087/1250000000 : ℝ)|=(273876087/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5145848941/10000000000 : ℝ)|^8243 ≤ (8262240731619/20000000000000 : ℝ)^6195
        have hw : |(5145848941/10000000000 : ℝ)|=(5145848941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(552638383/1000000000 : ℝ)|^8243 ≤ (45424989985411/100000000000000 : ℝ)^6195
        have hw : |(552638383/1000000000 : ℝ)|=(552638383/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s2_5 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1320135693/2500000000 : ℝ)*x 0 + (-2009073323/10000000000 : ℝ)*x 1 + (2763191949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1320135693/2500000000 : ℝ)^8243 ≤ (21378099882191/50000000000000 : ℝ)^6195 := by
    have hnat : (1320135693 : ℕ)^8243*50000000000000^6195 ≤ 21378099882191^6195*2500000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320135693 2500000000 21378099882191 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2009073323/10000000000 : ℝ)^8243 ≤ (2954702373941/25000000000000 : ℝ)^6195 := by
    have hnat : (2009073323 : ℕ)^8243*25000000000000^6195 ≤ 2954702373941^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009073323 10000000000 2954702373941 25000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2763191949/5000000000 : ℝ)^8243 ≤ (22712495364563/50000000000000 : ℝ)^6195 := by
    have hnat : (2763191949 : ℕ)^8243*50000000000000^6195 ≤ 22712495364563^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2763191949 5000000000 22712495364563 50000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1320135693/2500000000 : ℝ), (-2009073323/10000000000 : ℝ), (2763191949/5000000000 : ℝ)] ![(21378099882191/50000000000000 : ℝ), (2954702373941/25000000000000 : ℝ), (22712495364563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1320135693/2500000000 : ℝ)|^8243 ≤ (21378099882191/50000000000000 : ℝ)^6195
        have hw : |(1320135693/2500000000 : ℝ)|=(1320135693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2009073323/10000000000 : ℝ)|^8243 ≤ (2954702373941/25000000000000 : ℝ)^6195
        have hw : |(-2009073323/10000000000 : ℝ)|=(2009073323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2763191949/5000000000 : ℝ)|^8243 ≤ (22712495364563/50000000000000 : ℝ)^6195
        have hw : |(2763191949/5000000000 : ℝ)|=(2763191949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s2_6 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2640271501/5000000000 : ℝ)*x 0 + (5526383737/10000000000 : ℝ)*x 1 + (-200907323/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640271501/5000000000 : ℝ)^8243 ≤ (42756202242331/100000000000000 : ℝ)^6195 := by
    have hnat : (2640271501 : ℕ)^8243*100000000000000^6195 ≤ 42756202242331^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640271501 5000000000 42756202242331 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5526383737/10000000000 : ℝ)^8243 ≤ (45424988968271/100000000000000 : ℝ)^6195 := by
    have hnat : (5526383737 : ℕ)^8243*100000000000000^6195 ≤ 45424988968271^6195*10000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5526383737 10000000000 45424988968271 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200907323/1000000000 : ℝ)^8243 ≤ (11818808767809/100000000000000 : ℝ)^6195 := by
    have hnat : (200907323 : ℕ)^8243*100000000000000^6195 ≤ 11818808767809^6195*1000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200907323 1000000000 11818808767809 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640271501/5000000000 : ℝ), (5526383737/10000000000 : ℝ), (-200907323/1000000000 : ℝ)] ![(42756202242331/100000000000000 : ℝ), (45424988968271/100000000000000 : ℝ), (11818808767809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640271501/5000000000 : ℝ)|^8243 ≤ (42756202242331/100000000000000 : ℝ)^6195
        have hw : |(2640271501/5000000000 : ℝ)|=(2640271501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5526383737/10000000000 : ℝ)|^8243 ≤ (45424988968271/100000000000000 : ℝ)^6195
        have hw : |(5526383737/10000000000 : ℝ)|=(5526383737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-200907323/1000000000 : ℝ)|^8243 ≤ (11818808767809/100000000000000 : ℝ)^6195
        have hw : |(-200907323/1000000000 : ℝ)|=(200907323/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1050_s2_7 (p : ℝ) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2182566311/5000000000 : ℝ)*x 0 + (594140499/1250000000 : ℝ)*x 1 + (2004848267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182566311/5000000000 : ℝ)^8243 ≤ (4148532571163/12500000000000 : ℝ)^6195 := by
    have hnat : (2182566311 : ℕ)^8243*12500000000000^6195 ≤ 4148532571163^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182566311 5000000000 4148532571163 12500000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (594140499/1250000000 : ℝ)^8243 ≤ (37169947017127/100000000000000 : ℝ)^6195 := by
    have hnat : (594140499 : ℕ)^8243*100000000000000^6195 ≤ 37169947017127^6195*1250000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      594140499 1250000000 37169947017127 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2004848267/5000000000 : ℝ)^8243 ≤ (29641792389247/100000000000000 : ℝ)^6195 := by
    have hnat : (2004848267 : ℕ)^8243*100000000000000^6195 ≤ 29641792389247^6195*5000000000^8243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004848267 5000000000 29641792389247 100000000000000 8243 6195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8243/2048 : ℝ)) 8243 6195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182566311/5000000000 : ℝ), (594140499/1250000000 : ℝ), (2004848267/5000000000 : ℝ)] ![(4148532571163/12500000000000 : ℝ), (37169947017127/100000000000000 : ℝ), (29641792389247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182566311/5000000000 : ℝ)|^8243 ≤ (4148532571163/12500000000000 : ℝ)^6195
        have hw : |(2182566311/5000000000 : ℝ)|=(2182566311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(594140499/1250000000 : ℝ)|^8243 ≤ (37169947017127/100000000000000 : ℝ)^6195
        have hw : |(594140499/1250000000 : ℝ)|=(594140499/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2004848267/5000000000 : ℝ)|^8243 ≤ (29641792389247/100000000000000 : ℝ)^6195
        have hw : |(2004848267/5000000000 : ℝ)|=(2004848267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1050_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73840941/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5217/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2559/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1079/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8397/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5217/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2559/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5217/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2559/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5217/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2559/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5217/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2559/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5217/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2559/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5217/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2559/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2559/50000 : ℝ) ^ (4121/1024 : ℝ) ≤ (638094527214033/100000000000000000000 : ℝ) := by
    have hpowers : (2559/50000 : ℝ)^4121 ≤ (638094527214033/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2559 : ℕ)^4121*100000000000000000000^1024 ≤ 638094527214033^1024*50000^4121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2559 50000 638094527214033 100000000000000000000 4121 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2559/50000 : ℝ)) (X := (638094527214033/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5217/25000 : ℝ) ^ (4121/1024 : ℝ) ≤ (182519417721655273/100000000000000000000 : ℝ) := by
    have hpowers : (5217/25000 : ℝ)^4121 ≤ (182519417721655273/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5217 : ℕ)^4121*100000000000000000000^1024 ≤ 182519417721655273^1024*25000^4121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5217 25000 182519417721655273 100000000000000000000 4121 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5217/25000 : ℝ)) (X := (182519417721655273/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000638094527214033/50000000000000000000 : ℝ) ≤ (10000031711024633/10000000000000000 : ℝ) ^ (4121/1024 : ℝ) := by
    have hpowers : (50000638094527214033/50000000000000000000 : ℝ)^1024 ≤ (10000031711024633/10000000000000000 : ℝ)^4121 := by
      have hnat : (50000638094527214033 : ℕ)^1024*10000000000000000^4121 ≤ 10000031711024633^4121*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000638094527214033 50000000000000000000 10000031711024633 10000000000000000 1024 4121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000031711024633/10000000000000000 : ℝ)) (X := (50000638094527214033/50000000000000000000 : ℝ)) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50091578756124434653/50000000000000000000 : ℝ) ≤ (2000909606166839/2000000000000000 : ℝ) ^ (4121/1024 : ℝ) := by
    have hpowers : (50091578756124434653/50000000000000000000 : ℝ)^1024 ≤ (2000909606166839/2000000000000000 : ℝ)^4121 := by
      have hnat : (50091578756124434653 : ℕ)^1024*2000000000000000^4121 ≤ 2000909606166839^4121*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50091578756124434653 50000000000000000000 2000909606166839 2000000000000000 1024 4121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000909606166839/2000000000000000 : ℝ)) (X := (50091578756124434653/50000000000000000000 : ℝ)) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50182519417721655273/50000000000000000000 : ℝ) ≤ (10009064350643757/10000000000000000 : ℝ) ^ (4121/1024 : ℝ) := by
    have hpowers : (50182519417721655273/50000000000000000000 : ℝ)^1024 ≤ (10009064350643757/10000000000000000 : ℝ)^4121 := by
      have hnat : (50182519417721655273 : ℕ)^1024*10000000000000000^4121 ≤ 10009064350643757^4121*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50182519417721655273 50000000000000000000 10009064350643757 10000000000000000 1024 4121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009064350643757/10000000000000000 : ℝ)) (X := (50182519417721655273/50000000000000000000 : ℝ)) (by norm_num) 4121 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(638094527214033/100000000000000000000 : ℝ) ≤ ((26242378399844548853/26250000000000000000 : ℝ)+2*(2258159904781/787500000000000 : ℝ)*(2559/50000 : ℝ))^(4121/1024 : ℝ) := by
    rw [show (26242378399844548853/26250000000000000000 : ℝ)+2*(2258159904781/787500000000000 : ℝ)*(2559/50000 : ℝ)=(10000031711024633/10000000000000000 : ℝ) by norm_num, show 1+2*(638094527214033/100000000000000000000 : ℝ)=(50000638094527214033/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(182519417721655273/100000000000000000000 : ℝ)+(638094527214033/100000000000000000000 : ℝ) ≤ ((26242378399844548853/26250000000000000000 : ℝ)+(2258159904781/787500000000000 : ℝ)*((5217/25000 : ℝ)+(2559/50000 : ℝ)))^(4121/1024 : ℝ) := by
    rw [show (26242378399844548853/26250000000000000000 : ℝ)+(2258159904781/787500000000000 : ℝ)*((5217/25000 : ℝ)+(2559/50000 : ℝ))=(2000909606166839/2000000000000000 : ℝ) by norm_num, show 1+(182519417721655273/100000000000000000000 : ℝ)+(638094527214033/100000000000000000000 : ℝ)=(50091578756124434653/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(182519417721655273/100000000000000000000 : ℝ) ≤ ((26242378399844548853/26250000000000000000 : ℝ)+2*(2258159904781/787500000000000 : ℝ)*(5217/25000 : ℝ))^(4121/1024 : ℝ) := by
    rw [show (26242378399844548853/26250000000000000000 : ℝ)+2*(2258159904781/787500000000000 : ℝ)*(5217/25000 : ℝ)=(10009064350643757/10000000000000000 : ℝ) by norm_num, show 1+2*(182519417721655273/100000000000000000000 : ℝ)=(50182519417721655273/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26242378399844548853/26250000000000000000 : ℝ)*(X 1 0+X 2 0)+(2258159904781/787500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4121/1024 : ℝ)) (lo := (2559/50000 : ℝ)) (hi := (5217/25000 : ℝ)) (c := (26242378399844548853/26250000000000000000 : ℝ)) (alpha := (2258159904781/787500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26242378399844548853/26250000000000000000 : ℝ)*(X 0 1+X 2 1)+(2258159904781/787500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4121/1024 : ℝ)) (lo := (2559/50000 : ℝ)) (hi := (5217/25000 : ℝ)) (c := (26242378399844548853/26250000000000000000 : ℝ)) (alpha := (2258159904781/787500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26242378399844548853/26250000000000000000 : ℝ)*(X 0 2+X 1 2)+(2258159904781/787500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4121/1024 : ℝ)) (lo := (2559/50000 : ℝ)) (hi := (5217/25000 : ℝ)) (c := (26242378399844548853/26250000000000000000 : ℝ)) (alpha := (2258159904781/787500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-547719247/2500000000 : ℝ)*X 0 0+(1382313899/2500000000 : ℝ)*X 0 1+(1285751861/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((537792519/1000000000 : ℝ)*X 1 0+(-2392449541/10000000000 : ℝ)*X 1 1+(1285751863/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5377925149/10000000000 : ℝ)*X 2 0+(5143007487/10000000000 : ℝ)*X 2 1+(-47848991/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364875483/10000000000 : ℝ)*X 0 0+(4004086351/10000000000 : ℝ)*X 0 1+(594834391/1250000000 : ℝ)*X 0 2+(4364875483/10000000000 : ℝ)*X 1 0+(4004086351/10000000000 : ℝ)*X 1 1+(594834391/1250000000 : ℝ)*X 1 2+(4364875483/10000000000 : ℝ)*X 2 0+(4004086351/10000000000 : ℝ)*X 2 1+(594834391/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-273876087/1250000000 : ℝ)*X 0 0+(5145848941/10000000000 : ℝ)*X 0 1+(552638383/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1320135693/2500000000 : ℝ)*X 1 0+(-2009073323/10000000000 : ℝ)*X 1 1+(2763191949/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2640271501/5000000000 : ℝ)*X 2 0+(5526383737/10000000000 : ℝ)*X 2 1+(-200907323/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2182566311/5000000000 : ℝ)*X 0 0+(594140499/1250000000 : ℝ)*X 0 1+(2004848267/5000000000 : ℝ)*X 0 2+(2182566311/5000000000 : ℝ)*X 1 0+(594140499/1250000000 : ℝ)*X 1 1+(2004848267/5000000000 : ℝ)*X 1 2+(2182566311/5000000000 : ℝ)*X 2 0+(594140499/1250000000 : ℝ)*X 2 1+(2004848267/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1050_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (420748268968497704758373123/46875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53857449/50000000000000 : ℝ)*(base1) + (1870046827/100000000000000 : ℝ)*(base19) + (1850308599/100000000000000 : ℝ)*(base23) + (98863907/50000000000000 : ℝ)*(upper3) + (188151909/100000000000000 : ℝ)*(upper5) + (978571524625621/50000000000000 : ℝ)*(major0) + (978571524625621/50000000000000 : ℝ)*(major1) + (978571524625621/50000000000000 : ℝ)*(major2) + (1294513137313603/50000000000000 : ℝ)*(sp0) + (2589041439964089/100000000000000 : ℝ)*(sp1) + (647260364925579/25000000000000 : ℝ)*(sp2) + (331308416983771/25000000000000 : ℝ)*(sp3) + (17143098607/100000000000000 : ℝ)*(sp4) + (1089205351/12500000000000 : ℝ)*(sp7) + (1325242489292791/100000000000000 : ℝ)*(f.failure) + (647260827502729/25000000000000 : ℝ)*(f.sum) + (52354224455251/19687500000000000000000000000 : ℝ)*base65 + (39969279166747488139/3937500000000000000000000000000000 : ℝ)*base67 + (9422522263934988139/3937500000000000000000000000000000 : ℝ)*base69 + (41044326621434988139/3937500000000000000000000000000000 : ℝ)*base71 + (103922967942377/39375000000000000000000000000 : ℝ)*base73 + (5288548492440011861/3937500000000000000000000000000000 : ℝ)*base76 + (8199894123809988139/3937500000000000000000000000000000 : ℝ)*base77 + (55324072571309988139/3937500000000000000000000000000000 : ℝ)*base79 + (28023343396501/19687500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (11956331/5000000000000000000000 : ℝ)*base89 + (11956331/5000000000000000000000 : ℝ)*base91 + (11956331/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (797833598018885416571203637/218750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (333001467/50000000000000 : ℝ)*(base19) + (25667213/3125000000000 : ℝ)*(base23) + (52439499/50000000000000 : ℝ)*(upper3) + (881721/10000000000000 : ℝ)*(lower4) + (16378361/20000000000000 : ℝ)*(upper5) + (993250399057557/50000000000000 : ℝ)*(major0) + (993250399057557/50000000000000 : ℝ)*(major1) + (993250399057557/50000000000000 : ℝ)*(major2) + (2751013163/50000000000000 : ℝ)*(sp1) + (34068743/500000000000 : ℝ)*(sp2) + (1313939969814307/50000000000000 : ℝ)*(sp4) + (1313936885799677/50000000000000 : ℝ)*(sp5) + (1313936152264599/50000000000000 : ℝ)*(sp6) + (1345121535026967/100000000000000 : ℝ)*(sp7) + (1345121535026967/100000000000000 : ℝ)*(f.failure) + (1313939969814307/50000000000000 : ℝ)*(f.sum) + (10100789117393/3281250000000000000000000000 : ℝ)*base66 + (7848063369504232121/1312500000000000000000000000000000 : ℝ)*base67 + (10838130047004232121/1312500000000000000000000000000000 : ℝ)*base69 + (5077311998004232121/1312500000000000000000000000000000 : ℝ)*base71 + (12481797280411/6562500000000000000000000000 : ℝ)*base74 + (1970786040504232121/1312500000000000000000000000000000 : ℝ)*base75 + (2420821752504232121/1312500000000000000000000000000000 : ℝ)*base77 + (10053820220004232121/1312500000000000000000000000000000 : ℝ)*base79 + (164918185991/1640625000000000000000000000 : ℝ)*base81 + (3655947/5000000000000000000000 : ℝ)*base89 + (3655947/5000000000000000000000 : ℝ)*base91 + (3655947/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1050_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73840941/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5217/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2559/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1079/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8397/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1050_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1050_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73840941/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1079/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8397/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1050_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1050_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1050_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4121/1024 : ℝ) ≤ p) (hpb : p ≤ (8243/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73840941/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1079/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8397/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1050_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
