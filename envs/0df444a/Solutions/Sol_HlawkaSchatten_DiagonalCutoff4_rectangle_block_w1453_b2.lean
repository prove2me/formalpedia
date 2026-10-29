-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1453_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:59:47.461927+00:00
-- url     : https://prove2.me/submissions/6e9fc254-1021-4308-85db-900cc4c6826b

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
theorem support_rectangle_w1453_s6_0 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-975911463/5000000000 : ℝ)*x 0 + (1351746103/2500000000 : ℝ)*x 1 + (5247415157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (975911463/5000000000 : ℝ)^4413 ≤ (11913630553779/100000000000000 : ℝ)^3389 := by
    have hnat : (975911463 : ℕ)^4413*100000000000000^3389 ≤ 11913630553779^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975911463 5000000000 11913630553779 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351746103/2500000000 : ℝ)^4413 ≤ (44902077043839/100000000000000 : ℝ)^3389 := by
    have hnat : (1351746103 : ℕ)^4413*100000000000000^3389 ≤ 44902077043839^3389*2500000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351746103 2500000000 44902077043839 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247415157/10000000000 : ℝ)^4413 ≤ (43184292388637/100000000000000 : ℝ)^3389 := by
    have hnat : (5247415157 : ℕ)^4413*100000000000000^3389 ≤ 43184292388637^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247415157 10000000000 43184292388637 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-975911463/5000000000 : ℝ), (1351746103/2500000000 : ℝ), (5247415157/10000000000 : ℝ)] ![(11913630553779/100000000000000 : ℝ), (44902077043839/100000000000000 : ℝ), (43184292388637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-975911463/5000000000 : ℝ)|^4413 ≤ (11913630553779/100000000000000 : ℝ)^3389
        have hw : |(-975911463/5000000000 : ℝ)|=(975911463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351746103/2500000000 : ℝ)|^4413 ≤ (44902077043839/100000000000000 : ℝ)^3389
        have hw : |(1351746103/2500000000 : ℝ)|=(1351746103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247415157/10000000000 : ℝ)|^4413 ≤ (43184292388637/100000000000000 : ℝ)^3389
        have hw : |(5247415157/10000000000 : ℝ)|=(5247415157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s6_1 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334175719/625000000 : ℝ)*x 0 + (-508261531/2500000000 : ℝ)*x 1 + (524741513/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334175719/625000000 : ℝ)^4413 ≤ (8850496616971/20000000000000 : ℝ)^3389 := by
    have hnat : (334175719 : ℕ)^4413*20000000000000^3389 ≤ 8850496616971^3389*625000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334175719 625000000 8850496616971 20000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508261531/2500000000 : ℝ)^4413 ≤ (12563224805851/100000000000000 : ℝ)^3389 := by
    have hnat : (508261531 : ℕ)^4413*100000000000000^3389 ≤ 12563224805851^3389*2500000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508261531 2500000000 12563224805851 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524741513/1000000000 : ℝ)^4413 ≤ (21592146049649/50000000000000 : ℝ)^3389 := by
    have hnat : (524741513 : ℕ)^4413*50000000000000^3389 ≤ 21592146049649^3389*1000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524741513 1000000000 21592146049649 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334175719/625000000 : ℝ), (-508261531/2500000000 : ℝ), (524741513/1000000000 : ℝ)] ![(8850496616971/20000000000000 : ℝ), (12563224805851/100000000000000 : ℝ), (21592146049649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334175719/625000000 : ℝ)|^4413 ≤ (8850496616971/20000000000000 : ℝ)^3389
        have hw : |(334175719/625000000 : ℝ)|=(334175719/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-508261531/2500000000 : ℝ)|^4413 ≤ (12563224805851/100000000000000 : ℝ)^3389
        have hw : |(-508261531/2500000000 : ℝ)|=(508261531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524741513/1000000000 : ℝ)|^4413 ≤ (21592146049649/50000000000000 : ℝ)^3389
        have hw : |(524741513/1000000000 : ℝ)|=(524741513/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s6_2 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069362309/2000000000 : ℝ)*x 0 + (655926893/1250000000 : ℝ)*x 1 + (-40660921/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069362309/2000000000 : ℝ)^4413 ≤ (44252483526719/100000000000000 : ℝ)^3389 := by
    have hnat : (1069362309 : ℕ)^4413*100000000000000^3389 ≤ 44252483526719^3389*2000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069362309 2000000000 44252483526719 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655926893/1250000000 : ℝ)^4413 ≤ (21592146124663/50000000000000 : ℝ)^3389 := by
    have hnat : (655926893 : ℕ)^4413*50000000000000^3389 ≤ 21592146124663^3389*1250000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655926893 1250000000 21592146124663 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40660921/200000000 : ℝ)^4413 ≤ (12563224210397/100000000000000 : ℝ)^3389 := by
    have hnat : (40660921 : ℕ)^4413*100000000000000^3389 ≤ 12563224210397^3389*200000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40660921 200000000 12563224210397 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069362309/2000000000 : ℝ), (655926893/1250000000 : ℝ), (-40660921/200000000 : ℝ)] ![(44252483526719/100000000000000 : ℝ), (21592146124663/50000000000000 : ℝ), (12563224210397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069362309/2000000000 : ℝ)|^4413 ≤ (44252483526719/100000000000000 : ℝ)^3389
        have hw : |(1069362309/2000000000 : ℝ)|=(1069362309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655926893/1250000000 : ℝ)|^4413 ≤ (21592146124663/50000000000000 : ℝ)^3389
        have hw : |(655926893/1250000000 : ℝ)|=(655926893/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-40660921/200000000 : ℝ)|^4413 ≤ (12563224210397/100000000000000 : ℝ)^3389
        have hw : |(-40660921/200000000 : ℝ)|=(40660921/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s6_3 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537301023/1250000000 : ℝ)*x 0 + (4127427793/10000000000 : ℝ)*x 1 + (447566739/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537301023/1250000000 : ℝ)^4413 ≤ (8326262409927/25000000000000 : ℝ)^3389 := by
    have hnat : (537301023 : ℕ)^4413*25000000000000^3389 ≤ 8326262409927^3389*1250000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537301023 1250000000 8326262409927 25000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4127427793/10000000000 : ℝ)^4413 ≤ (31590426730841/100000000000000 : ℝ)^3389 := by
    have hnat : (4127427793 : ℕ)^4413*100000000000000^3389 ≤ 31590426730841^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127427793 10000000000 31590426730841 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447566739/1000000000 : ℝ)^4413 ≤ (17552261803411/50000000000000 : ℝ)^3389 := by
    have hnat : (447566739 : ℕ)^4413*50000000000000^3389 ≤ 17552261803411^3389*1000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447566739 1000000000 17552261803411 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537301023/1250000000 : ℝ), (4127427793/10000000000 : ℝ), (447566739/1000000000 : ℝ)] ![(8326262409927/25000000000000 : ℝ), (31590426730841/100000000000000 : ℝ), (17552261803411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537301023/1250000000 : ℝ)|^4413 ≤ (8326262409927/25000000000000 : ℝ)^3389
        have hw : |(537301023/1250000000 : ℝ)|=(537301023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4127427793/10000000000 : ℝ)|^4413 ≤ (31590426730841/100000000000000 : ℝ)^3389
        have hw : |(4127427793/10000000000 : ℝ)|=(4127427793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(447566739/1000000000 : ℝ)|^4413 ≤ (17552261803411/50000000000000 : ℝ)^3389
        have hw : |(447566739/1000000000 : ℝ)|=(447566739/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s6_4 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1951834001/10000000000 : ℝ)*x 0 + (5247991923/10000000000 : ℝ)*x 1 + (5406404683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1951834001/10000000000 : ℝ)^4413 ≤ (11913718579619/100000000000000 : ℝ)^3389 := by
    have hnat : (1951834001 : ℕ)^4413*100000000000000^3389 ≤ 11913718579619^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951834001 10000000000 11913718579619 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247991923/10000000000 : ℝ)^4413 ≤ (43190473258553/100000000000000 : ℝ)^3389 := by
    have hnat : (5247991923 : ℕ)^4413*100000000000000^3389 ≤ 43190473258553^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247991923 10000000000 43190473258553 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406404683/10000000000 : ℝ)^4413 ≤ (22447904069607/50000000000000 : ℝ)^3389 := by
    have hnat : (5406404683 : ℕ)^4413*50000000000000^3389 ≤ 22447904069607^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406404683 10000000000 22447904069607 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1951834001/10000000000 : ℝ), (5247991923/10000000000 : ℝ), (5406404683/10000000000 : ℝ)] ![(11913718579619/100000000000000 : ℝ), (43190473258553/100000000000000 : ℝ), (22447904069607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1951834001/10000000000 : ℝ)|^4413 ≤ (11913718579619/100000000000000 : ℝ)^3389
        have hw : |(-1951834001/10000000000 : ℝ)|=(1951834001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247991923/10000000000 : ℝ)|^4413 ≤ (43190473258553/100000000000000 : ℝ)^3389
        have hw : |(5247991923/10000000000 : ℝ)|=(5247991923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406404683/10000000000 : ℝ)|^4413 ≤ (22447904069607/50000000000000 : ℝ)^3389
        have hw : |(5406404683/10000000000 : ℝ)|=(5406404683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s6_5 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (106104647/200000000 : ℝ)*x 0 + (-374811311/2000000000 : ℝ)*x 1 + (5406404683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106104647/200000000 : ℝ)^4413 ≤ (10951226118493/25000000000000 : ℝ)^3389 := by
    have hnat : (106104647 : ℕ)^4413*25000000000000^3389 ≤ 10951226118493^3389*200000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106104647 200000000 10951226118493 25000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (374811311/2000000000 : ℝ)^4413 ≤ (2824821845163/25000000000000 : ℝ)^3389 := by
    have hnat : (374811311 : ℕ)^4413*25000000000000^3389 ≤ 2824821845163^3389*2000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374811311 2000000000 2824821845163 25000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406404683/10000000000 : ℝ)^4413 ≤ (22447904069607/50000000000000 : ℝ)^3389 := by
    have hnat : (5406404683 : ℕ)^4413*50000000000000^3389 ≤ 22447904069607^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406404683 10000000000 22447904069607 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106104647/200000000 : ℝ), (-374811311/2000000000 : ℝ), (5406404683/10000000000 : ℝ)] ![(10951226118493/25000000000000 : ℝ), (2824821845163/25000000000000 : ℝ), (22447904069607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106104647/200000000 : ℝ)|^4413 ≤ (10951226118493/25000000000000 : ℝ)^3389
        have hw : |(106104647/200000000 : ℝ)|=(106104647/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-374811311/2000000000 : ℝ)|^4413 ≤ (2824821845163/25000000000000 : ℝ)^3389
        have hw : |(-374811311/2000000000 : ℝ)|=(374811311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406404683/10000000000 : ℝ)|^4413 ≤ (22447904069607/50000000000000 : ℝ)^3389
        have hw : |(5406404683/10000000000 : ℝ)|=(5406404683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s6_6 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305232349/10000000000 : ℝ)*x 0 + (5406404683/10000000000 : ℝ)*x 1 + (-468514139/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305232349/10000000000 : ℝ)^4413 ≤ (2190245223161/5000000000000 : ℝ)^3389 := by
    have hnat : (5305232349 : ℕ)^4413*5000000000000^3389 ≤ 2190245223161^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305232349 10000000000 2190245223161 5000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406404683/10000000000 : ℝ)^4413 ≤ (22447904069607/50000000000000 : ℝ)^3389 := by
    have hnat : (5406404683 : ℕ)^4413*50000000000000^3389 ≤ 22447904069607^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406404683 10000000000 22447904069607 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (468514139/2500000000 : ℝ)^4413 ≤ (11299287388503/100000000000000 : ℝ)^3389 := by
    have hnat : (468514139 : ℕ)^4413*100000000000000^3389 ≤ 11299287388503^3389*2500000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468514139 2500000000 11299287388503 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305232349/10000000000 : ℝ), (5406404683/10000000000 : ℝ), (-468514139/2500000000 : ℝ)] ![(2190245223161/5000000000000 : ℝ), (22447904069607/50000000000000 : ℝ), (11299287388503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305232349/10000000000 : ℝ)|^4413 ≤ (2190245223161/5000000000000 : ℝ)^3389
        have hw : |(5305232349/10000000000 : ℝ)|=(5305232349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406404683/10000000000 : ℝ)|^4413 ≤ (22447904069607/50000000000000 : ℝ)^3389
        have hw : |(5406404683/10000000000 : ℝ)|=(5406404683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-468514139/2500000000 : ℝ)|^4413 ≤ (11299287388503/100000000000000 : ℝ)^3389
        have hw : |(-468514139/2500000000 : ℝ)|=(468514139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s6_7 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (859686481/2000000000 : ℝ)*x 0 + (559301079/1250000000 : ℝ)*x 1 + (2064346553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (859686481/2000000000 : ℝ)^4413 ≤ (33305294014963/100000000000000 : ℝ)^3389 := by
    have hnat : (859686481 : ℕ)^4413*100000000000000^3389 ≤ 33305294014963^3389*2000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859686481 2000000000 33305294014963 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (559301079/1250000000 : ℝ)^4413 ≤ (3509166803417/10000000000000 : ℝ)^3389 := by
    have hnat : (559301079 : ℕ)^4413*10000000000000^3389 ≤ 3509166803417^3389*1250000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559301079 1250000000 3509166803417 10000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2064346553/5000000000 : ℝ)^4413 ≤ (6320607586377/20000000000000 : ℝ)^3389 := by
    have hnat : (2064346553 : ℕ)^4413*20000000000000^3389 ≤ 6320607586377^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064346553 5000000000 6320607586377 20000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(859686481/2000000000 : ℝ), (559301079/1250000000 : ℝ), (2064346553/5000000000 : ℝ)] ![(33305294014963/100000000000000 : ℝ), (3509166803417/10000000000000 : ℝ), (6320607586377/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(859686481/2000000000 : ℝ)|^4413 ≤ (33305294014963/100000000000000 : ℝ)^3389
        have hw : |(859686481/2000000000 : ℝ)|=(859686481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(559301079/1250000000 : ℝ)|^4413 ≤ (3509166803417/10000000000000 : ℝ)^3389
        have hw : |(559301079/1250000000 : ℝ)|=(559301079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2064346553/5000000000 : ℝ)|^4413 ≤ (6320607586377/20000000000000 : ℝ)^3389
        have hw : |(2064346553/5000000000 : ℝ)|=(2064346553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1453_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79559293/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2847/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14769/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3693/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2277/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3693/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2277/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3693/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2277/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3693/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2277/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3693/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2277/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3693/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2277/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2277/20000 : ℝ) ^ (1103/256 : ℝ) ≤ (268517400397009/3125000000000000000 : ℝ) := by
    have hpowers : (2277/20000 : ℝ)^1103 ≤ (268517400397009/3125000000000000000 : ℝ)^256 := by
      have hnat : (2277 : ℕ)^1103*3125000000000000000^256 ≤ 268517400397009^256*20000^1103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2277 20000 268517400397009 3125000000000000000 1103 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2277/20000 : ℝ)) (X := (268517400397009/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3693/25000 : ℝ) ^ (1103/256 : ℝ) ≤ (659768175682321/2500000000000000000 : ℝ) := by
    have hpowers : (3693/25000 : ℝ)^1103 ≤ (659768175682321/2500000000000000000 : ℝ)^256 := by
      have hnat : (3693 : ℕ)^1103*2500000000000000000^256 ≤ 659768175682321^256*25000^1103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3693 25000 659768175682321 2500000000000000000 1103 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3693/25000 : ℝ)) (X := (659768175682321/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562768517400397009/1562500000000000000 : ℝ) ≤ (2500099707589161/2500000000000000 : ℝ) ^ (1103/256 : ℝ) := by
    have hpowers : (1562768517400397009/1562500000000000000 : ℝ)^256 ≤ (2500099707589161/2500000000000000 : ℝ)^1103 := by
      have hnat : (1562768517400397009 : ℕ)^256*2500000000000000^1103 ≤ 2500099707589161^1103*1562500000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562768517400397009 1562500000000000000 2500099707589161 2500000000000000 256 1103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500099707589161/2500000000000000 : ℝ)) (X := (1562768517400397009/1562500000000000000 : ℝ)) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (12504372910479999641/12500000000000000000 : ℝ) ≤ (10000811832999519/10000000000000000 : ℝ) ^ (1103/256 : ℝ) := by
    have hpowers : (12504372910479999641/12500000000000000000 : ℝ)^256 ≤ (10000811832999519/10000000000000000 : ℝ)^1103 := by
      have hnat : (12504372910479999641 : ℕ)^256*10000000000000000^1103 ≤ 10000811832999519^1103*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504372910479999641 12500000000000000000 10000811832999519 10000000000000000 256 1103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000811832999519/10000000000000000 : ℝ)) (X := (12504372910479999641/12500000000000000000 : ℝ)) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250659768175682321/1250000000000000000 : ℝ) ≤ (5000612417821197/5000000000000000 : ℝ) ^ (1103/256 : ℝ) := by
    have hpowers : (1250659768175682321/1250000000000000000 : ℝ)^256 ≤ (5000612417821197/5000000000000000 : ℝ)^1103 := by
      have hnat : (1250659768175682321 : ℕ)^256*5000000000000000^1103 ≤ 5000612417821197^1103*1250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250659768175682321 1250000000000000000 5000612417821197 5000000000000000 256 1103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000612417821197/5000000000000000 : ℝ)) (X := (1250659768175682321/1250000000000000000 : ℝ)) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(268517400397009/3125000000000000000 : ℝ) ≤ ((5643657794706614913/5645000000000000000 : ℝ)+2*(1101340381/903200000000 : ℝ)*(2277/20000 : ℝ))^(1103/256 : ℝ) := by
    rw [show (5643657794706614913/5645000000000000000 : ℝ)+2*(1101340381/903200000000 : ℝ)*(2277/20000 : ℝ)=(2500099707589161/2500000000000000 : ℝ) by norm_num, show 1+2*(268517400397009/3125000000000000000 : ℝ)=(1562768517400397009/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(659768175682321/2500000000000000000 : ℝ)+(268517400397009/3125000000000000000 : ℝ) ≤ ((5643657794706614913/5645000000000000000 : ℝ)+(1101340381/903200000000 : ℝ)*((3693/25000 : ℝ)+(2277/20000 : ℝ)))^(1103/256 : ℝ) := by
    rw [show (5643657794706614913/5645000000000000000 : ℝ)+(1101340381/903200000000 : ℝ)*((3693/25000 : ℝ)+(2277/20000 : ℝ))=(10000811832999519/10000000000000000 : ℝ) by norm_num, show 1+(659768175682321/2500000000000000000 : ℝ)+(268517400397009/3125000000000000000 : ℝ)=(12504372910479999641/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(659768175682321/2500000000000000000 : ℝ) ≤ ((5643657794706614913/5645000000000000000 : ℝ)+2*(1101340381/903200000000 : ℝ)*(3693/25000 : ℝ))^(1103/256 : ℝ) := by
    rw [show (5643657794706614913/5645000000000000000 : ℝ)+2*(1101340381/903200000000 : ℝ)*(3693/25000 : ℝ)=(5000612417821197/5000000000000000 : ℝ) by norm_num, show 1+2*(659768175682321/2500000000000000000 : ℝ)=(1250659768175682321/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5643657794706614913/5645000000000000000 : ℝ)*(X 1 0+X 2 0)+(1101340381/903200000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1103/256 : ℝ)) (lo := (2277/20000 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (5643657794706614913/5645000000000000000 : ℝ)) (alpha := (1101340381/903200000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5643657794706614913/5645000000000000000 : ℝ)*(X 0 1+X 2 1)+(1101340381/903200000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1103/256 : ℝ)) (lo := (2277/20000 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (5643657794706614913/5645000000000000000 : ℝ)) (alpha := (1101340381/903200000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5643657794706614913/5645000000000000000 : ℝ)*(X 0 2+X 1 2)+(1101340381/903200000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1103/256 : ℝ)) (lo := (2277/20000 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (5643657794706614913/5645000000000000000 : ℝ)) (alpha := (1101340381/903200000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-975911463/5000000000 : ℝ)*X 0 0+(1351746103/2500000000 : ℝ)*X 0 1+(5247415157/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334175719/625000000 : ℝ)*X 1 0+(-508261531/2500000000 : ℝ)*X 1 1+(524741513/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069362309/2000000000 : ℝ)*X 2 0+(655926893/1250000000 : ℝ)*X 2 1+(-40660921/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((537301023/1250000000 : ℝ)*X 0 0+(4127427793/10000000000 : ℝ)*X 0 1+(447566739/1000000000 : ℝ)*X 0 2+(537301023/1250000000 : ℝ)*X 1 0+(4127427793/10000000000 : ℝ)*X 1 1+(447566739/1000000000 : ℝ)*X 1 2+(537301023/1250000000 : ℝ)*X 2 0+(4127427793/10000000000 : ℝ)*X 2 1+(447566739/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1951834001/10000000000 : ℝ)*X 0 0+(5247991923/10000000000 : ℝ)*X 0 1+(5406404683/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((106104647/200000000 : ℝ)*X 1 0+(-374811311/2000000000 : ℝ)*X 1 1+(5406404683/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305232349/10000000000 : ℝ)*X 2 0+(5406404683/10000000000 : ℝ)*X 2 1+(-468514139/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((859686481/2000000000 : ℝ)*X 0 0+(559301079/1250000000 : ℝ)*X 0 1+(2064346553/5000000000 : ℝ)*X 0 2+(859686481/2000000000 : ℝ)*X 1 0+(559301079/1250000000 : ℝ)*X 1 1+(2064346553/5000000000 : ℝ)*X 1 2+(859686481/2000000000 : ℝ)*X 2 0+(559301079/1250000000 : ℝ)*X 2 1+(2064346553/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (606926662132737472927527591/70562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (202291881/12500000000000 : ℝ)*(base19) + (15876981/1000000000000 : ℝ)*(base23) + (42075451/100000000000000 : ℝ)*(lower2) + (33746447/20000000000000 : ℝ)*(upper3) + (13416759/6250000000000 : ℝ)*(upper5) + (2284640312855469/50000000000000 : ℝ)*(major0) + (2284640312855469/50000000000000 : ℝ)*(major1) + (2284640312855469/50000000000000 : ℝ)*(major2) + (3133452294276833/50000000000000 : ℝ)*(sp0) + (313346983457251/5000000000000 : ℝ)*(sp1) + (391683731236373/6250000000000 : ℝ)*(sp2) + (574320586168059/20000000000000 : ℝ)*(sp3) + (18349463201/50000000000000 : ℝ)*(sp4) + (16746392721/100000000000000 : ℝ)*(sp7) + (358952459654127/12500000000000 : ℝ)*(f.failure) + (1566735321870017/25000000000000 : ℝ)*(f.sum) + (1474359242907/1129000000000000000000000000 : ℝ)*base65 + (3918913973135990803/282250000000000000000000000000000 : ℝ)*base68 + (1008161612163740803/282250000000000000000000000000000 : ℝ)*base70 + (1068108904455990803/282250000000000000000000000000000 : ℝ)*base72 + (5412119594933/1129000000000000000000000000 : ℝ)*base74 + (3058864308614259197/282250000000000000000000000000000 : ℝ)*base75 + (2113819887435990803/282250000000000000000000000000000 : ℝ)*base78 + (31320440652490803/282250000000000000000000000000000 : ℝ)*base80 + (421072091823/564500000000000000000000000 : ℝ)*base81 + (6152211/625000000000000000000 : ℝ)*base89 + (6152211/625000000000000000000 : ℝ)*base91 + (6152211/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7952769836330072807757/1129000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47118419/4000000000000 : ℝ)*(base19) + (319749199/25000000000000 : ℝ)*(base23) + (99492729/25000000000000 : ℝ)*(lower1) + (35784113/25000000000000 : ℝ)*(upper3) + (9332583/20000000000000 : ℝ)*(lower4) + (144905261/100000000000000 : ℝ)*(upper5) + (4602568326737931/100000000000000 : ℝ)*(major0) + (4602568326737931/100000000000000 : ℝ)*(major1) + (4602568326737931/100000000000000 : ℝ)*(major2) + (1820730931/100000000000000 : ℝ)*(sp2) + (252503867323851/4000000000000 : ℝ)*(sp4) + (31562977525679/500000000000 : ℝ)*(sp5) + (6312593583368547/100000000000000 : ℝ)*(sp6) + (361567466947099/12500000000000 : ℝ)*(sp7) + (361567466947099/12500000000000 : ℝ)*(f.failure) + (252503867323851/4000000000000 : ℝ)*(f.sum) + (56698269679/112900000000000000000000000 : ℝ)*base66 + (23858710560080615003/564500000000000000000000000000000 : ℝ)*base67 + (3678444162235384997/564500000000000000000000000000000 : ℝ)*base70 + (37506514786138884997/564500000000000000000000000000000 : ℝ)*base72 + (9739431307599/1129000000000000000000000000 : ℝ)*base73 + (27145327614322884997/564500000000000000000000000000000 : ℝ)*base76 + (8308420768140115003/564500000000000000000000000000000 : ℝ)*base77 + (5759182149400615003/564500000000000000000000000000000 : ℝ)*base79 + (1471534040611/225800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3908993/625000000000000000000 : ℝ)*base90 + (3908993/625000000000000000000 : ℝ)*base92 + (3908993/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1453_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79559293/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2847/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1453_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1453_s7_0 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-390365177/2000000000 : ℝ)*x 0 + (5406965199/10000000000 : ℝ)*x 1 + (104948647/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (390365177/2000000000 : ℝ)^4413 ≤ (11913654072361/100000000000000 : ℝ)^3389 := by
    have hnat : (390365177 : ℕ)^4413*100000000000000^3389 ≤ 11913654072361^3389*2000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390365177 2000000000 11913654072361 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406965199/10000000000 : ℝ)^4413 ≤ (44901869280641/100000000000000 : ℝ)^3389 := by
    have hnat : (5406965199 : ℕ)^4413*100000000000000^3389 ≤ 44901869280641^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406965199 10000000000 44901869280641 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104948647/200000000 : ℝ)^4413 ≤ (21592238316587/50000000000000 : ℝ)^3389 := by
    have hnat : (104948647 : ℕ)^4413*50000000000000^3389 ≤ 21592238316587^3389*200000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104948647 200000000 21592238316587 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-390365177/2000000000 : ℝ), (5406965199/10000000000 : ℝ), (104948647/200000000 : ℝ)] ![(11913654072361/100000000000000 : ℝ), (44901869280641/100000000000000 : ℝ), (21592238316587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-390365177/2000000000 : ℝ)|^4413 ≤ (11913654072361/100000000000000 : ℝ)^3389
        have hw : |(-390365177/2000000000 : ℝ)|=(390365177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406965199/10000000000 : ℝ)|^4413 ≤ (44901869280641/100000000000000 : ℝ)^3389
        have hw : |(5406965199/10000000000 : ℝ)|=(5406965199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104948647/200000000 : ℝ)|^4413 ≤ (21592238316587/50000000000000 : ℝ)^3389
        have hw : |(104948647/200000000 : ℝ)|=(104948647/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s7_1 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (106936107/200000000 : ℝ)*x 0 + (-2033029293/10000000000 : ℝ)*x 1 + (5247433957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106936107/200000000 : ℝ)^4413 ≤ (22126208381051/50000000000000 : ℝ)^3389 := by
    have hnat : (106936107 : ℕ)^4413*50000000000000^3389 ≤ 22126208381051^3389*200000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106936107 200000000 22126208381051 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2033029293/10000000000 : ℝ)^4413 ≤ (12563089372497/100000000000000 : ℝ)^3389 := by
    have hnat : (2033029293 : ℕ)^4413*100000000000000^3389 ≤ 12563089372497^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2033029293 10000000000 12563089372497 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247433957/10000000000 : ℝ)^4413 ≤ (21592246927101/50000000000000 : ℝ)^3389 := by
    have hnat : (5247433957 : ℕ)^4413*50000000000000^3389 ≤ 21592246927101^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247433957 10000000000 21592246927101 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106936107/200000000 : ℝ), (-2033029293/10000000000 : ℝ), (5247433957/10000000000 : ℝ)] ![(22126208381051/50000000000000 : ℝ), (12563089372497/100000000000000 : ℝ), (21592246927101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106936107/200000000 : ℝ)|^4413 ≤ (22126208381051/50000000000000 : ℝ)^3389
        have hw : |(106936107/200000000 : ℝ)|=(106936107/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2033029293/10000000000 : ℝ)|^4413 ≤ (12563089372497/100000000000000 : ℝ)^3389
        have hw : |(-2033029293/10000000000 : ℝ)|=(2033029293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247433957/10000000000 : ℝ)|^4413 ≤ (21592246927101/50000000000000 : ℝ)^3389
        have hw : |(5247433957/10000000000 : ℝ)|=(5247433957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s7_2 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346802567/10000000000 : ℝ)*x 0 + (5247439189/10000000000 : ℝ)*x 1 + (-508256513/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346802567/10000000000 : ℝ)^4413 ≤ (44252386769223/100000000000000 : ℝ)^3389 := by
    have hnat : (5346802567 : ℕ)^4413*100000000000000^3389 ≤ 44252386769223^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346802567 10000000000 44252386769223 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247439189/10000000000 : ℝ)^4413 ≤ (21592274960839/50000000000000 : ℝ)^3389 := by
    have hnat : (5247439189 : ℕ)^4413*50000000000000^3389 ≤ 21592274960839^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247439189 10000000000 21592274960839 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508256513/2500000000 : ℝ)^4413 ≤ (12563063293307/100000000000000 : ℝ)^3389 := by
    have hnat : (508256513 : ℕ)^4413*100000000000000^3389 ≤ 12563063293307^3389*2500000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508256513 2500000000 12563063293307 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346802567/10000000000 : ℝ), (5247439189/10000000000 : ℝ), (-508256513/2500000000 : ℝ)] ![(44252386769223/100000000000000 : ℝ), (21592274960839/50000000000000 : ℝ), (12563063293307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346802567/10000000000 : ℝ)|^4413 ≤ (44252386769223/100000000000000 : ℝ)^3389
        have hw : |(5346802567/10000000000 : ℝ)|=(5346802567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247439189/10000000000 : ℝ)|^4413 ≤ (21592274960839/50000000000000 : ℝ)^3389
        have hw : |(5247439189/10000000000 : ℝ)|=(5247439189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-508256513/2500000000 : ℝ)|^4413 ≤ (12563063293307/100000000000000 : ℝ)^3389
        have hw : |(-508256513/2500000000 : ℝ)|=(508256513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s7_3 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4298410477/10000000000 : ℝ)*x 0 + (412747143/1000000000 : ℝ)*x 1 + (4475622543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298410477/10000000000 : ℝ)^4413 ≤ (1332202910987/4000000000000 : ℝ)^3389 := by
    have hnat : (4298410477 : ℕ)^4413*4000000000000^3389 ≤ 1332202910987^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298410477 10000000000 1332202910987 4000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (412747143/1000000000 : ℝ)^4413 ≤ (15795430817693/50000000000000 : ℝ)^3389 := by
    have hnat : (412747143 : ℕ)^4413*50000000000000^3389 ≤ 15795430817693^3389*1000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412747143 1000000000 15795430817693 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4475622543/10000000000 : ℝ)^4413 ≤ (1097002049063/3125000000000 : ℝ)^3389 := by
    have hnat : (4475622543 : ℕ)^4413*3125000000000^3389 ≤ 1097002049063^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475622543 10000000000 1097002049063 3125000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298410477/10000000000 : ℝ), (412747143/1000000000 : ℝ), (4475622543/10000000000 : ℝ)] ![(1332202910987/4000000000000 : ℝ), (15795430817693/50000000000000 : ℝ), (1097002049063/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298410477/10000000000 : ℝ)|^4413 ≤ (1332202910987/4000000000000 : ℝ)^3389
        have hw : |(4298410477/10000000000 : ℝ)|=(4298410477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(412747143/1000000000 : ℝ)|^4413 ≤ (15795430817693/50000000000000 : ℝ)^3389
        have hw : |(412747143/1000000000 : ℝ)|=(412747143/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4475622543/10000000000 : ℝ)|^4413 ≤ (1097002049063/3125000000000 : ℝ)^3389
        have hw : |(4475622543/10000000000 : ℝ)|=(4475622543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s7_4 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-975918029/5000000000 : ℝ)*x 0 + (524801113/1000000000 : ℝ)*x 1 + (675798017/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (975918029/5000000000 : ℝ)^4413 ≤ (2382746985799/20000000000000 : ℝ)^3389 := by
    have hnat : (975918029 : ℕ)^4413*20000000000000^3389 ≤ 2382746985799^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975918029 5000000000 2382746985799 20000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524801113/1000000000 : ℝ)^4413 ≤ (43190679092471/100000000000000 : ℝ)^3389 := by
    have hnat : (524801113 : ℕ)^4413*100000000000000^3389 ≤ 43190679092471^3389*1000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524801113 1000000000 43190679092471 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675798017/1250000000 : ℝ)^4413 ≤ (44895585957777/100000000000000 : ℝ)^3389 := by
    have hnat : (675798017 : ℕ)^4413*100000000000000^3389 ≤ 44895585957777^3389*1250000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675798017 1250000000 44895585957777 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-975918029/5000000000 : ℝ), (524801113/1000000000 : ℝ), (675798017/1250000000 : ℝ)] ![(2382746985799/20000000000000 : ℝ), (43190679092471/100000000000000 : ℝ), (44895585957777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-975918029/5000000000 : ℝ)|^4413 ≤ (2382746985799/20000000000000 : ℝ)^3389
        have hw : |(-975918029/5000000000 : ℝ)|=(975918029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524801113/1000000000 : ℝ)|^4413 ≤ (43190679092471/100000000000000 : ℝ)^3389
        have hw : |(524801113/1000000000 : ℝ)|=(524801113/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675798017/1250000000 : ℝ)|^4413 ≤ (44895585957777/100000000000000 : ℝ)^3389
        have hw : |(675798017/1250000000 : ℝ)|=(675798017/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s7_5 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305237549/10000000000 : ℝ)*x 0 + (-93703873/500000000 : ℝ)*x 1 + (1081276867/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305237549/10000000000 : ℝ)^4413 ≤ (1752198414901/4000000000000 : ℝ)^3389 := by
    have hnat : (5305237549 : ℕ)^4413*4000000000000^3389 ≤ 1752198414901^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305237549 10000000000 1752198414901 4000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (93703873/500000000 : ℝ)^4413 ≤ (5649725754127/50000000000000 : ℝ)^3389 := by
    have hnat : (93703873 : ℕ)^4413*50000000000000^3389 ≤ 5649725754127^3389*500000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93703873 500000000 5649725754127 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081276867/2000000000 : ℝ)^4413 ≤ (11223897027407/25000000000000 : ℝ)^3389 := by
    have hnat : (1081276867 : ℕ)^4413*25000000000000^3389 ≤ 11223897027407^3389*2000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081276867 2000000000 11223897027407 25000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305237549/10000000000 : ℝ), (-93703873/500000000 : ℝ), (1081276867/2000000000 : ℝ)] ![(1752198414901/4000000000000 : ℝ), (5649725754127/50000000000000 : ℝ), (11223897027407/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305237549/10000000000 : ℝ)|^4413 ≤ (1752198414901/4000000000000 : ℝ)^3389
        have hw : |(5305237549/10000000000 : ℝ)|=(5305237549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-93703873/500000000 : ℝ)|^4413 ≤ (5649725754127/50000000000000 : ℝ)^3389
        have hw : |(-93703873/500000000 : ℝ)|=(93703873/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081276867/2000000000 : ℝ)|^4413 ≤ (11223897027407/25000000000000 : ℝ)^3389
        have hw : |(1081276867/2000000000 : ℝ)|=(1081276867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s7_6 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4298433919/10000000000 : ℝ)*x 0 + (223718247/500000000 : ℝ)*x 1 + (206436817/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298433919/10000000000 : ℝ)^4413 ≤ (16652654645161/50000000000000 : ℝ)^3389 := by
    have hnat : (4298433919 : ℕ)^4413*50000000000000^3389 ≤ 16652654645161^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298433919 10000000000 16652654645161 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223718247/500000000 : ℝ)^4413 ≤ (17545610915829/50000000000000 : ℝ)^3389 := by
    have hnat : (223718247 : ℕ)^4413*50000000000000^3389 ≤ 17545610915829^3389*500000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223718247 500000000 17545610915829 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206436817/500000000 : ℝ)^4413 ≤ (6320693771973/20000000000000 : ℝ)^3389 := by
    have hnat : (206436817 : ℕ)^4413*20000000000000^3389 ≤ 6320693771973^3389*500000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206436817 500000000 6320693771973 20000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298433919/10000000000 : ℝ), (223718247/500000000 : ℝ), (206436817/500000000 : ℝ)] ![(16652654645161/50000000000000 : ℝ), (17545610915829/50000000000000 : ℝ), (6320693771973/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298433919/10000000000 : ℝ)|^4413 ≤ (16652654645161/50000000000000 : ℝ)^3389
        have hw : |(4298433919/10000000000 : ℝ)|=(4298433919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(223718247/500000000 : ℝ)|^4413 ≤ (17545610915829/50000000000000 : ℝ)^3389
        have hw : |(223718247/500000000 : ℝ)|=(223718247/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(206436817/500000000 : ℝ)|^4413 ≤ (6320693771973/20000000000000 : ℝ)^3389
        have hw : |(206436817/500000000 : ℝ)|=(206436817/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s7_7 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (335684047/400000000 : ℝ)*x 0 + (1248477573/5000000000 : ℝ)*x 1 + (-842516641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335684047/400000000 : ℝ)^4413 ≤ (79591729117327/100000000000000 : ℝ)^3389 := by
    have hnat : (335684047 : ℕ)^4413*100000000000000^3389 ≤ 79591729117327^3389*400000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335684047 400000000 79591729117327 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1248477573/5000000000 : ℝ)^4413 ≤ (16418594210357/100000000000000 : ℝ)^3389 := by
    have hnat : (1248477573 : ℕ)^4413*100000000000000^3389 ≤ 16418594210357^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1248477573 5000000000 16418594210357 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (842516641/10000000000 : ℝ)^4413 ≤ (124677395647/3125000000000 : ℝ)^3389 := by
    have hnat : (842516641 : ℕ)^4413*3125000000000^3389 ≤ 124677395647^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842516641 10000000000 124677395647 3125000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335684047/400000000 : ℝ), (1248477573/5000000000 : ℝ), (-842516641/10000000000 : ℝ)] ![(79591729117327/100000000000000 : ℝ), (16418594210357/100000000000000 : ℝ), (124677395647/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335684047/400000000 : ℝ)|^4413 ≤ (79591729117327/100000000000000 : ℝ)^3389
        have hw : |(335684047/400000000 : ℝ)|=(335684047/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1248477573/5000000000 : ℝ)|^4413 ≤ (16418594210357/100000000000000 : ℝ)^3389
        have hw : |(1248477573/5000000000 : ℝ)|=(1248477573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-842516641/10000000000 : ℝ)|^4413 ≤ (124677395647/3125000000000 : ℝ)^3389
        have hw : |(-842516641/10000000000 : ℝ)|=(842516641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1453_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79559293/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2847/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11389/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14769/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14769/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2847/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14769/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2847/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14769/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2847/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14769/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2847/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14769/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2847/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14769/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2847/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2847/25000 : ℝ) ^ (1103/256 : ℝ) ≤ (8602316490759889/100000000000000000000 : ℝ) := by
    have hpowers : (2847/25000 : ℝ)^1103 ≤ (8602316490759889/100000000000000000000 : ℝ)^256 := by
      have hnat : (2847 : ℕ)^1103*100000000000000000000^256 ≤ 8602316490759889^256*25000^1103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 25000 8602316490759889 100000000000000000000 1103 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/25000 : ℝ)) (X := (8602316490759889/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14769/100000 : ℝ) ^ (1103/256 : ℝ) ≤ (411994412433231/1562500000000000000 : ℝ) := by
    have hpowers : (14769/100000 : ℝ)^1103 ≤ (411994412433231/1562500000000000000 : ℝ)^256 := by
      have hnat : (14769 : ℕ)^1103*1562500000000000000^256 ≤ 411994412433231^256*100000^1103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14769 100000 411994412433231 1562500000000000000 1103 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14769/100000 : ℝ)) (X := (411994412433231/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008602316490759889/50000000000000000000 : ℝ) ≤ (10000399283329941/10000000000000000 : ℝ) ^ (1103/256 : ℝ) := by
    have hpowers : (50008602316490759889/50000000000000000000 : ℝ)^256 ≤ (10000399283329941/10000000000000000 : ℝ)^1103 := by
      have hnat : (50008602316490759889 : ℕ)^256*10000000000000000^1103 ≤ 10000399283329941^1103*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008602316490759889 50000000000000000000 10000399283329941 10000000000000000 256 1103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000399283329941/10000000000000000 : ℝ)) (X := (50008602316490759889/50000000000000000000 : ℝ)) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034969958886486673/100000000000000000000 : ℝ) ≤ (10000811523817997/10000000000000000 : ℝ) ^ (1103/256 : ℝ) := by
    have hpowers : (100034969958886486673/100000000000000000000 : ℝ)^256 ≤ (10000811523817997/10000000000000000 : ℝ)^1103 := by
      have hnat : (100034969958886486673 : ℕ)^256*10000000000000000^1103 ≤ 10000811523817997^1103*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034969958886486673 100000000000000000000 10000811523817997 10000000000000000 256 1103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000811523817997/10000000000000000 : ℝ)) (X := (100034969958886486673/100000000000000000000 : ℝ)) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (781661994412433231/781250000000000000 : ℝ) ≤ (10001223764306053/10000000000000000 : ℝ) ^ (1103/256 : ℝ) := by
    have hpowers : (781661994412433231/781250000000000000 : ℝ)^256 ≤ (10001223764306053/10000000000000000 : ℝ)^1103 := by
      have hnat : (781661994412433231 : ℕ)^256*10000000000000000^1103 ≤ 10001223764306053^1103*781250000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781661994412433231 781250000000000000 10001223764306053 10000000000000000 256 1103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001223764306053/10000000000000000 : ℝ)) (X := (781661994412433231/781250000000000000 : ℝ)) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8602316490759889/100000000000000000000 : ℝ) ≤ ((2253464052505504471/2254000000000000000 : ℝ)+2*(51530061007/42262500000000 : ℝ)*(2847/25000 : ℝ))^(1103/256 : ℝ) := by
    rw [show (2253464052505504471/2254000000000000000 : ℝ)+2*(51530061007/42262500000000 : ℝ)*(2847/25000 : ℝ)=(10000399283329941/10000000000000000 : ℝ) by norm_num, show 1+2*(8602316490759889/100000000000000000000 : ℝ)=(50008602316490759889/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(411994412433231/1562500000000000000 : ℝ)+(8602316490759889/100000000000000000000 : ℝ) ≤ ((2253464052505504471/2254000000000000000 : ℝ)+(51530061007/42262500000000 : ℝ)*((14769/100000 : ℝ)+(2847/25000 : ℝ)))^(1103/256 : ℝ) := by
    rw [show (2253464052505504471/2254000000000000000 : ℝ)+(51530061007/42262500000000 : ℝ)*((14769/100000 : ℝ)+(2847/25000 : ℝ))=(10000811523817997/10000000000000000 : ℝ) by norm_num, show 1+(411994412433231/1562500000000000000 : ℝ)+(8602316490759889/100000000000000000000 : ℝ)=(100034969958886486673/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(411994412433231/1562500000000000000 : ℝ) ≤ ((2253464052505504471/2254000000000000000 : ℝ)+2*(51530061007/42262500000000 : ℝ)*(14769/100000 : ℝ))^(1103/256 : ℝ) := by
    rw [show (2253464052505504471/2254000000000000000 : ℝ)+2*(51530061007/42262500000000 : ℝ)*(14769/100000 : ℝ)=(10001223764306053/10000000000000000 : ℝ) by norm_num, show 1+2*(411994412433231/1562500000000000000 : ℝ)=(781661994412433231/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2253464052505504471/2254000000000000000 : ℝ)*(X 1 0+X 2 0)+(51530061007/42262500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1103/256 : ℝ)) (lo := (2847/25000 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (2253464052505504471/2254000000000000000 : ℝ)) (alpha := (51530061007/42262500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2253464052505504471/2254000000000000000 : ℝ)*(X 0 1+X 2 1)+(51530061007/42262500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1103/256 : ℝ)) (lo := (2847/25000 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (2253464052505504471/2254000000000000000 : ℝ)) (alpha := (51530061007/42262500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2253464052505504471/2254000000000000000 : ℝ)*(X 0 2+X 1 2)+(51530061007/42262500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1103/256 : ℝ)) (lo := (2847/25000 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (2253464052505504471/2254000000000000000 : ℝ)) (alpha := (51530061007/42262500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-390365177/2000000000 : ℝ)*X 0 0+(5406965199/10000000000 : ℝ)*X 0 1+(104948647/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((106936107/200000000 : ℝ)*X 1 0+(-2033029293/10000000000 : ℝ)*X 1 1+(5247433957/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346802567/10000000000 : ℝ)*X 2 0+(5247439189/10000000000 : ℝ)*X 2 1+(-508256513/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4298410477/10000000000 : ℝ)*X 0 0+(412747143/1000000000 : ℝ)*X 0 1+(4475622543/10000000000 : ℝ)*X 0 2+(4298410477/10000000000 : ℝ)*X 1 0+(412747143/1000000000 : ℝ)*X 1 1+(4475622543/10000000000 : ℝ)*X 1 2+(4298410477/10000000000 : ℝ)*X 2 0+(412747143/1000000000 : ℝ)*X 2 1+(4475622543/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-975918029/5000000000 : ℝ)*X 0 0+(524801113/1000000000 : ℝ)*X 0 1+(675798017/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305237549/10000000000 : ℝ)*X 1 0+(-93703873/500000000 : ℝ)*X 1 1+(1081276867/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((4298433919/10000000000 : ℝ)*X 0 0+(223718247/500000000 : ℝ)*X 0 1+(206436817/500000000 : ℝ)*X 0 2+(4298433919/10000000000 : ℝ)*X 1 0+(223718247/500000000 : ℝ)*X 1 1+(206436817/500000000 : ℝ)*X 1 2+(4298433919/10000000000 : ℝ)*X 2 0+(223718247/500000000 : ℝ)*X 2 1+(206436817/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s7_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((335684047/400000000 : ℝ)*X 2 0+(1248477573/5000000000 : ℝ)*X 2 1+(-842516641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s7_7 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (39179051230090609643936173/22540000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (152565441/100000000000000 : ℝ)*(upper2) + (55243611/25000000000000 : ℝ)*(upper4) + (1014544109/100000000000000 : ℝ)*(upper5) + (914099961096521/20000000000000 : ℝ)*(major0) + (914099961096521/20000000000000 : ℝ)*(major1) + (914099961096521/20000000000000 : ℝ)*(major2) + (6268431345397241/100000000000000 : ℝ)*(sp0) + (6268494719926949/100000000000000 : ℝ)*(sp1) + (6268609337810537/100000000000000 : ℝ)*(sp2) + (2872355959926941/100000000000000 : ℝ)*(sp3) + (729288483/400000000000 : ℝ)*(sp4) + (59473795521/50000000000000 : ℝ)*(sp5) + (374069753/1250000000000 : ℝ)*(sp6) + (2164853727/50000000000000 : ℝ)*(sp7) + (2872385885507181/100000000000000 : ℝ)*(f.failure) + (6268613667517991/100000000000000 : ℝ)*(f.sum) + (1434211821101/211312500000000000000000000 : ℝ)*base66 + (2765582252912323/2760000000000000000000000000000 : ℝ)*base68 + (10590668631152323/2760000000000000000000000000000 : ℝ)*base70 + (10560553523727677/2760000000000000000000000000000 : ℝ)*base71 + (3948252580817/3381000000000000000000000000 : ℝ)*base74 + (14721190551032323/2760000000000000000000000000000 : ℝ)*base76 + (16691945146232323/2760000000000000000000000000000 : ℝ)*base78 + (5157744829407677/2760000000000000000000000000000 : ℝ)*base79 + (10933726840051/3381000000000000000000000000 : ℝ)*base81 + (16783033/5000000000000000000000 : ℝ)*base89 + (16783033/5000000000000000000000 : ℝ)*base91 + (16783033/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1453_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79559293/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2847/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1453_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1453_box_0 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1792873771/10000000000 : ℝ)*x 0 + (1346306659/2500000000 : ℝ)*x 1 + (2692613129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1792873771/10000000000 : ℝ)^4413 ≤ (5333063533833/50000000000000 : ℝ)^3389 := by
    have hnat : (1792873771 : ℕ)^4413*50000000000000^3389 ≤ 5333063533833^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1792873771 10000000000 5333063533833 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346306659/2500000000 : ℝ)^4413 ≤ (8933387700269/20000000000000 : ℝ)^3389 := by
    have hnat : (1346306659 : ℕ)^4413*20000000000000^3389 ≤ 8933387700269^3389*2500000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346306659 2500000000 8933387700269 20000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692613129/5000000000 : ℝ)^4413 ≤ (7146709507/16000000000 : ℝ)^3389 := by
    have hnat : (2692613129 : ℕ)^4413*16000000000^3389 ≤ 7146709507^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692613129 5000000000 7146709507 16000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1792873771/10000000000 : ℝ), (1346306659/2500000000 : ℝ), (2692613129/5000000000 : ℝ)] ![(5333063533833/50000000000000 : ℝ), (8933387700269/20000000000000 : ℝ), (7146709507/16000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1792873771/10000000000 : ℝ)|^4413 ≤ (5333063533833/50000000000000 : ℝ)^3389
        have hw : |(-1792873771/10000000000 : ℝ)|=(1792873771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346306659/2500000000 : ℝ)|^4413 ≤ (8933387700269/20000000000000 : ℝ)^3389
        have hw : |(1346306659/2500000000 : ℝ)|=(1346306659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692613129/5000000000 : ℝ)|^4413 ≤ (7146709507/16000000000 : ℝ)^3389
        have hw : |(2692613129/5000000000 : ℝ)|=(2692613129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_box_1 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1321554163/2500000000 : ℝ)*x 0 + (-192899439/1000000000 : ℝ)*x 1 + (5385225853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321554163/2500000000 : ℝ)^4413 ≤ (8720112505719/20000000000000 : ℝ)^3389 := by
    have hnat : (1321554163 : ℕ)^4413*20000000000000^3389 ≤ 8720112505719^3389*2500000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321554163 2500000000 8720112505719 20000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192899439/1000000000 : ℝ)^4413 ≤ (2933126851759/25000000000000 : ℝ)^3389 := by
    have hnat : (192899439 : ℕ)^4413*25000000000000^3389 ≤ 2933126851759^3389*1000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192899439 1000000000 2933126851759 25000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385225853/10000000000 : ℝ)^4413 ≤ (44666930044541/100000000000000 : ℝ)^3389 := by
    have hnat : (5385225853 : ℕ)^4413*100000000000000^3389 ≤ 44666930044541^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385225853 10000000000 44666930044541 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321554163/2500000000 : ℝ), (-192899439/1000000000 : ℝ), (5385225853/10000000000 : ℝ)] ![(8720112505719/20000000000000 : ℝ), (2933126851759/25000000000000 : ℝ), (44666930044541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321554163/2500000000 : ℝ)|^4413 ≤ (8720112505719/20000000000000 : ℝ)^3389
        have hw : |(1321554163/2500000000 : ℝ)|=(1321554163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-192899439/1000000000 : ℝ)|^4413 ≤ (2933126851759/25000000000000 : ℝ)^3389
        have hw : |(-192899439/1000000000 : ℝ)|=(192899439/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385225853/10000000000 : ℝ)|^4413 ≤ (44666930044541/100000000000000 : ℝ)^3389
        have hw : |(5385225853/10000000000 : ℝ)|=(5385225853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_box_2 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286215939/10000000000 : ℝ)*x 0 + (5385226481/10000000000 : ℝ)*x 1 + (-1928994501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286215939/10000000000 : ℝ)^4413 ≤ (43600554870883/100000000000000 : ℝ)^3389 := by
    have hnat : (5286215939 : ℕ)^4413*100000000000000^3389 ≤ 43600554870883^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286215939 10000000000 43600554870883 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385226481/10000000000 : ℝ)^4413 ≤ (8933387365453/20000000000000 : ℝ)^3389 := by
    have hnat : (5385226481 : ℕ)^4413*20000000000000^3389 ≤ 8933387365453^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385226481 10000000000 8933387365453 20000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1928994501/10000000000 : ℝ)^4413 ≤ (234650165723/2000000000000 : ℝ)^3389 := by
    have hnat : (1928994501 : ℕ)^4413*2000000000000^3389 ≤ 234650165723^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1928994501 10000000000 234650165723 2000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286215939/10000000000 : ℝ), (5385226481/10000000000 : ℝ), (-1928994501/10000000000 : ℝ)] ![(43600554870883/100000000000000 : ℝ), (8933387365453/20000000000000 : ℝ), (234650165723/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286215939/10000000000 : ℝ)|^4413 ≤ (43600554870883/100000000000000 : ℝ)^3389
        have hw : |(5286215939/10000000000 : ℝ)|=(5286215939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385226481/10000000000 : ℝ)|^4413 ≤ (8933387365453/20000000000000 : ℝ)^3389
        have hw : |(5385226481/10000000000 : ℝ)|=(5385226481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1928994501/10000000000 : ℝ)|^4413 ≤ (234650165723/2000000000000 : ℝ)^3389
        have hw : |(-1928994501/10000000000 : ℝ)|=(1928994501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_box_3 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (888847617/2000000000 : ℝ)*x 0 + (2114579281/5000000000 : ℝ)*x 1 + (4229157827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (888847617/2000000000 : ℝ)^4413 ≤ (34783866646581/100000000000000 : ℝ)^3389 := by
    have hnat : (888847617 : ℕ)^4413*100000000000000^3389 ≤ 34783866646581^3389*2000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888847617 2000000000 34783866646581 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114579281/5000000000 : ℝ)^4413 ≤ (6521614072023/20000000000000 : ℝ)^3389 := by
    have hnat : (2114579281 : ℕ)^4413*20000000000000^3389 ≤ 6521614072023^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114579281 5000000000 6521614072023 20000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4229157827/10000000000 : ℝ)^4413 ≤ (32608062980719/100000000000000 : ℝ)^3389 := by
    have hnat : (4229157827 : ℕ)^4413*100000000000000^3389 ≤ 32608062980719^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229157827 10000000000 32608062980719 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(888847617/2000000000 : ℝ), (2114579281/5000000000 : ℝ), (4229157827/10000000000 : ℝ)] ![(34783866646581/100000000000000 : ℝ), (6521614072023/20000000000000 : ℝ), (32608062980719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(888847617/2000000000 : ℝ)|^4413 ≤ (34783866646581/100000000000000 : ℝ)^3389
        have hw : |(888847617/2000000000 : ℝ)|=(888847617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2114579281/5000000000 : ℝ)|^4413 ≤ (6521614072023/20000000000000 : ℝ)^3389
        have hw : |(2114579281/5000000000 : ℝ)|=(2114579281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4229157827/10000000000 : ℝ)|^4413 ≤ (32608062980719/100000000000000 : ℝ)^3389
        have hw : |(4229157827/10000000000 : ℝ)|=(4229157827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_box_4 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-528375533/2500000000 : ℝ)*x 0 + (131671487/250000000 : ℝ)*x 1 + (5266857457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528375533/2500000000 : ℝ)^4413 ≤ (13214463460587/100000000000000 : ℝ)^3389 := by
    have hnat : (528375533 : ℕ)^4413*100000000000000^3389 ≤ 13214463460587^3389*2500000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528375533 2500000000 13214463460587 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131671487/250000000 : ℝ)^4413 ≤ (43392779117713/100000000000000 : ℝ)^3389 := by
    have hnat : (131671487 : ℕ)^4413*100000000000000^3389 ≤ 43392779117713^3389*250000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131671487 250000000 43392779117713 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266857457/10000000000 : ℝ)^4413 ≤ (5424094676813/12500000000000 : ℝ)^3389 := by
    have hnat : (5266857457 : ℕ)^4413*12500000000000^3389 ≤ 5424094676813^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266857457 10000000000 5424094676813 12500000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-528375533/2500000000 : ℝ), (131671487/250000000 : ℝ), (5266857457/10000000000 : ℝ)] ![(13214463460587/100000000000000 : ℝ), (43392779117713/100000000000000 : ℝ), (5424094676813/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-528375533/2500000000 : ℝ)|^4413 ≤ (13214463460587/100000000000000 : ℝ)^3389
        have hw : |(-528375533/2500000000 : ℝ)|=(528375533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131671487/250000000 : ℝ)|^4413 ≤ (43392779117713/100000000000000 : ℝ)^3389
        have hw : |(131671487/250000000 : ℝ)|=(131671487/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266857457/10000000000 : ℝ)|^4413 ≤ (5424094676813/12500000000000 : ℝ)^3389
        have hw : |(5266857457/10000000000 : ℝ)|=(5266857457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_box_5 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5368975797/10000000000 : ℝ)*x 0 + (-395440049/2000000000 : ℝ)*x 1 + (5266858683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368975797/10000000000 : ℝ)^4413 ≤ (44491501107057/100000000000000 : ℝ)^3389 := by
    have hnat : (5368975797 : ℕ)^4413*100000000000000^3389 ≤ 44491501107057^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368975797 10000000000 44491501107057 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (395440049/2000000000 : ℝ)^4413 ≤ (6057864154557/50000000000000 : ℝ)^3389 := by
    have hnat : (395440049 : ℕ)^4413*50000000000000^3389 ≤ 6057864154557^3389*2000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395440049 2000000000 6057864154557 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266858683/10000000000 : ℝ)^4413 ≤ (21696385283657/50000000000000 : ℝ)^3389 := by
    have hnat : (5266858683 : ℕ)^4413*50000000000000^3389 ≤ 21696385283657^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266858683 10000000000 21696385283657 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368975797/10000000000 : ℝ), (-395440049/2000000000 : ℝ), (5266858683/10000000000 : ℝ)] ![(44491501107057/100000000000000 : ℝ), (6057864154557/50000000000000 : ℝ), (21696385283657/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368975797/10000000000 : ℝ)|^4413 ≤ (44491501107057/100000000000000 : ℝ)^3389
        have hw : |(5368975797/10000000000 : ℝ)|=(5368975797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-395440049/2000000000 : ℝ)|^4413 ≤ (6057864154557/50000000000000 : ℝ)^3389
        have hw : |(-395440049/2000000000 : ℝ)|=(395440049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266858683/10000000000 : ℝ)|^4413 ≤ (21696385283657/50000000000000 : ℝ)^3389
        have hw : |(5266858683/10000000000 : ℝ)|=(5266858683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_box_6 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5368975727/10000000000 : ℝ)*x 0 + (526685849/1000000000 : ℝ)*x 1 + (-1977200599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368975727/10000000000 : ℝ)^4413 ≤ (4449150035171/10000000000000 : ℝ)^3389 := by
    have hnat : (5368975727 : ℕ)^4413*10000000000000^3389 ≤ 4449150035171^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368975727 10000000000 4449150035171 10000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526685849/1000000000 : ℝ)^4413 ≤ (8678553699353/20000000000000 : ℝ)^3389 := by
    have hnat : (526685849 : ℕ)^4413*20000000000000^3389 ≤ 8678553699353^3389*1000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526685849 1000000000 8678553699353 20000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1977200599/10000000000 : ℝ)^4413 ≤ (3028932783441/25000000000000 : ℝ)^3389 := by
    have hnat : (1977200599 : ℕ)^4413*25000000000000^3389 ≤ 3028932783441^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977200599 10000000000 3028932783441 25000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368975727/10000000000 : ℝ), (526685849/1000000000 : ℝ), (-1977200599/10000000000 : ℝ)] ![(4449150035171/10000000000000 : ℝ), (8678553699353/20000000000000 : ℝ), (3028932783441/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368975727/10000000000 : ℝ)|^4413 ≤ (4449150035171/10000000000000 : ℝ)^3389
        have hw : |(5368975727/10000000000 : ℝ)|=(5368975727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526685849/1000000000 : ℝ)|^4413 ≤ (8678553699353/20000000000000 : ℝ)^3389
        have hw : |(526685849/1000000000 : ℝ)|=(526685849/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1977200599/10000000000 : ℝ)|^4413 ≤ (3028932783441/25000000000000 : ℝ)^3389
        have hw : |(-1977200599/10000000000 : ℝ)|=(1977200599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_box_7 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4151500859/10000000000 : ℝ)*x 0 + (4375477239/10000000000 : ℝ)*x 1 + (218773797/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4151500859/10000000000 : ℝ)^4413 ≤ (31830559686513/100000000000000 : ℝ)^3389 := by
    have hnat : (4151500859 : ℕ)^4413*100000000000000^3389 ≤ 31830559686513^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4151500859 10000000000 31830559686513 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4375477239/10000000000 : ℝ)^4413 ≤ (8521181684041/25000000000000 : ℝ)^3389 := by
    have hnat : (4375477239 : ℕ)^4413*25000000000000^3389 ≤ 8521181684041^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375477239 10000000000 8521181684041 25000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218773797/500000000 : ℝ)^4413 ≤ (532573649367/1562500000000 : ℝ)^3389 := by
    have hnat : (218773797 : ℕ)^4413*1562500000000^3389 ≤ 532573649367^3389*500000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218773797 500000000 532573649367 1562500000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4151500859/10000000000 : ℝ), (4375477239/10000000000 : ℝ), (218773797/500000000 : ℝ)] ![(31830559686513/100000000000000 : ℝ), (8521181684041/25000000000000 : ℝ), (532573649367/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4151500859/10000000000 : ℝ)|^4413 ≤ (31830559686513/100000000000000 : ℝ)^3389
        have hw : |(4151500859/10000000000 : ℝ)|=(4151500859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4375477239/10000000000 : ℝ)|^4413 ≤ (8521181684041/25000000000000 : ℝ)^3389
        have hw : |(4375477239/10000000000 : ℝ)|=(4375477239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218773797/500000000 : ℝ)|^4413 ≤ (532573649367/1562500000000 : ℝ)^3389
        have hw : |(218773797/500000000 : ℝ)|=(218773797/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_box_8 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1022958509/5000000000 : ℝ)*x 0 + (2592439403/5000000000 : ℝ)*x 1 + (5399185559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1022958509/5000000000 : ℝ)^4413 ≤ (12666891569917/100000000000000 : ℝ)^3389 := by
    have hnat : (1022958509 : ℕ)^4413*100000000000000^3389 ≤ 12666891569917^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022958509 5000000000 12666891569917 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592439403/5000000000 : ℝ)^4413 ≤ (8503069463999/20000000000000 : ℝ)^3389 := by
    have hnat : (2592439403 : ℕ)^4413*20000000000000^3389 ≤ 8503069463999^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592439403 5000000000 8503069463999 20000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399185559/10000000000 : ℝ)^4413 ≤ (44817761095767/100000000000000 : ℝ)^3389 := by
    have hnat : (5399185559 : ℕ)^4413*100000000000000^3389 ≤ 44817761095767^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399185559 10000000000 44817761095767 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1022958509/5000000000 : ℝ), (2592439403/5000000000 : ℝ), (5399185559/10000000000 : ℝ)] ![(12666891569917/100000000000000 : ℝ), (8503069463999/20000000000000 : ℝ), (44817761095767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1022958509/5000000000 : ℝ)|^4413 ≤ (12666891569917/100000000000000 : ℝ)^3389
        have hw : |(-1022958509/5000000000 : ℝ)|=(1022958509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592439403/5000000000 : ℝ)|^4413 ≤ (8503069463999/20000000000000 : ℝ)^3389
        have hw : |(2592439403/5000000000 : ℝ)|=(2592439403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399185559/10000000000 : ℝ)|^4413 ≤ (44817761095767/100000000000000 : ℝ)^3389
        have hw : |(5399185559/10000000000 : ℝ)|=(5399185559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_box_9 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659556529/1250000000 : ℝ)*x 0 + (-1923185069/10000000000 : ℝ)*x 1 + (10798371/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659556529/1250000000 : ℝ)^4413 ≤ (43495720677473/100000000000000 : ℝ)^3389 := by
    have hnat : (659556529 : ℕ)^4413*100000000000000^3389 ≤ 43495720677473^3389*1250000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659556529 1250000000 43495720677473 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1923185069/10000000000 : ℝ)^4413 ≤ (2921629711353/25000000000000 : ℝ)^3389 := by
    have hnat : (1923185069 : ℕ)^4413*25000000000000^3389 ≤ 2921629711353^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1923185069 10000000000 2921629711353 25000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10798371/20000000 : ℝ)^4413 ≤ (22408880229019/50000000000000 : ℝ)^3389 := by
    have hnat : (10798371 : ℕ)^4413*50000000000000^3389 ≤ 22408880229019^3389*20000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10798371 20000000 22408880229019 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659556529/1250000000 : ℝ), (-1923185069/10000000000 : ℝ), (10798371/20000000 : ℝ)] ![(43495720677473/100000000000000 : ℝ), (2921629711353/25000000000000 : ℝ), (22408880229019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659556529/1250000000 : ℝ)|^4413 ≤ (43495720677473/100000000000000 : ℝ)^3389
        have hw : |(659556529/1250000000 : ℝ)|=(659556529/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1923185069/10000000000 : ℝ)|^4413 ≤ (2921629711353/25000000000000 : ℝ)^3389
        have hw : |(-1923185069/10000000000 : ℝ)|=(1923185069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10798371/20000000 : ℝ)|^4413 ≤ (22408880229019/50000000000000 : ℝ)^3389
        have hw : |(10798371/20000000 : ℝ)|=(10798371/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_box_10 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276452263/10000000000 : ℝ)*x 0 + (1349796471/2500000000 : ℝ)*x 1 + (-240398063/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276452263/10000000000 : ℝ)^4413 ≤ (43495721010231/100000000000000 : ℝ)^3389 := by
    have hnat : (5276452263 : ℕ)^4413*100000000000000^3389 ≤ 43495721010231^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276452263 10000000000 43495721010231 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349796471/2500000000 : ℝ)^4413 ≤ (22408882304341/50000000000000 : ℝ)^3389 := by
    have hnat : (1349796471 : ℕ)^4413*50000000000000^3389 ≤ 22408882304341^3389*2500000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349796471 2500000000 22408882304341 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (240398063/1250000000 : ℝ)^4413 ≤ (11686514374719/100000000000000 : ℝ)^3389 := by
    have hnat : (240398063 : ℕ)^4413*100000000000000^3389 ≤ 11686514374719^3389*1250000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240398063 1250000000 11686514374719 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276452263/10000000000 : ℝ), (1349796471/2500000000 : ℝ), (-240398063/1250000000 : ℝ)] ![(43495721010231/100000000000000 : ℝ), (22408882304341/50000000000000 : ℝ), (11686514374719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276452263/10000000000 : ℝ)|^4413 ≤ (43495721010231/100000000000000 : ℝ)^3389
        have hw : |(5276452263/10000000000 : ℝ)|=(5276452263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349796471/2500000000 : ℝ)|^4413 ≤ (22408882304341/50000000000000 : ℝ)^3389
        have hw : |(1349796471/2500000000 : ℝ)|=(1349796471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-240398063/1250000000 : ℝ)|^4413 ≤ (11686514374719/100000000000000 : ℝ)^3389
        have hw : |(-240398063/1250000000 : ℝ)|=(240398063/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_box_11 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (179128143/400000000 : ℝ)*x 0 + (4211888759/10000000000 : ℝ)*x 1 + (4211888147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (179128143/400000000 : ℝ)^4413 ≤ (17565214367359/50000000000000 : ℝ)^3389 := by
    have hnat : (179128143 : ℕ)^4413*50000000000000^3389 ≤ 17565214367359^3389*400000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179128143 400000000 17565214367359 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4211888759/10000000000 : ℝ)^4413 ≤ (32434788696531/100000000000000 : ℝ)^3389 := by
    have hnat : (4211888759 : ℕ)^4413*100000000000000^3389 ≤ 32434788696531^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211888759 10000000000 32434788696531 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4211888147/10000000000 : ℝ)^4413 ≤ (16217391279823/50000000000000 : ℝ)^3389 := by
    have hnat : (4211888147 : ℕ)^4413*50000000000000^3389 ≤ 16217391279823^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211888147 10000000000 16217391279823 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(179128143/400000000 : ℝ), (4211888759/10000000000 : ℝ), (4211888147/10000000000 : ℝ)] ![(17565214367359/50000000000000 : ℝ), (32434788696531/100000000000000 : ℝ), (16217391279823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(179128143/400000000 : ℝ)|^4413 ≤ (17565214367359/50000000000000 : ℝ)^3389
        have hw : |(179128143/400000000 : ℝ)|=(179128143/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4211888759/10000000000 : ℝ)|^4413 ≤ (32434788696531/100000000000000 : ℝ)^3389
        have hw : |(4211888759/10000000000 : ℝ)|=(4211888759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4211888147/10000000000 : ℝ)|^4413 ≤ (16217391279823/50000000000000 : ℝ)^3389
        have hw : |(4211888147/10000000000 : ℝ)|=(4211888147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_box_12 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-465149933/2500000000 : ℝ)*x 0 + (5465228477/10000000000 : ℝ)*x 1 + (5255720551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (465149933/2500000000 : ℝ)^4413 ≤ (11193751270621/100000000000000 : ℝ)^3389 := by
    have hnat : (465149933 : ℕ)^4413*100000000000000^3389 ≤ 11193751270621^3389*2500000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465149933 2500000000 11193751270621 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5465228477/10000000000 : ℝ)^4413 ≤ (45532932388787/100000000000000 : ℝ)^3389 := by
    have hnat : (5465228477 : ℕ)^4413*100000000000000^3389 ≤ 45532932388787^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465228477 10000000000 45532932388787 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255720551/10000000000 : ℝ)^4413 ≤ (8654663264361/20000000000000 : ℝ)^3389 := by
    have hnat : (5255720551 : ℕ)^4413*20000000000000^3389 ≤ 8654663264361^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255720551 10000000000 8654663264361 20000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-465149933/2500000000 : ℝ), (5465228477/10000000000 : ℝ), (5255720551/10000000000 : ℝ)] ![(11193751270621/100000000000000 : ℝ), (45532932388787/100000000000000 : ℝ), (8654663264361/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-465149933/2500000000 : ℝ)|^4413 ≤ (11193751270621/100000000000000 : ℝ)^3389
        have hw : |(-465149933/2500000000 : ℝ)|=(465149933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5465228477/10000000000 : ℝ)|^4413 ≤ (45532932388787/100000000000000 : ℝ)^3389
        have hw : |(5465228477/10000000000 : ℝ)|=(5465228477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255720551/10000000000 : ℝ)|^4413 ≤ (8654663264361/20000000000000 : ℝ)^3389
        have hw : |(5255720551/10000000000 : ℝ)|=(5255720551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_box_13 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688380389/5000000000 : ℝ)*x 0 + (-247704751/1250000000 : ℝ)*x 1 + (2627860687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688380389/5000000000 : ℝ)^4413 ≤ (44575524578883/100000000000000 : ℝ)^3389 := by
    have hnat : (2688380389 : ℕ)^4413*100000000000000^3389 ≤ 44575524578883^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688380389 5000000000 44575524578883 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (247704751/1250000000 : ℝ)^4413 ≤ (1518893782697/12500000000000 : ℝ)^3389 := by
    have hnat : (247704751 : ℕ)^4413*12500000000000^3389 ≤ 1518893782697^3389*1250000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247704751 1250000000 1518893782697 12500000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627860687/5000000000 : ℝ)^4413 ≤ (10818331286373/25000000000000 : ℝ)^3389 := by
    have hnat : (2627860687 : ℕ)^4413*25000000000000^3389 ≤ 10818331286373^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627860687 5000000000 10818331286373 25000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688380389/5000000000 : ℝ), (-247704751/1250000000 : ℝ), (2627860687/5000000000 : ℝ)] ![(44575524578883/100000000000000 : ℝ), (1518893782697/12500000000000 : ℝ), (10818331286373/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688380389/5000000000 : ℝ)|^4413 ≤ (44575524578883/100000000000000 : ℝ)^3389
        have hw : |(2688380389/5000000000 : ℝ)|=(2688380389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-247704751/1250000000 : ℝ)|^4413 ≤ (1518893782697/12500000000000 : ℝ)^3389
        have hw : |(-247704751/1250000000 : ℝ)|=(247704751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627860687/5000000000 : ℝ)|^4413 ≤ (10818331286373/25000000000000 : ℝ)^3389
        have hw : |(2627860687/5000000000 : ℝ)|=(2627860687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_box_14 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (168023783/312500000 : ℝ)*x 0 + (1051144059/2000000000 : ℝ)*x 1 + (-1981639081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168023783/312500000 : ℝ)^4413 ≤ (2228776379/5000000000 : ℝ)^3389 := by
    have hnat : (168023783 : ℕ)^4413*5000000000^3389 ≤ 2228776379^3389*312500000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168023783 312500000 2228776379 5000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051144059/2000000000 : ℝ)^4413 ≤ (21636656788567/50000000000000 : ℝ)^3389 := by
    have hnat : (1051144059 : ℕ)^4413*50000000000000^3389 ≤ 21636656788567^3389*2000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051144059 2000000000 21636656788567 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1981639081/10000000000 : ℝ)^4413 ≤ (6075579414549/50000000000000 : ℝ)^3389 := by
    have hnat : (1981639081 : ℕ)^4413*50000000000000^3389 ≤ 6075579414549^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981639081 10000000000 6075579414549 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168023783/312500000 : ℝ), (1051144059/2000000000 : ℝ), (-1981639081/10000000000 : ℝ)] ![(2228776379/5000000000 : ℝ), (21636656788567/50000000000000 : ℝ), (6075579414549/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168023783/312500000 : ℝ)|^4413 ≤ (2228776379/5000000000 : ℝ)^3389
        have hw : |(168023783/312500000 : ℝ)|=(168023783/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1051144059/2000000000 : ℝ)|^4413 ≤ (21636656788567/50000000000000 : ℝ)^3389
        have hw : |(1051144059/2000000000 : ℝ)|=(1051144059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1981639081/10000000000 : ℝ)|^4413 ≤ (6075579414549/50000000000000 : ℝ)^3389
        have hw : |(-1981639081/10000000000 : ℝ)|=(1981639081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_box_15 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4123507887/10000000000 : ℝ)*x 0 + (175569303/400000000 : ℝ)*x 1 + (2194615739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4123507887/10000000000 : ℝ)^4413 ≤ (31551364981551/100000000000000 : ℝ)^3389 := by
    have hnat : (4123507887 : ℕ)^4413*100000000000000^3389 ≤ 31551364981551^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4123507887 10000000000 31551364981551 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (175569303/400000000 : ℝ)^4413 ≤ (34224323071149/100000000000000 : ℝ)^3389 := by
    have hnat : (175569303 : ℕ)^4413*100000000000000^3389 ≤ 34224323071149^3389*400000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175569303 400000000 34224323071149 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2194615739/5000000000 : ℝ)^4413 ≤ (2139019495809/6250000000000 : ℝ)^3389 := by
    have hnat : (2194615739 : ℕ)^4413*6250000000000^3389 ≤ 2139019495809^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194615739 5000000000 2139019495809 6250000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4123507887/10000000000 : ℝ), (175569303/400000000 : ℝ), (2194615739/5000000000 : ℝ)] ![(31551364981551/100000000000000 : ℝ), (34224323071149/100000000000000 : ℝ), (2139019495809/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4123507887/10000000000 : ℝ)|^4413 ≤ (31551364981551/100000000000000 : ℝ)^3389
        have hw : |(4123507887/10000000000 : ℝ)|=(4123507887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(175569303/400000000 : ℝ)|^4413 ≤ (34224323071149/100000000000000 : ℝ)^3389
        have hw : |(175569303/400000000 : ℝ)|=(175569303/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2194615739/5000000000 : ℝ)|^4413 ≤ (2139019495809/6250000000000 : ℝ)^3389
        have hw : |(2194615739/5000000000 : ℝ)|=(2194615739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1453_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79559293/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12583/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29581/50000 : ℝ) ∧ (4029/5000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42387/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14769/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14769/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14769/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14769/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14769/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14769/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11389/100000 : ℝ) ^ (1103/256 : ℝ) ≤ (2151392901922037/25000000000000000000 : ℝ) := by
    have hpowers : (11389/100000 : ℝ)^1103 ≤ (2151392901922037/25000000000000000000 : ℝ)^256 := by
      have hnat : (11389 : ℕ)^1103*25000000000000000000^256 ≤ 2151392901922037^256*100000^1103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11389 100000 2151392901922037 25000000000000000000 1103 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11389/100000 : ℝ)) (X := (2151392901922037/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14769/100000 : ℝ) ^ (1103/256 : ℝ) ≤ (411994412433231/1562500000000000000 : ℝ) := by
    have hpowers : (14769/100000 : ℝ)^1103 ≤ (411994412433231/1562500000000000000 : ℝ)^256 := by
      have hnat : (14769 : ℕ)^1103*1562500000000000000^256 ≤ 411994412433231^256*100000^1103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14769 100000 411994412433231 1562500000000000000 1103 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14769/100000 : ℝ)) (X := (411994412433231/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502151392901922037/12500000000000000000 : ℝ) ≤ (10000399434408787/10000000000000000 : ℝ) ^ (1103/256 : ℝ) := by
    have hpowers : (12502151392901922037/12500000000000000000 : ℝ)^256 ≤ (10000399434408787/10000000000000000 : ℝ)^1103 := by
      have hnat : (12502151392901922037 : ℕ)^256*10000000000000000^1103 ≤ 10000399434408787^1103*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502151392901922037 12500000000000000000 10000399434408787 10000000000000000 256 1103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000399434408787/10000000000000000 : ℝ)) (X := (12502151392901922037/12500000000000000000 : ℝ)) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008743303500853733/25000000000000000000 : ℝ) ≤ (125010144991839/125000000000000 : ℝ) ^ (1103/256 : ℝ) := by
    have hpowers : (25008743303500853733/25000000000000000000 : ℝ)^256 ≤ (125010144991839/125000000000000 : ℝ)^1103 := by
      have hnat : (25008743303500853733 : ℕ)^256*125000000000000^1103 ≤ 125010144991839^1103*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008743303500853733 25000000000000000000 125010144991839 125000000000000 256 1103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125010144991839/125000000000000 : ℝ)) (X := (25008743303500853733/25000000000000000000 : ℝ)) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (781661994412433231/781250000000000000 : ℝ) ≤ (10001223764285453/10000000000000000 : ℝ) ^ (1103/256 : ℝ) := by
    have hpowers : (781661994412433231/781250000000000000 : ℝ)^256 ≤ (10001223764285453/10000000000000000 : ℝ)^1103 := by
      have hnat : (781661994412433231 : ℕ)^256*10000000000000000^1103 ≤ 10001223764285453^1103*781250000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781661994412433231 781250000000000000 10001223764285453 10000000000000000 256 1103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001223764285453/10000000000000000 : ℝ)) (X := (781661994412433231/781250000000000000 : ℝ)) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2151392901922037/25000000000000000000 : ℝ) ≤ ((16895980897668175493/16900000000000000000 : ℝ)+2*(412164938333/338000000000000 : ℝ)*(11389/100000 : ℝ))^(1103/256 : ℝ) := by
    rw [show (16895980897668175493/16900000000000000000 : ℝ)+2*(412164938333/338000000000000 : ℝ)*(11389/100000 : ℝ)=(10000399434408787/10000000000000000 : ℝ) by norm_num, show 1+2*(2151392901922037/25000000000000000000 : ℝ)=(12502151392901922037/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(411994412433231/1562500000000000000 : ℝ)+(2151392901922037/25000000000000000000 : ℝ) ≤ ((16895980897668175493/16900000000000000000 : ℝ)+(412164938333/338000000000000 : ℝ)*((14769/100000 : ℝ)+(11389/100000 : ℝ)))^(1103/256 : ℝ) := by
    rw [show (16895980897668175493/16900000000000000000 : ℝ)+(412164938333/338000000000000 : ℝ)*((14769/100000 : ℝ)+(11389/100000 : ℝ))=(125010144991839/125000000000000 : ℝ) by norm_num, show 1+(411994412433231/1562500000000000000 : ℝ)+(2151392901922037/25000000000000000000 : ℝ)=(25008743303500853733/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(411994412433231/1562500000000000000 : ℝ) ≤ ((16895980897668175493/16900000000000000000 : ℝ)+2*(412164938333/338000000000000 : ℝ)*(14769/100000 : ℝ))^(1103/256 : ℝ) := by
    rw [show (16895980897668175493/16900000000000000000 : ℝ)+2*(412164938333/338000000000000 : ℝ)*(14769/100000 : ℝ)=(10001223764285453/10000000000000000 : ℝ) by norm_num, show 1+2*(411994412433231/1562500000000000000 : ℝ)=(781661994412433231/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16895980897668175493/16900000000000000000 : ℝ)*(X 1 0+X 2 0)+(412164938333/338000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1103/256 : ℝ)) (lo := (11389/100000 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (16895980897668175493/16900000000000000000 : ℝ)) (alpha := (412164938333/338000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16895980897668175493/16900000000000000000 : ℝ)*(X 0 1+X 2 1)+(412164938333/338000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1103/256 : ℝ)) (lo := (11389/100000 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (16895980897668175493/16900000000000000000 : ℝ)) (alpha := (412164938333/338000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16895980897668175493/16900000000000000000 : ℝ)*(X 0 2+X 1 2)+(412164938333/338000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1103/256 : ℝ)) (lo := (11389/100000 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (16895980897668175493/16900000000000000000 : ℝ)) (alpha := (412164938333/338000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1792873771/10000000000 : ℝ)*X 0 0+(1346306659/2500000000 : ℝ)*X 0 1+(2692613129/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1321554163/2500000000 : ℝ)*X 1 0+(-192899439/1000000000 : ℝ)*X 1 1+(5385225853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5286215939/10000000000 : ℝ)*X 2 0+(5385226481/10000000000 : ℝ)*X 2 1+(-1928994501/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((888847617/2000000000 : ℝ)*X 0 0+(2114579281/5000000000 : ℝ)*X 0 1+(4229157827/10000000000 : ℝ)*X 0 2+(888847617/2000000000 : ℝ)*X 1 0+(2114579281/5000000000 : ℝ)*X 1 1+(4229157827/10000000000 : ℝ)*X 1 2+(888847617/2000000000 : ℝ)*X 2 0+(2114579281/5000000000 : ℝ)*X 2 1+(4229157827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-528375533/2500000000 : ℝ)*X 0 0+(131671487/250000000 : ℝ)*X 0 1+(5266857457/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5368975797/10000000000 : ℝ)*X 1 0+(-395440049/2000000000 : ℝ)*X 1 1+(5266858683/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5368975727/10000000000 : ℝ)*X 2 0+(526685849/1000000000 : ℝ)*X 2 1+(-1977200599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4151500859/10000000000 : ℝ)*X 0 0+(4375477239/10000000000 : ℝ)*X 0 1+(218773797/500000000 : ℝ)*X 0 2+(4151500859/10000000000 : ℝ)*X 1 0+(4375477239/10000000000 : ℝ)*X 1 1+(218773797/500000000 : ℝ)*X 1 2+(4151500859/10000000000 : ℝ)*X 2 0+(4375477239/10000000000 : ℝ)*X 2 1+(218773797/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1022958509/5000000000 : ℝ)*X 0 0+(2592439403/5000000000 : ℝ)*X 0 1+(5399185559/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((659556529/1250000000 : ℝ)*X 1 0+(-1923185069/10000000000 : ℝ)*X 1 1+(10798371/20000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276452263/10000000000 : ℝ)*X 2 0+(1349796471/2500000000 : ℝ)*X 2 1+(-240398063/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((179128143/400000000 : ℝ)*X 0 0+(4211888759/10000000000 : ℝ)*X 0 1+(4211888147/10000000000 : ℝ)*X 0 2+(179128143/400000000 : ℝ)*X 1 0+(4211888759/10000000000 : ℝ)*X 1 1+(4211888147/10000000000 : ℝ)*X 1 2+(179128143/400000000 : ℝ)*X 2 0+(4211888759/10000000000 : ℝ)*X 2 1+(4211888147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-465149933/2500000000 : ℝ)*X 0 0+(5465228477/10000000000 : ℝ)*X 0 1+(5255720551/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2688380389/5000000000 : ℝ)*X 1 0+(-247704751/1250000000 : ℝ)*X 1 1+(2627860687/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((168023783/312500000 : ℝ)*X 2 0+(1051144059/2000000000 : ℝ)*X 2 1+(-1981639081/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4123507887/10000000000 : ℝ)*X 0 0+(175569303/400000000 : ℝ)*X 0 1+(2194615739/5000000000 : ℝ)*X 0 2+(4123507887/10000000000 : ℝ)*X 1 0+(175569303/400000000 : ℝ)*X 1 1+(2194615739/5000000000 : ℝ)*X 1 2+(4123507887/10000000000 : ℝ)*X 2 0+(175569303/400000000 : ℝ)*X 2 1+(2194615739/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12583/20000 : ℝ) ≤ (-265804965442072369660467008647137/422500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (64349961/50000000000000 : ℝ)*(lower0) + (193510109/50000000000000 : ℝ)*(lower2) + (206428479/50000000000000 : ℝ)*(lower4) + (67548639/25000000000000 : ℝ)*(lower5) + (3042808831381303/100000000000000 : ℝ)*(major0) + (3042808831381303/100000000000000 : ℝ)*(major1) + (3042808831381303/100000000000000 : ℝ)*(major2) + (2097130725655521/50000000000000 : ℝ)*(sp4) + (838855278753981/20000000000000 : ℝ)*(sp5) + (4194271869129551/100000000000000 : ℝ)*(sp6) + (956145007278189/50000000000000 : ℝ)*(sp7) + (1850142361/5000000000000 : ℝ)*(sp8) + (5515097089/25000000000000 : ℝ)*(sp13) + (2658502871/10000000000000 : ℝ)*(sp14) + (956145007278189/50000000000000 : ℝ)*(f.failure) + (4194298454158261/100000000000000 : ℝ)*(f.sum) + (3026331541699/16900000000000000000000000000 : ℝ)*base65 + (1062681562782042621/1690000000000000000000000000000000 : ℝ)*base68 + (3032689231537957379/1690000000000000000000000000000000 : ℝ)*base69 + (736253922447957379/1690000000000000000000000000000000 : ℝ)*base71 + (36241226991799/16900000000000000000000000000 : ℝ)*base73 + (8893913287887957379/1690000000000000000000000000000000 : ℝ)*base75 + (2448838940487957379/1690000000000000000000000000000000 : ℝ)*base77 + (22126636604817957379/1690000000000000000000000000000000 : ℝ)*base79 + (205188126999/16900000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (3839623/2500000000000000000000 : ℝ)*base90 + (3839623/2500000000000000000000 : ℝ)*base92 + (3839623/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29581/50000 : ℝ) ≤ (399948996997427745051639777/676000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60078823/100000000000000 : ℝ)*(lower0) + (90855279/100000000000000 : ℝ)*(upper2) + (13449997/10000000000000 : ℝ)*(upper3) + (122882627/100000000000000 : ℝ)*(lower5) + (124609563192223/4000000000000 : ℝ)*(major0) + (124609563192223/4000000000000 : ℝ)*(major1) + (124609563192223/4000000000000 : ℝ)*(major2) + (2126473564205703/50000000000000 : ℝ)*(sp0) + (4252727391960697/100000000000000 : ℝ)*(sp1) + (4252944895596359/100000000000000 : ℝ)*(sp2) + (978904806539969/50000000000000 : ℝ)*(sp3) + (33591521/50000000000000 : ℝ)*(sp7) + (21973645071/10000000000000 : ℝ)*(sp9) + (279101881/12500000000000 : ℝ)*(sp10) + (97890484013149/5000000000000 : ℝ)*(f.failure) + (2126473564205703/50000000000000 : ℝ)*(f.sum) + (2351295691627/676000000000000000000000000 : ℝ)*base65 + (316117381246259061/67600000000000000000000000000000 : ℝ)*base68 + (108791710779340939/67600000000000000000000000000000 : ℝ)*base69 + (100625629562540939/67600000000000000000000000000000 : ℝ)*base71 + (2165239292913/135200000000000000000000000 : ℝ)*base74 + (115850240827459061/67600000000000000000000000000000 : ℝ)*base76 + (182569770838940939/67600000000000000000000000000000 : ℝ)*base77 + (692037932148259061/67600000000000000000000000000000 : ℝ)*base80 + (2049806616521/676000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (356343/250000000000000000000 : ℝ)*base90 + (356343/250000000000000000000 : ℝ)*base92 + (356343/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (4029/5000 : ℝ) ≤ (680919714457125888018673641209139/845000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (108844103/100000000000000 : ℝ)*(upper0) + (58939791/50000000000000 : ℝ)*(upper1) + (251490633/100000000000000 : ℝ)*(upper4) + (3421774095198847/100000000000000 : ℝ)*(major0) + (3421774095198847/100000000000000 : ℝ)*(major1) + (3421774095198847/100000000000000 : ℝ)*(major2) + (213775443943/100000000000000 : ℝ)*(sp1) + (91310820863/20000000000000 : ℝ)*(sp2) + (77169720277/100000000000000 : ℝ)*(sp3) + (3931027459/25000000000000 : ℝ)*(sp4) + (1166554102411403/25000000000000 : ℝ)*(sp8) + (933203671662301/20000000000000 : ℝ)*(sp9) + (4665775579651133/100000000000000 : ℝ)*(sp10) + (537594537169769/25000000000000 : ℝ)*(sp11) + (268806914799919/12500000000000 : ℝ)*(f.failure) + (583279016719431/12500000000000 : ℝ)*(f.sum) + (71428432119249/16900000000000000000000000000 : ℝ)*base66 + (11966845555270193429/1690000000000000000000000000000000 : ℝ)*base68 + (6052726891960193429/1690000000000000000000000000000000 : ℝ)*base70 + (29157865804660193429/1690000000000000000000000000000000 : ℝ)*base72 + (52264150954649/16900000000000000000000000000 : ℝ)*base74 + (5432956097070193429/1690000000000000000000000000000000 : ℝ)*base76 + (23753875782580193429/1690000000000000000000000000000000 : ℝ)*base78 + (27827542089420193429/1690000000000000000000000000000000 : ℝ)*base80 + (22019668625549/16900000000000000000000000000 : ℝ)*base82 + (1652733/625000000000000000000 : ℝ)*base90 + (1652733/625000000000000000000 : ℝ)*base92 + (1652733/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-42387/50000 : ℝ) ≤ (-27550846830755091945555434073861/32500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34002921/25000000000000 : ℝ)*(lower0) + (415981037/100000000000000 : ℝ)*(upper3) + (215760527/100000000000000 : ℝ)*(lower4) + (3459525158929033/100000000000000 : ℝ)*(major0) + (3459525158929033/100000000000000 : ℝ)*(major1) + (3459525158929033/100000000000000 : ℝ)*(major2) + (12739861227/50000000000000 : ℝ)*(sp0) + (317069068963/100000000000000 : ℝ)*(sp5) + (382315975377/50000000000000 : ℝ)*(sp6) + (13472920809/20000000000000 : ℝ)*(sp7) + (2386550842957779/50000000000000 : ℝ)*(sp12) + (4772810096569049/100000000000000 : ℝ)*(sp13) + (2386181266843629/50000000000000 : ℝ)*(sp14) + (1087056533208387/50000000000000 : ℝ)*(sp15) + (2174180431020819/100000000000000 : ℝ)*(f.failure) + (1193281791409503/25000000000000 : ℝ)*(f.sum) + (46121563041289/16900000000000000000000000000 : ℝ)*base65 + (22135244941273761731/1690000000000000000000000000000000 : ℝ)*base68 + (4967379450296238269/1690000000000000000000000000000000 : ℝ)*base69 + (15218320178863761731/1690000000000000000000000000000000 : ℝ)*base72 + (67903544356211/16900000000000000000000000000 : ℝ)*base74 + (15539552845553761731/1690000000000000000000000000000000 : ℝ)*base76 + (13664067693233761731/1690000000000000000000000000000000 : ℝ)*base78 + (26281275736673761731/1690000000000000000000000000000000 : ℝ)*base80 + (132384722718789/16900000000000000000000000000 : ℝ)*base81 + (22079033/5000000000000000000000 : ℝ)*base90 + (22079033/5000000000000000000000 : ℝ)*base92 + (22079033/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1453_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79559293/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12583/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29581/50000 : ℝ) else (4029/5000 : ℝ) ≤ X j i ∧ X j i ≤ (42387/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1453_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1453_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79559293/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12583/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29581/50000 : ℝ) else (4029/5000 : ℝ) ≤ X j i ∧ X j i ≤ (42387/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1453_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1453_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1453_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79559293/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12583/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29581/50000 : ℝ) else (4029/5000 : ℝ) ≤ X j i ∧ X j i ≤ (42387/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1453_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
