-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1291_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:25:50.383257+00:00
-- url     : https://prove2.me/submissions/4fdee209-dcdd-4fa4-a109-e68739a93cd6

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
theorem support_rectangle_w1291_s3_0 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2086497257/10000000000 : ℝ)*x 0 + (679278699/1250000000 : ℝ)*x 1 + (1045112269/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2086497257/10000000000 : ℝ)^4251 ≤ (6344884508427/50000000000000 : ℝ)^3227 := by
    have hnat : (2086497257 : ℕ)^4251*50000000000000^3227 ≤ 6344884508427^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086497257 10000000000 6344884508427 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679278699/1250000000 : ℝ)^4251 ≤ (44780741618939/100000000000000 : ℝ)^3227 := by
    have hnat : (679278699 : ℕ)^4251*100000000000000^3227 ≤ 44780741618939^3227*1250000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679278699 1250000000 44780741618939 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1045112269/2000000000 : ℝ)^4251 ≤ (42529489340531/100000000000000 : ℝ)^3227 := by
    have hnat : (1045112269 : ℕ)^4251*100000000000000^3227 ≤ 42529489340531^3227*2000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045112269 2000000000 42529489340531 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2086497257/10000000000 : ℝ), (679278699/1250000000 : ℝ), (1045112269/2000000000 : ℝ)] ![(6344884508427/50000000000000 : ℝ), (44780741618939/100000000000000 : ℝ), (42529489340531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2086497257/10000000000 : ℝ)|^4251 ≤ (6344884508427/50000000000000 : ℝ)^3227
        have hw : |(-2086497257/10000000000 : ℝ)|=(2086497257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679278699/1250000000 : ℝ)|^4251 ≤ (44780741618939/100000000000000 : ℝ)^3227
        have hw : |(679278699/1250000000 : ℝ)|=(679278699/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1045112269/2000000000 : ℝ)|^4251 ≤ (42529489340531/100000000000000 : ℝ)^3227
        have hw : |(1045112269/2000000000 : ℝ)|=(1045112269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s3_1 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669323743/1250000000 : ℝ)*x 0 + (-2193294419/10000000000 : ℝ)*x 1 + (1045112263/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669323743/1250000000 : ℝ)^4251 ≤ (8783647820289/20000000000000 : ℝ)^3227 := by
    have hnat : (669323743 : ℕ)^4251*20000000000000^3227 ≤ 8783647820289^3227*1250000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669323743 1250000000 8783647820289 20000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2193294419/10000000000 : ℝ)^4251 ≤ (1694033984179/12500000000000 : ℝ)^3227 := by
    have hnat : (2193294419 : ℕ)^4251*12500000000000^3227 ≤ 1694033984179^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193294419 10000000000 1694033984179 12500000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1045112263/2000000000 : ℝ)^4251 ≤ (42529489018891/100000000000000 : ℝ)^3227 := by
    have hnat : (1045112263 : ℕ)^4251*100000000000000^3227 ≤ 42529489018891^3227*2000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045112263 2000000000 42529489018891 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669323743/1250000000 : ℝ), (-2193294419/10000000000 : ℝ), (1045112263/2000000000 : ℝ)] ![(8783647820289/20000000000000 : ℝ), (1694033984179/12500000000000 : ℝ), (42529489018891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669323743/1250000000 : ℝ)|^4251 ≤ (8783647820289/20000000000000 : ℝ)^3227
        have hw : |(669323743/1250000000 : ℝ)|=(669323743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2193294419/10000000000 : ℝ)|^4251 ≤ (1694033984179/12500000000000 : ℝ)^3227
        have hw : |(-2193294419/10000000000 : ℝ)|=(2193294419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1045112263/2000000000 : ℝ)|^4251 ≤ (42529489018891/100000000000000 : ℝ)^3227
        have hw : |(1045112263/2000000000 : ℝ)|=(1045112263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s3_2 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677294929/5000000000 : ℝ)*x 0 + (5225561621/10000000000 : ℝ)*x 1 + (-137080883/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677294929/5000000000 : ℝ)^4251 ≤ (8783647634449/20000000000000 : ℝ)^3227 := by
    have hnat : (2677294929 : ℕ)^4251*20000000000000^3227 ≤ 8783647634449^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677294929 5000000000 8783647634449 20000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5225561621/10000000000 : ℝ)^4251 ≤ (42529492299623/100000000000000 : ℝ)^3227 := by
    have hnat : (5225561621 : ℕ)^4251*100000000000000^3227 ≤ 42529492299623^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225561621 10000000000 42529492299623 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137080883/625000000 : ℝ)^4251 ≤ (2710453900957/20000000000000 : ℝ)^3227 := by
    have hnat : (137080883 : ℕ)^4251*20000000000000^3227 ≤ 2710453900957^3227*625000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137080883 625000000 2710453900957 20000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677294929/5000000000 : ℝ), (5225561621/10000000000 : ℝ), (-137080883/625000000 : ℝ)] ![(8783647634449/20000000000000 : ℝ), (42529492299623/100000000000000 : ℝ), (2710453900957/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677294929/5000000000 : ℝ)|^4251 ≤ (8783647634449/20000000000000 : ℝ)^3227
        have hw : |(2677294929/5000000000 : ℝ)|=(2677294929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5225561621/10000000000 : ℝ)|^4251 ≤ (42529492299623/100000000000000 : ℝ)^3227
        have hw : |(5225561621/10000000000 : ℝ)|=(5225561621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-137080883/625000000 : ℝ)|^4251 ≤ (2710453900957/20000000000000 : ℝ)^3227
        have hw : |(-137080883/625000000 : ℝ)|=(137080883/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s3_3 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4338707359/10000000000 : ℝ)*x 0 + (4129418523/10000000000 : ℝ)*x 1 + (4558116913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4338707359/10000000000 : ℝ)^4251 ≤ (33287916079289/100000000000000 : ℝ)^3227 := by
    have hnat : (4338707359 : ℕ)^4251*100000000000000^3227 ≤ 33287916079289^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4338707359 10000000000 33287916079289 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4129418523/10000000000 : ℝ)^4251 ≤ (6237804629077/20000000000000 : ℝ)^3227 := by
    have hnat : (4129418523 : ℕ)^4251*20000000000000^3227 ≤ 6237804629077^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129418523 10000000000 6237804629077 20000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4558116913/10000000000 : ℝ)^4251 ≤ (7104612152631/20000000000000 : ℝ)^3227 := by
    have hnat : (4558116913 : ℕ)^4251*20000000000000^3227 ≤ 7104612152631^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4558116913 10000000000 7104612152631 20000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4338707359/10000000000 : ℝ), (4129418523/10000000000 : ℝ), (4558116913/10000000000 : ℝ)] ![(33287916079289/100000000000000 : ℝ), (6237804629077/20000000000000 : ℝ), (7104612152631/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4338707359/10000000000 : ℝ)|^4251 ≤ (33287916079289/100000000000000 : ℝ)^3227
        have hw : |(4338707359/10000000000 : ℝ)|=(4338707359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4129418523/10000000000 : ℝ)|^4251 ≤ (6237804629077/20000000000000 : ℝ)^3227
        have hw : |(4129418523/10000000000 : ℝ)|=(4129418523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4558116913/10000000000 : ℝ)|^4251 ≤ (7104612152631/20000000000000 : ℝ)^3227
        have hw : |(4558116913/10000000000 : ℝ)|=(4558116913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s3_4 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-521629979/2500000000 : ℝ)*x 0 + (2613230361/5000000000 : ℝ)*x 1 + (108666491/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (521629979/2500000000 : ℝ)^4251 ≤ (12689950555681/100000000000000 : ℝ)^3227 := by
    have hnat : (521629979 : ℕ)^4251*100000000000000^3227 ≤ 12689950555681^3227*2500000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521629979 2500000000 12689950555681 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2613230361/5000000000 : ℝ)^4251 ≤ (21269566068421/50000000000000 : ℝ)^3227 := by
    have hnat : (2613230361 : ℕ)^4251*50000000000000^3227 ≤ 21269566068421^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613230361 5000000000 21269566068421 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108666491/200000000 : ℝ)^4251 ≤ (8954183458903/20000000000000 : ℝ)^3227 := by
    have hnat : (108666491 : ℕ)^4251*20000000000000^3227 ≤ 8954183458903^3227*200000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108666491 200000000 8954183458903 20000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-521629979/2500000000 : ℝ), (2613230361/5000000000 : ℝ), (108666491/200000000 : ℝ)] ![(12689950555681/100000000000000 : ℝ), (21269566068421/50000000000000 : ℝ), (8954183458903/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-521629979/2500000000 : ℝ)|^4251 ≤ (12689950555681/100000000000000 : ℝ)^3227
        have hw : |(-521629979/2500000000 : ℝ)|=(521629979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2613230361/5000000000 : ℝ)|^4251 ≤ (21269566068421/50000000000000 : ℝ)^3227
        have hw : |(2613230361/5000000000 : ℝ)|=(2613230361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(108666491/200000000 : ℝ)|^4251 ≤ (8954183458903/20000000000000 : ℝ)^3227
        have hw : |(108666491/200000000 : ℝ)|=(108666491/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s3_5 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2650584089/5000000000 : ℝ)*x 0 + (-1985531027/10000000000 : ℝ)*x 1 + (2716662251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650584089/5000000000 : ℝ)^4251 ≤ (43341951193983/100000000000000 : ℝ)^3227 := by
    have hnat : (2650584089 : ℕ)^4251*100000000000000^3227 ≤ 43341951193983^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650584089 5000000000 43341951193983 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1985531027/10000000000 : ℝ)^4251 ≤ (11887132031517/100000000000000 : ℝ)^3227 := by
    have hnat : (1985531027 : ℕ)^4251*100000000000000^3227 ≤ 11887132031517^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1985531027 10000000000 11887132031517 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716662251/5000000000 : ℝ)^4251 ≤ (11192729193371/25000000000000 : ℝ)^3227 := by
    have hnat : (2716662251 : ℕ)^4251*25000000000000^3227 ≤ 11192729193371^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716662251 5000000000 11192729193371 25000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650584089/5000000000 : ℝ), (-1985531027/10000000000 : ℝ), (2716662251/5000000000 : ℝ)] ![(43341951193983/100000000000000 : ℝ), (11887132031517/100000000000000 : ℝ), (11192729193371/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650584089/5000000000 : ℝ)|^4251 ≤ (43341951193983/100000000000000 : ℝ)^3227
        have hw : |(2650584089/5000000000 : ℝ)|=(2650584089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1985531027/10000000000 : ℝ)|^4251 ≤ (11887132031517/100000000000000 : ℝ)^3227
        have hw : |(-1985531027/10000000000 : ℝ)|=(1985531027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716662251/5000000000 : ℝ)|^4251 ≤ (11192729193371/25000000000000 : ℝ)^3227
        have hw : |(2716662251/5000000000 : ℝ)|=(2716662251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s3_6 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530116821/1000000000 : ℝ)*x 0 + (2716662223/5000000000 : ℝ)*x 1 + (-992765529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530116821/1000000000 : ℝ)^4251 ≤ (21670975769317/50000000000000 : ℝ)^3227 := by
    have hnat : (530116821 : ℕ)^4251*50000000000000^3227 ≤ 21670975769317^3227*1000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530116821 1000000000 21670975769317 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716662223/5000000000 : ℝ)^4251 ≤ (22385458082807/50000000000000 : ℝ)^3227 := by
    have hnat : (2716662223 : ℕ)^4251*50000000000000^3227 ≤ 22385458082807^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716662223 5000000000 22385458082807 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (992765529/5000000000 : ℝ)^4251 ≤ (11887132276003/100000000000000 : ℝ)^3227 := by
    have hnat : (992765529 : ℕ)^4251*100000000000000^3227 ≤ 11887132276003^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992765529 5000000000 11887132276003 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530116821/1000000000 : ℝ), (2716662223/5000000000 : ℝ), (-992765529/5000000000 : ℝ)] ![(21670975769317/50000000000000 : ℝ), (22385458082807/50000000000000 : ℝ), (11887132276003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530116821/1000000000 : ℝ)|^4251 ≤ (21670975769317/50000000000000 : ℝ)^3227
        have hw : |(530116821/1000000000 : ℝ)|=(530116821/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716662223/5000000000 : ℝ)|^4251 ≤ (22385458082807/50000000000000 : ℝ)^3227
        have hw : |(2716662223/5000000000 : ℝ)|=(2716662223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-992765529/5000000000 : ℝ)|^4251 ≤ (11887132276003/100000000000000 : ℝ)^3227
        have hw : |(-992765529/5000000000 : ℝ)|=(992765529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s3_7 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4338754051/10000000000 : ℝ)*x 0 + (4556269133/10000000000 : ℝ)*x 1 + (516409681/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4338754051/10000000000 : ℝ)^4251 ≤ (16644193995963/50000000000000 : ℝ)^3227 := by
    have hnat : (4338754051 : ℕ)^4251*50000000000000^3227 ≤ 16644193995963^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4338754051 10000000000 16644193995963 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4556269133/10000000000 : ℝ)^4251 ≤ (17752045991933/50000000000000 : ℝ)^3227 := by
    have hnat : (4556269133 : ℕ)^4251*50000000000000^3227 ≤ 17752045991933^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4556269133 10000000000 17752045991933 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516409681/1250000000 : ℝ)^4251 ≤ (31207520000449/100000000000000 : ℝ)^3227 := by
    have hnat : (516409681 : ℕ)^4251*100000000000000^3227 ≤ 31207520000449^3227*1250000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516409681 1250000000 31207520000449 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4338754051/10000000000 : ℝ), (4556269133/10000000000 : ℝ), (516409681/1250000000 : ℝ)] ![(16644193995963/50000000000000 : ℝ), (17752045991933/50000000000000 : ℝ), (31207520000449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4338754051/10000000000 : ℝ)|^4251 ≤ (16644193995963/50000000000000 : ℝ)^3227
        have hw : |(4338754051/10000000000 : ℝ)|=(4338754051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4556269133/10000000000 : ℝ)|^4251 ≤ (17752045991933/50000000000000 : ℝ)^3227
        have hw : |(4556269133/10000000000 : ℝ)|=(4556269133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(516409681/1250000000 : ℝ)|^4251 ≤ (31207520000449/100000000000000 : ℝ)^3227
        have hw : |(516409681/1250000000 : ℝ)|=(516409681/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1291_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76361297/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8161/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9497/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10653/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3767/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8161/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9497/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8161/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9497/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8161/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9497/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8161/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9497/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8161/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9497/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8161/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9497/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9497/100000 : ℝ) ^ (2125/512 : ℝ) ≤ (5709319370107789/100000000000000000000 : ℝ) := by
    have hpowers : (9497/100000 : ℝ)^2125 ≤ (5709319370107789/100000000000000000000 : ℝ)^512 := by
      have hnat : (9497 : ℕ)^2125*100000000000000000000^512 ≤ 5709319370107789^512*100000^2125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9497 100000 5709319370107789 100000000000000000000 2125 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9497/100000 : ℝ)) (X := (5709319370107789/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have hpowhi : (8161/50000 : ℝ) ^ (2125/512 : ℝ) ≤ (10807667756462017/20000000000000000000 : ℝ) := by
    have hpowers : (8161/50000 : ℝ)^2125 ≤ (10807667756462017/20000000000000000000 : ℝ)^512 := by
      have hnat : (8161 : ℕ)^2125*20000000000000000000^512 ≤ 10807667756462017^512*50000^2125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8161 50000 10807667756462017 20000000000000000000 2125 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8161/50000 : ℝ)) (X := (10807667756462017/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005709319370107789/50000000000000000000 : ℝ) ≤ (5000137555051493/5000000000000000 : ℝ) ^ (2125/512 : ℝ) := by
    have hpowers : (50005709319370107789/50000000000000000000 : ℝ)^512 ≤ (5000137555051493/5000000000000000 : ℝ)^2125 := by
      have hnat : (50005709319370107789 : ℕ)^512*5000000000000000^2125 ≤ 5000137555051493^2125*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005709319370107789 50000000000000000000 5000137555051493 5000000000000000 512 2125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000137555051493/5000000000000000 : ℝ)) (X := (50005709319370107789/50000000000000000000 : ℝ)) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50029873829076208937/50000000000000000000 : ℝ) ≤ (10001439240782831/10000000000000000 : ℝ) ^ (2125/512 : ℝ) := by
    have hpowers : (50029873829076208937/50000000000000000000 : ℝ)^512 ≤ (10001439240782831/10000000000000000 : ℝ)^2125 := by
      have hnat : (50029873829076208937 : ℕ)^512*10000000000000000^2125 ≤ 10001439240782831^2125*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029873829076208937 50000000000000000000 10001439240782831 10000000000000000 512 2125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001439240782831/10000000000000000 : ℝ)) (X := (50029873829076208937/50000000000000000000 : ℝ)) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10010807667756462017/10000000000000000000 : ℝ) ≤ (2500650842865669/2500000000000000 : ℝ) ^ (2125/512 : ℝ) := by
    have hpowers : (10010807667756462017/10000000000000000000 : ℝ)^512 ≤ (2500650842865669/2500000000000000 : ℝ)^2125 := by
      have hnat : (10010807667756462017 : ℕ)^512*2500000000000000^2125 ≤ 2500650842865669^2125*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10010807667756462017 10000000000000000000 2500650842865669 2500000000000000 512 2125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500650842865669/2500000000000000 : ℝ)) (X := (10010807667756462017/10000000000000000000 : ℝ)) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5709319370107789/100000000000000000000 : ℝ) ≤ ((60919434043142771/60937500000000000 : ℝ)+2*(33260876567/19500000000000 : ℝ)*(9497/100000 : ℝ))^(2125/512 : ℝ) := by
    rw [show (60919434043142771/60937500000000000 : ℝ)+2*(33260876567/19500000000000 : ℝ)*(9497/100000 : ℝ)=(5000137555051493/5000000000000000 : ℝ) by norm_num, show 1+2*(5709319370107789/100000000000000000000 : ℝ)=(50005709319370107789/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10807667756462017/20000000000000000000 : ℝ)+(5709319370107789/100000000000000000000 : ℝ) ≤ ((60919434043142771/60937500000000000 : ℝ)+(33260876567/19500000000000 : ℝ)*((8161/50000 : ℝ)+(9497/100000 : ℝ)))^(2125/512 : ℝ) := by
    rw [show (60919434043142771/60937500000000000 : ℝ)+(33260876567/19500000000000 : ℝ)*((8161/50000 : ℝ)+(9497/100000 : ℝ))=(10001439240782831/10000000000000000 : ℝ) by norm_num, show 1+(10807667756462017/20000000000000000000 : ℝ)+(5709319370107789/100000000000000000000 : ℝ)=(50029873829076208937/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10807667756462017/20000000000000000000 : ℝ) ≤ ((60919434043142771/60937500000000000 : ℝ)+2*(33260876567/19500000000000 : ℝ)*(8161/50000 : ℝ))^(2125/512 : ℝ) := by
    rw [show (60919434043142771/60937500000000000 : ℝ)+2*(33260876567/19500000000000 : ℝ)*(8161/50000 : ℝ)=(2500650842865669/2500000000000000 : ℝ) by norm_num, show 1+2*(10807667756462017/20000000000000000000 : ℝ)=(10010807667756462017/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (60919434043142771/60937500000000000 : ℝ)*(X 1 0+X 2 0)+(33260876567/19500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2125/512 : ℝ)) (lo := (9497/100000 : ℝ)) (hi := (8161/50000 : ℝ)) (c := (60919434043142771/60937500000000000 : ℝ)) (alpha := (33260876567/19500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (60919434043142771/60937500000000000 : ℝ)*(X 0 1+X 2 1)+(33260876567/19500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2125/512 : ℝ)) (lo := (9497/100000 : ℝ)) (hi := (8161/50000 : ℝ)) (c := (60919434043142771/60937500000000000 : ℝ)) (alpha := (33260876567/19500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (60919434043142771/60937500000000000 : ℝ)*(X 0 2+X 1 2)+(33260876567/19500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2125/512 : ℝ)) (lo := (9497/100000 : ℝ)) (hi := (8161/50000 : ℝ)) (c := (60919434043142771/60937500000000000 : ℝ)) (alpha := (33260876567/19500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2086497257/10000000000 : ℝ)*X 0 0+(679278699/1250000000 : ℝ)*X 0 1+(1045112269/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669323743/1250000000 : ℝ)*X 1 0+(-2193294419/10000000000 : ℝ)*X 1 1+(1045112263/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677294929/5000000000 : ℝ)*X 2 0+(5225561621/10000000000 : ℝ)*X 2 1+(-137080883/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4338707359/10000000000 : ℝ)*X 0 0+(4129418523/10000000000 : ℝ)*X 0 1+(4558116913/10000000000 : ℝ)*X 0 2+(4338707359/10000000000 : ℝ)*X 1 0+(4129418523/10000000000 : ℝ)*X 1 1+(4558116913/10000000000 : ℝ)*X 1 2+(4338707359/10000000000 : ℝ)*X 2 0+(4129418523/10000000000 : ℝ)*X 2 1+(4558116913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-521629979/2500000000 : ℝ)*X 0 0+(2613230361/5000000000 : ℝ)*X 0 1+(108666491/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2650584089/5000000000 : ℝ)*X 1 0+(-1985531027/10000000000 : ℝ)*X 1 1+(2716662251/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530116821/1000000000 : ℝ)*X 2 0+(2716662223/5000000000 : ℝ)*X 2 1+(-992765529/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4338754051/10000000000 : ℝ)*X 0 0+(4556269133/10000000000 : ℝ)*X 0 1+(516409681/1250000000 : ℝ)*X 0 2+(4338754051/10000000000 : ℝ)*X 1 0+(4556269133/10000000000 : ℝ)*X 1 1+(516409681/1250000000 : ℝ)*X 1 2+(4338754051/10000000000 : ℝ)*X 2 0+(4556269133/10000000000 : ℝ)*X 2 1+(516409681/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10256450392054306570297929/1015625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (214023313/12500000000000 : ℝ)*(base19) + (1595864543/100000000000000 : ℝ)*(base23) + (5267839/25000000000000 : ℝ)*(lower2) + (54529389/100000000000000 : ℝ)*(upper3) + (301971869/100000000000000 : ℝ)*(upper5) + (1781257921520537/50000000000000 : ℝ)*(major0) + (1781257921520537/50000000000000 : ℝ)*(major1) + (1781257921520537/50000000000000 : ℝ)*(major2) + (4792324200266523/100000000000000 : ℝ)*(sp0) + (2396179258935347/50000000000000 : ℝ)*(sp1) + (958471726838531/20000000000000 : ℝ)*(sp2) + (1166329106357863/50000000000000 : ℝ)*(sp3) + (1441191627/4000000000000 : ℝ)*(sp4) + (6453343629/50000000000000 : ℝ)*(sp7) + (291583889925373/12500000000000 : ℝ)*(f.failure) + (2396180115028599/50000000000000 : ℝ)*(f.sum) + (2851471008983/975000000000000000000000000 : ℝ)*base65 + (1270662250286827/126953125000000000000000000000 : ℝ)*base68 + (142036241689759/1015625000000000000000000000000 : ℝ)*base69 + (1728849561694183/507812500000000000000000000000 : ℝ)*base72 + (445165683451/121875000000000000000000000 : ℝ)*base73 + (1282822299555817/507812500000000000000000000000 : ℝ)*base75 + (888899275026779/253906250000000000000000000000 : ℝ)*base78 + (8078369194247741/1015625000000000000000000000000 : ℝ)*base80 + (1280317142627/243750000000000000000000000 : ℝ)*base81 + (2988781/625000000000000000000 : ℝ)*base89 + (2988781/625000000000000000000 : ℝ)*base91 + (2988781/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5211492214954460511493519/507812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2332445363/100000000000000 : ℝ)*(base19) + (494425121/20000000000000 : ℝ)*(base23) + (9602147/4000000000000 : ℝ)*(upper3) + (5478889/10000000000000 : ℝ)*(lower4) + (32216071/12500000000000 : ℝ)*(upper5) + (3593542400035147/100000000000000 : ℝ)*(major0) + (3593542400035147/100000000000000 : ℝ)*(major1) + (3593542400035147/100000000000000 : ℝ)*(major2) + (38596575987/100000000000000 : ℝ)*(sp1) + (39305896239/100000000000000 : ℝ)*(sp2) + (4834097708664319/100000000000000 : ℝ)*(sp4) + (604257097455371/12500000000000 : ℝ)*(sp5) + (2417027965321237/50000000000000 : ℝ)*(sp6) + (94119469972731/4000000000000 : ℝ)*(sp7) + (94119469972731/4000000000000 : ℝ)*(f.failure) + (4834097708664319/100000000000000 : ℝ)*(f.sum) + (2831568249937/487500000000000000000000000 : ℝ)*base65 + (1944581412882851/507812500000000000000000000000 : ℝ)*base67 + (1878012291312577/1015625000000000000000000000000 : ℝ)*base69 + (1460613165539101/507812500000000000000000000000 : ℝ)*base71 + (164218336499/975000000000000000000000000 : ℝ)*base73 + (4057774091960899/507812500000000000000000000000 : ℝ)*base76 + (435902175916997/63476562500000000000000000000 : ℝ)*base77 + (3890915187124923/1015625000000000000000000000000 : ℝ)*base80 + (471870912751/975000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (207893/200000000000000000000 : ℝ)*base90 + (207893/200000000000000000000 : ℝ)*base92 + (207893/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1291_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76361297/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8161/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9497/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10653/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3767/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1291_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1291_s4_0 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-208842753/1000000000 : ℝ)*x 0 + (5419013719/10000000000 : ℝ)*x 1 + (5239512049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208842753/1000000000 : ℝ)^4251 ≤ (3176309043543/25000000000000 : ℝ)^3227 := by
    have hnat : (208842753 : ℕ)^4251*25000000000000^3227 ≤ 3176309043543^3227*1000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208842753 1000000000 3176309043543 25000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419013719/10000000000 : ℝ)^4251 ≤ (22307820403221/50000000000000 : ℝ)^3227 := by
    have hnat : (5419013719 : ℕ)^4251*50000000000000^3227 ≤ 22307820403221^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419013719 10000000000 22307820403221 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239512049/10000000000 : ℝ)^4251 ≤ (666861296829/1562500000000 : ℝ)^3227 := by
    have hnat : (5239512049 : ℕ)^4251*1562500000000^3227 ≤ 666861296829^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239512049 10000000000 666861296829 1562500000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-208842753/1000000000 : ℝ), (5419013719/10000000000 : ℝ), (5239512049/10000000000 : ℝ)] ![(3176309043543/25000000000000 : ℝ), (22307820403221/50000000000000 : ℝ), (666861296829/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-208842753/1000000000 : ℝ)|^4251 ≤ (3176309043543/25000000000000 : ℝ)^3227
        have hw : |(-208842753/1000000000 : ℝ)|=(208842753/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419013719/10000000000 : ℝ)|^4251 ≤ (22307820403221/50000000000000 : ℝ)^3227
        have hw : |(5419013719/10000000000 : ℝ)|=(5419013719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239512049/10000000000 : ℝ)|^4251 ≤ (666861296829/1562500000000 : ℝ)^3227
        have hw : |(5239512049/10000000000 : ℝ)|=(5239512049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s4_1 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350744981/10000000000 : ℝ)*x 0 + (-545000439/2500000000 : ℝ)*x 1 + (2619755959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350744981/10000000000 : ℝ)^4251 ≤ (43876700342659/100000000000000 : ℝ)^3227 := by
    have hnat : (5350744981 : ℕ)^4251*100000000000000^3227 ≤ 43876700342659^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350744981 10000000000 43876700342659 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545000439/2500000000 : ℝ)^4251 ≤ (13444178040309/100000000000000 : ℝ)^3227 := by
    have hnat : (545000439 : ℕ)^4251*100000000000000^3227 ≤ 13444178040309^3227*2500000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545000439 2500000000 13444178040309 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2619755959/5000000000 : ℝ)^4251 ≤ (42679121591371/100000000000000 : ℝ)^3227 := by
    have hnat : (2619755959 : ℕ)^4251*100000000000000^3227 ≤ 42679121591371^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619755959 5000000000 42679121591371 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350744981/10000000000 : ℝ), (-545000439/2500000000 : ℝ), (2619755959/5000000000 : ℝ)] ![(43876700342659/100000000000000 : ℝ), (13444178040309/100000000000000 : ℝ), (42679121591371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350744981/10000000000 : ℝ)|^4251 ≤ (43876700342659/100000000000000 : ℝ)^3227
        have hw : |(5350744981/10000000000 : ℝ)|=(5350744981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-545000439/2500000000 : ℝ)|^4251 ≤ (13444178040309/100000000000000 : ℝ)^3227
        have hw : |(-545000439/2500000000 : ℝ)|=(545000439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2619755959/5000000000 : ℝ)|^4251 ≤ (42679121591371/100000000000000 : ℝ)^3227
        have hw : |(2619755959/5000000000 : ℝ)|=(2619755959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s4_2 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350744799/10000000000 : ℝ)*x 0 + (523951233/1000000000 : ℝ)*x 1 + (-1090000727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350744799/10000000000 : ℝ)^4251 ≤ (2193834918833/5000000000000 : ℝ)^3227 := by
    have hnat : (5350744799 : ℕ)^4251*5000000000000^3227 ≤ 2193834918833^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350744799 10000000000 2193834918833 5000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523951233/1000000000 : ℝ)^4251 ≤ (8535825202461/20000000000000 : ℝ)^3227 := by
    have hnat : (523951233 : ℕ)^4251*20000000000000^3227 ≤ 8535825202461^3227*1000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523951233 1000000000 8535825202461 20000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090000727/5000000000 : ℝ)^4251 ≤ (13444175586863/100000000000000 : ℝ)^3227 := by
    have hnat : (1090000727 : ℕ)^4251*100000000000000^3227 ≤ 13444175586863^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090000727 5000000000 13444175586863 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350744799/10000000000 : ℝ), (523951233/1000000000 : ℝ), (-1090000727/5000000000 : ℝ)] ![(2193834918833/5000000000000 : ℝ), (8535825202461/20000000000000 : ℝ), (13444175586863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350744799/10000000000 : ℝ)|^4251 ≤ (2193834918833/5000000000000 : ℝ)^3227
        have hw : |(5350744799/10000000000 : ℝ)|=(5350744799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(523951233/1000000000 : ℝ)|^4251 ≤ (8535825202461/20000000000000 : ℝ)^3227
        have hw : |(523951233/1000000000 : ℝ)|=(523951233/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1090000727/5000000000 : ℝ)|^4251 ≤ (13444175586863/100000000000000 : ℝ)^3227
        have hw : |(-1090000727/5000000000 : ℝ)|=(1090000727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s4_3 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4339874931/10000000000 : ℝ)*x 0 + (519903993/1250000000 : ℝ)*x 1 + (4528009309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4339874931/10000000000 : ℝ)^4251 ≤ (3329971712797/10000000000000 : ℝ)^3227 := by
    have hnat : (4339874931 : ℕ)^4251*10000000000000^3227 ≤ 3329971712797^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339874931 10000000000 3329971712797 10000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (519903993/1250000000 : ℝ)^4251 ≤ (629719871509/2000000000000 : ℝ)^3227 := by
    have hnat : (519903993 : ℕ)^4251*2000000000000^3227 ≤ 629719871509^3227*1250000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519903993 1250000000 629719871509 2000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4528009309/10000000000 : ℝ)^4251 ≤ (35214289278077/100000000000000 : ℝ)^3227 := by
    have hnat : (4528009309 : ℕ)^4251*100000000000000^3227 ≤ 35214289278077^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4528009309 10000000000 35214289278077 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4339874931/10000000000 : ℝ), (519903993/1250000000 : ℝ), (4528009309/10000000000 : ℝ)] ![(3329971712797/10000000000000 : ℝ), (629719871509/2000000000000 : ℝ), (35214289278077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4339874931/10000000000 : ℝ)|^4251 ≤ (3329971712797/10000000000000 : ℝ)^3227
        have hw : |(4339874931/10000000000 : ℝ)|=(4339874931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(519903993/1250000000 : ℝ)|^4251 ≤ (629719871509/2000000000000 : ℝ)^3227
        have hw : |(519903993/1250000000 : ℝ)|=(519903993/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4528009309/10000000000 : ℝ)|^4251 ≤ (35214289278077/100000000000000 : ℝ)^3227
        have hw : |(4528009309/10000000000 : ℝ)|=(4528009309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s4_4 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2088442063/10000000000 : ℝ)*x 0 + (5240178373/10000000000 : ℝ)*x 1 + (1083668743/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2088442063/10000000000 : ℝ)^4251 ≤ (12705352643407/100000000000000 : ℝ)^3227 := by
    have hnat : (2088442063 : ℕ)^4251*100000000000000^3227 ≤ 12705352643407^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088442063 10000000000 12705352643407 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240178373/10000000000 : ℝ)^4251 ≤ (5335784134839/12500000000000 : ℝ)^3227 := by
    have hnat : (5240178373 : ℕ)^4251*12500000000000^3227 ≤ 5335784134839^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240178373 10000000000 5335784134839 12500000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083668743/2000000000 : ℝ)^4251 ≤ (44608374262573/100000000000000 : ℝ)^3227 := by
    have hnat : (1083668743 : ℕ)^4251*100000000000000^3227 ≤ 44608374262573^3227*2000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083668743 2000000000 44608374262573 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2088442063/10000000000 : ℝ), (5240178373/10000000000 : ℝ), (1083668743/2000000000 : ℝ)] ![(12705352643407/100000000000000 : ℝ), (5335784134839/12500000000000 : ℝ), (44608374262573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2088442063/10000000000 : ℝ)|^4251 ≤ (12705352643407/100000000000000 : ℝ)^3227
        have hw : |(-2088442063/10000000000 : ℝ)|=(2088442063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240178373/10000000000 : ℝ)|^4251 ≤ (5335784134839/12500000000000 : ℝ)^3227
        have hw : |(5240178373/10000000000 : ℝ)|=(5240178373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083668743/2000000000 : ℝ)|^4251 ≤ (44608374262573/100000000000000 : ℝ)^3227
        have hw : |(1083668743/2000000000 : ℝ)|=(1083668743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s4_5 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326198459/2500000000 : ℝ)*x 0 + (-2001169687/10000000000 : ℝ)*x 1 + (42330809/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326198459/2500000000 : ℝ)^4251 ≤ (21690502482201/50000000000000 : ℝ)^3227 := by
    have hnat : (1326198459 : ℕ)^4251*50000000000000^3227 ≤ 21690502482201^3227*2500000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326198459 2500000000 21690502482201 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2001169687/10000000000 : ℝ)^4251 ≤ (12010622518027/100000000000000 : ℝ)^3227 := by
    have hnat : (2001169687 : ℕ)^4251*100000000000000^3227 ≤ 12010622518027^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001169687 10000000000 12010622518027 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42330809/78125000 : ℝ)^4251 ≤ (44608372494787/100000000000000 : ℝ)^3227 := by
    have hnat : (42330809 : ℕ)^4251*100000000000000^3227 ≤ 44608372494787^3227*78125000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42330809 78125000 44608372494787 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326198459/2500000000 : ℝ), (-2001169687/10000000000 : ℝ), (42330809/78125000 : ℝ)] ![(21690502482201/50000000000000 : ℝ), (12010622518027/100000000000000 : ℝ), (44608372494787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326198459/2500000000 : ℝ)|^4251 ≤ (21690502482201/50000000000000 : ℝ)^3227
        have hw : |(1326198459/2500000000 : ℝ)|=(1326198459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2001169687/10000000000 : ℝ)|^4251 ≤ (12010622518027/100000000000000 : ℝ)^3227
        have hw : |(-2001169687/10000000000 : ℝ)|=(2001169687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42330809/78125000 : ℝ)|^4251 ≤ (44608372494787/100000000000000 : ℝ)^3227
        have hw : |(42330809/78125000 : ℝ)|=(42330809/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s4_6 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304793407/10000000000 : ℝ)*x 0 + (1083668803/2000000000 : ℝ)*x 1 + (-1000584819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304793407/10000000000 : ℝ)^4251 ≤ (2711312521433/6250000000000 : ℝ)^3227 := by
    have hnat : (5304793407 : ℕ)^4251*6250000000000^3227 ≤ 2711312521433^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304793407 10000000000 2711312521433 6250000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083668803/2000000000 : ℝ)^4251 ≤ (22304188758083/50000000000000 : ℝ)^3227 := by
    have hnat : (1083668803 : ℕ)^4251*50000000000000^3227 ≤ 22304188758083^3227*2000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083668803 2000000000 22304188758083 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1000584819/5000000000 : ℝ)^4251 ≤ (6005311065309/50000000000000 : ℝ)^3227 := by
    have hnat : (1000584819 : ℕ)^4251*50000000000000^3227 ≤ 6005311065309^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000584819 5000000000 6005311065309 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304793407/10000000000 : ℝ), (1083668803/2000000000 : ℝ), (-1000584819/5000000000 : ℝ)] ![(2711312521433/6250000000000 : ℝ), (22304188758083/50000000000000 : ℝ), (6005311065309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304793407/10000000000 : ℝ)|^4251 ≤ (2711312521433/6250000000000 : ℝ)^3227
        have hw : |(5304793407/10000000000 : ℝ)|=(5304793407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083668803/2000000000 : ℝ)|^4251 ≤ (22304188758083/50000000000000 : ℝ)^3227
        have hw : |(1083668803/2000000000 : ℝ)|=(1083668803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1000584819/5000000000 : ℝ)|^4251 ≤ (6005311065309/50000000000000 : ℝ)^3227
        have hw : |(-1000584819/5000000000 : ℝ)|=(1000584819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s4_7 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (433990453/1000000000 : ℝ)*x 0 + (905328129/2000000000 : ℝ)*x 1 + (832121573/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433990453/1000000000 : ℝ)^4251 ≤ (1665000815413/5000000000000 : ℝ)^3227 := by
    have hnat : (433990453 : ℕ)^4251*5000000000000^3227 ≤ 1665000815413^3227*1000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433990453 1000000000 1665000815413 5000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (905328129/2000000000 : ℝ)^4251 ≤ (17600134126429/50000000000000 : ℝ)^3227 := by
    have hnat : (905328129 : ℕ)^4251*50000000000000^3227 ≤ 17600134126429^3227*2000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905328129 2000000000 17600134126429 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (832121573/2000000000 : ℝ)^4251 ≤ (15749857713139/50000000000000 : ℝ)^3227 := by
    have hnat : (832121573 : ℕ)^4251*50000000000000^3227 ≤ 15749857713139^3227*2000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832121573 2000000000 15749857713139 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(433990453/1000000000 : ℝ), (905328129/2000000000 : ℝ), (832121573/2000000000 : ℝ)] ![(1665000815413/5000000000000 : ℝ), (17600134126429/50000000000000 : ℝ), (15749857713139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(433990453/1000000000 : ℝ)|^4251 ≤ (1665000815413/5000000000000 : ℝ)^3227
        have hw : |(433990453/1000000000 : ℝ)|=(433990453/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(905328129/2000000000 : ℝ)|^4251 ≤ (17600134126429/50000000000000 : ℝ)^3227
        have hw : |(905328129/2000000000 : ℝ)|=(905328129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(832121573/2000000000 : ℝ)|^4251 ≤ (15749857713139/50000000000000 : ℝ)^3227
        have hw : |(832121573/2000000000 : ℝ)|=(832121573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1291_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76361297/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3767/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10653/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10951/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (59/400 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3767/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10653/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3767/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10653/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3767/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10653/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3767/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10653/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3767/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10653/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3767/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10653/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10653/100000 : ℝ) ^ (2125/512 : ℝ) ≤ (4598313825947307/50000000000000000000 : ℝ) := by
    have hpowers : (10653/100000 : ℝ)^2125 ≤ (4598313825947307/50000000000000000000 : ℝ)^512 := by
      have hnat : (10653 : ℕ)^2125*50000000000000000000^512 ≤ 4598313825947307^512*100000^2125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10653 100000 4598313825947307 50000000000000000000 2125 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10653/100000 : ℝ)) (X := (4598313825947307/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3767/25000 : ℝ) ^ (2125/512 : ℝ) ≤ (19390085324646221/50000000000000000000 : ℝ) := by
    have hpowers : (3767/25000 : ℝ)^2125 ≤ (19390085324646221/50000000000000000000 : ℝ)^512 := by
      have hnat : (3767 : ℕ)^2125*50000000000000000000^512 ≤ 19390085324646221^512*25000^2125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3767 25000 19390085324646221 50000000000000000000 2125 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3767/25000 : ℝ)) (X := (19390085324646221/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004598313825947307/25000000000000000000 : ℝ) ≤ (5000221569161931/5000000000000000 : ℝ) ^ (2125/512 : ℝ) := by
    have hpowers : (25004598313825947307/25000000000000000000 : ℝ)^512 ≤ (5000221569161931/5000000000000000 : ℝ)^2125 := by
      have hnat : (25004598313825947307 : ℕ)^512*5000000000000000^2125 ≤ 5000221569161931^2125*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004598313825947307 25000000000000000000 5000221569161931 5000000000000000 512 2125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000221569161931/5000000000000000 : ℝ)) (X := (25004598313825947307/25000000000000000000 : ℝ)) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252998549893824191/6250000000000000000 : ℝ) ≤ (10001155748197839/10000000000000000 : ℝ) ^ (2125/512 : ℝ) := by
    have hpowers : (6252998549893824191/6250000000000000000 : ℝ)^512 ≤ (10001155748197839/10000000000000000 : ℝ)^2125 := by
      have hnat : (6252998549893824191 : ℕ)^512*10000000000000000^2125 ≤ 10001155748197839^2125*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252998549893824191 6250000000000000000 10001155748197839 10000000000000000 512 2125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001155748197839/10000000000000000 : ℝ)) (X := (6252998549893824191/6250000000000000000 : ℝ)) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25019390085324646221/25000000000000000000 : ℝ) ≤ (1250233544758977/1250000000000000 : ℝ) ^ (2125/512 : ℝ) := by
    have hpowers : (25019390085324646221/25000000000000000000 : ℝ)^512 ≤ (1250233544758977/1250000000000000 : ℝ)^2125 := by
      have hnat : (25019390085324646221 : ℕ)^512*1250000000000000^2125 ≤ 1250233544758977^2125*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019390085324646221 25000000000000000000 1250233544758977 1250000000000000 512 2125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250233544758977/1250000000000000 : ℝ)) (X := (25019390085324646221/25000000000000000000 : ℝ)) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4598313825947307/50000000000000000000 : ℝ) ≤ ((86204635917431439/86230468750000000 : ℝ)+2*(712609873977/441500000000000 : ℝ)*(10653/100000 : ℝ))^(2125/512 : ℝ) := by
    rw [show (86204635917431439/86230468750000000 : ℝ)+2*(712609873977/441500000000000 : ℝ)*(10653/100000 : ℝ)=(5000221569161931/5000000000000000 : ℝ) by norm_num, show 1+2*(4598313825947307/50000000000000000000 : ℝ)=(25004598313825947307/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19390085324646221/50000000000000000000 : ℝ)+(4598313825947307/50000000000000000000 : ℝ) ≤ ((86204635917431439/86230468750000000 : ℝ)+(712609873977/441500000000000 : ℝ)*((3767/25000 : ℝ)+(10653/100000 : ℝ)))^(2125/512 : ℝ) := by
    rw [show (86204635917431439/86230468750000000 : ℝ)+(712609873977/441500000000000 : ℝ)*((3767/25000 : ℝ)+(10653/100000 : ℝ))=(10001155748197839/10000000000000000 : ℝ) by norm_num, show 1+(19390085324646221/50000000000000000000 : ℝ)+(4598313825947307/50000000000000000000 : ℝ)=(6252998549893824191/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19390085324646221/50000000000000000000 : ℝ) ≤ ((86204635917431439/86230468750000000 : ℝ)+2*(712609873977/441500000000000 : ℝ)*(3767/25000 : ℝ))^(2125/512 : ℝ) := by
    rw [show (86204635917431439/86230468750000000 : ℝ)+2*(712609873977/441500000000000 : ℝ)*(3767/25000 : ℝ)=(1250233544758977/1250000000000000 : ℝ) by norm_num, show 1+2*(19390085324646221/50000000000000000000 : ℝ)=(25019390085324646221/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (86204635917431439/86230468750000000 : ℝ)*(X 1 0+X 2 0)+(712609873977/441500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2125/512 : ℝ)) (lo := (10653/100000 : ℝ)) (hi := (3767/25000 : ℝ)) (c := (86204635917431439/86230468750000000 : ℝ)) (alpha := (712609873977/441500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (86204635917431439/86230468750000000 : ℝ)*(X 0 1+X 2 1)+(712609873977/441500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2125/512 : ℝ)) (lo := (10653/100000 : ℝ)) (hi := (3767/25000 : ℝ)) (c := (86204635917431439/86230468750000000 : ℝ)) (alpha := (712609873977/441500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (86204635917431439/86230468750000000 : ℝ)*(X 0 2+X 1 2)+(712609873977/441500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2125/512 : ℝ)) (lo := (10653/100000 : ℝ)) (hi := (3767/25000 : ℝ)) (c := (86204635917431439/86230468750000000 : ℝ)) (alpha := (712609873977/441500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-208842753/1000000000 : ℝ)*X 0 0+(5419013719/10000000000 : ℝ)*X 0 1+(5239512049/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350744981/10000000000 : ℝ)*X 1 0+(-545000439/2500000000 : ℝ)*X 1 1+(2619755959/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350744799/10000000000 : ℝ)*X 2 0+(523951233/1000000000 : ℝ)*X 2 1+(-1090000727/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4339874931/10000000000 : ℝ)*X 0 0+(519903993/1250000000 : ℝ)*X 0 1+(4528009309/10000000000 : ℝ)*X 0 2+(4339874931/10000000000 : ℝ)*X 1 0+(519903993/1250000000 : ℝ)*X 1 1+(4528009309/10000000000 : ℝ)*X 1 2+(4339874931/10000000000 : ℝ)*X 2 0+(519903993/1250000000 : ℝ)*X 2 1+(4528009309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2088442063/10000000000 : ℝ)*X 0 0+(5240178373/10000000000 : ℝ)*X 0 1+(1083668743/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326198459/2500000000 : ℝ)*X 1 0+(-2001169687/10000000000 : ℝ)*X 1 1+(42330809/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304793407/10000000000 : ℝ)*X 2 0+(1083668803/2000000000 : ℝ)*X 2 1+(-1000584819/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((433990453/1000000000 : ℝ)*X 0 0+(905328129/2000000000 : ℝ)*X 0 1+(832121573/2000000000 : ℝ)*X 0 2+(433990453/1000000000 : ℝ)*X 1 0+(905328129/2000000000 : ℝ)*X 1 1+(832121573/2000000000 : ℝ)*X 1 2+(433990453/1000000000 : ℝ)*X 2 0+(905328129/2000000000 : ℝ)*X 2 1+(832121573/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37473744598039636901791113/3449218750000000000000000000000 : ℝ) := by norm_num
    linear_combination (42829533/2500000000000 : ℝ)*(base19) + (159187123/12500000000000 : ℝ)*(base23) + (133870873/100000000000000 : ℝ)*(lower2) + (46134631/50000000000000 : ℝ)*(upper3) + (218100921/100000000000000 : ℝ)*(upper5) + (828274018952541/20000000000000 : ℝ)*(major0) + (828274018952541/20000000000000 : ℝ)*(major1) + (828274018952541/20000000000000 : ℝ)*(major2) + (5571009020087861/100000000000000 : ℝ)*(sp0) + (5571043671158113/100000000000000 : ℝ)*(sp1) + (5571044110842449/100000000000000 : ℝ)*(sp2) + (542335895449549/20000000000000 : ℝ)*(sp3) + (9091062893/25000000000000 : ℝ)*(sp4) + (7482895527/50000000000000 : ℝ)*(sp7) + (1355847221519399/50000000000000 : ℝ)*(f.failure) + (5571045384339433/100000000000000 : ℝ)*(f.sum) + (1259754271389/2207500000000000000000000000 : ℝ)*base66 + (127504443334280859/27593750000000000000000000000000 : ℝ)*base67 + (9736702496875391/27593750000000000000000000000000 : ℝ)*base70 + (125446429336625391/27593750000000000000000000000000 : ℝ)*base72 + (957220320473/4415000000000000000000000000 : ℝ)*base74 + (8125185381405859/27593750000000000000000000000000 : ℝ)*base75 + (12394612022062891/27593750000000000000000000000000 : ℝ)*base78 + (561039054811500391/27593750000000000000000000000000 : ℝ)*base80 + (7911852917039/2207500000000000000000000000 : ℝ)*base82 + (6699497/2500000000000000000000 : ℝ)*base90 + (6699497/2500000000000000000000 : ℝ)*base92 + (6699497/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (90946183800039191293019037/13796875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1735156727/100000000000000 : ℝ)*(base19) + (173931431/12500000000000 : ℝ)*(base23) + (7946453/4000000000000 : ℝ)*(upper3) + (33991413/100000000000000 : ℝ)*(lower4) + (42138709/100000000000000 : ℝ)*(upper5) + (417237561580649/10000000000000 : ℝ)*(major0) + (417237561580649/10000000000000 : ℝ)*(major1) + (417237561580649/10000000000000 : ℝ)*(major2) + (5513653/19531250000 : ℝ)*(sp1) + (33554321787/100000000000000 : ℝ)*(sp2) + (5612754712893193/100000000000000 : ℝ)*(sp4) + (5612724747833107/100000000000000 : ℝ)*(sp5) + (2806359883559979/50000000000000 : ℝ)*(sp6) + (682999074748313/25000000000000 : ℝ)*(sp7) + (682999074748313/25000000000000 : ℝ)*(f.failure) + (5612754712893193/100000000000000 : ℝ)*(f.sum) + (20960744561731/4415000000000000000000000000 : ℝ)*base65 + (26496615859605587/6898437500000000000000000000000 : ℝ)*base68 + (8802557570163589/862304687500000000000000000000 : ℝ)*base70 + (84863023487523201/13796875000000000000000000000000 : ℝ)*base71 + (12998091311681/4415000000000000000000000000 : ℝ)*base73 + (116503075634601799/13796875000000000000000000000000 : ℝ)*base76 + (315432412655303/1724609375000000000000000000000 : ℝ)*base78 + (77454678443476799/13796875000000000000000000000000 : ℝ)*base80 + (387161595403/551875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (4241961/1250000000000000000000 : ℝ)*base89 + (4241961/1250000000000000000000 : ℝ)*base91 + (4241961/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1291_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76361297/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3767/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10653/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10951/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (59/400 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1291_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1291_s5_0 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-522197533/2500000000 : ℝ)*x 0 + (5415949131/10000000000 : ℝ)*x 1 + (655292279/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522197533/2500000000 : ℝ)^4251 ≤ (6354071093847/50000000000000 : ℝ)^3227 := by
    have hnat : (522197533 : ℕ)^4251*50000000000000^3227 ≤ 6354071093847^3227*2500000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522197533 2500000000 6354071093847 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415949131/10000000000 : ℝ)^4251 ≤ (44582406077113/100000000000000 : ℝ)^3227 := by
    have hnat : (5415949131 : ℕ)^4251*100000000000000^3227 ≤ 44582406077113^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415949131 10000000000 44582406077113 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655292279/1250000000 : ℝ)^4251 ≤ (8541890345399/20000000000000 : ℝ)^3227 := by
    have hnat : (655292279 : ℕ)^4251*20000000000000^3227 ≤ 8541890345399^3227*1250000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655292279 1250000000 8541890345399 20000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-522197533/2500000000 : ℝ), (5415949131/10000000000 : ℝ), (655292279/1250000000 : ℝ)] ![(6354071093847/50000000000000 : ℝ), (44582406077113/100000000000000 : ℝ), (8541890345399/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-522197533/2500000000 : ℝ)|^4251 ≤ (6354071093847/50000000000000 : ℝ)^3227
        have hw : |(-522197533/2500000000 : ℝ)|=(522197533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415949131/10000000000 : ℝ)|^4251 ≤ (44582406077113/100000000000000 : ℝ)^3227
        have hw : |(5415949131/10000000000 : ℝ)|=(5415949131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655292279/1250000000 : ℝ)|^4251 ≤ (8541890345399/20000000000000 : ℝ)^3227
        have hw : |(655292279/1250000000 : ℝ)|=(655292279/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s5_1 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069993573/2000000000 : ℝ)*x 0 + (-2177301107/10000000000 : ℝ)*x 1 + (5242338229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069993573/2000000000 : ℝ)^4251 ≤ (8773661196149/20000000000000 : ℝ)^3227 := by
    have hnat : (1069993573 : ℕ)^4251*20000000000000^3227 ≤ 8773661196149^3227*2000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069993573 2000000000 8773661196149 20000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2177301107/10000000000 : ℝ)^4251 ≤ (13422242299819/100000000000000 : ℝ)^3227 := by
    have hnat : (2177301107 : ℕ)^4251*100000000000000^3227 ≤ 13422242299819^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177301107 10000000000 13422242299819 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242338229/10000000000 : ℝ)^4251 ≤ (21354725847399/50000000000000 : ℝ)^3227 := by
    have hnat : (5242338229 : ℕ)^4251*50000000000000^3227 ≤ 21354725847399^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242338229 10000000000 21354725847399 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069993573/2000000000 : ℝ), (-2177301107/10000000000 : ℝ), (5242338229/10000000000 : ℝ)] ![(8773661196149/20000000000000 : ℝ), (13422242299819/100000000000000 : ℝ), (21354725847399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069993573/2000000000 : ℝ)|^4251 ≤ (8773661196149/20000000000000 : ℝ)^3227
        have hw : |(1069993573/2000000000 : ℝ)|=(1069993573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2177301107/10000000000 : ℝ)|^4251 ≤ (13422242299819/100000000000000 : ℝ)^3227
        have hw : |(-2177301107/10000000000 : ℝ)|=(2177301107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242338229/10000000000 : ℝ)|^4251 ≤ (21354725847399/50000000000000 : ℝ)^3227
        have hw : |(5242338229/10000000000 : ℝ)|=(5242338229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s5_2 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534996787/1000000000 : ℝ)*x 0 + (327646139/625000000 : ℝ)*x 1 + (-2177301109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534996787/1000000000 : ℝ)^4251 ≤ (43868306034753/100000000000000 : ℝ)^3227 := by
    have hnat : (534996787 : ℕ)^4251*100000000000000^3227 ≤ 43868306034753^3227*1000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534996787 1000000000 43868306034753 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327646139/625000000 : ℝ)^4251 ≤ (42709451641137/100000000000000 : ℝ)^3227 := by
    have hnat : (327646139 : ℕ)^4251*100000000000000^3227 ≤ 42709451641137^3227*625000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327646139 625000000 42709451641137 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2177301109/10000000000 : ℝ)^4251 ≤ (13422242316061/100000000000000 : ℝ)^3227 := by
    have hnat : (2177301109 : ℕ)^4251*100000000000000^3227 ≤ 13422242316061^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177301109 10000000000 13422242316061 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534996787/1000000000 : ℝ), (327646139/625000000 : ℝ), (-2177301109/10000000000 : ℝ)] ![(43868306034753/100000000000000 : ℝ), (42709451641137/100000000000000 : ℝ), (13422242316061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534996787/1000000000 : ℝ)|^4251 ≤ (43868306034753/100000000000000 : ℝ)^3227
        have hw : |(534996787/1000000000 : ℝ)|=(534996787/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327646139/625000000 : ℝ)|^4251 ≤ (42709451641137/100000000000000 : ℝ)^3227
        have hw : |(327646139/625000000 : ℝ)|=(327646139/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2177301109/10000000000 : ℝ)|^4251 ≤ (13422242316061/100000000000000 : ℝ)^3227
        have hw : |(-2177301109/10000000000 : ℝ)|=(2177301109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s5_3 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4340089613/10000000000 : ℝ)*x 0 + (1041313971/2500000000 : ℝ)*x 1 + (904386227/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4340089613/10000000000 : ℝ)^4251 ≤ (16650943550937/50000000000000 : ℝ)^3227 := by
    have hnat : (4340089613 : ℕ)^4251*50000000000000^3227 ≤ 16650943550937^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4340089613 10000000000 16650943550937 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041313971/2500000000 : ℝ)^4251 ≤ (15773040029851/50000000000000 : ℝ)^3227 := by
    have hnat : (1041313971 : ℕ)^4251*50000000000000^3227 ≤ 15773040029851^3227*2500000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041313971 2500000000 15773040029851 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (904386227/2000000000 : ℝ)^4251 ≤ (7030406565667/20000000000000 : ℝ)^3227 := by
    have hnat : (904386227 : ℕ)^4251*20000000000000^3227 ≤ 7030406565667^3227*2000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904386227 2000000000 7030406565667 20000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4340089613/10000000000 : ℝ), (1041313971/2500000000 : ℝ), (904386227/2000000000 : ℝ)] ![(16650943550937/50000000000000 : ℝ), (15773040029851/50000000000000 : ℝ), (7030406565667/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4340089613/10000000000 : ℝ)|^4251 ≤ (16650943550937/50000000000000 : ℝ)^3227
        have hw : |(4340089613/10000000000 : ℝ)|=(4340089613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1041313971/2500000000 : ℝ)|^4251 ≤ (15773040029851/50000000000000 : ℝ)^3227
        have hw : |(1041313971/2500000000 : ℝ)|=(1041313971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(904386227/2000000000 : ℝ)|^4251 ≤ (7030406565667/20000000000000 : ℝ)^3227
        have hw : |(904386227/2000000000 : ℝ)|=(904386227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s5_4 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-16318779/78125000 : ℝ)*x 0 + (5242961503/10000000000 : ℝ)*x 1 + (5415322211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16318779/78125000 : ℝ)^4251 ≤ (12708251025459/100000000000000 : ℝ)^3227 := by
    have hnat : (16318779 : ℕ)^4251*100000000000000^3227 ≤ 12708251025459^3227*78125000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16318779 78125000 12708251025459 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242961503/10000000000 : ℝ)^4251 ≤ (5339517619781/12500000000000 : ℝ)^3227 := by
    have hnat : (5242961503 : ℕ)^4251*12500000000000^3227 ≤ 5339517619781^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242961503 10000000000 5339517619781 12500000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415322211/10000000000 : ℝ)^4251 ≤ (2785975500853/6250000000000 : ℝ)^3227 := by
    have hnat : (5415322211 : ℕ)^4251*6250000000000^3227 ≤ 2785975500853^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415322211 10000000000 2785975500853 6250000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16318779/78125000 : ℝ), (5242961503/10000000000 : ℝ), (5415322211/10000000000 : ℝ)] ![(12708251025459/100000000000000 : ℝ), (5339517619781/12500000000000 : ℝ), (2785975500853/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16318779/78125000 : ℝ)|^4251 ≤ (12708251025459/100000000000000 : ℝ)^3227
        have hw : |(-16318779/78125000 : ℝ)|=(16318779/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242961503/10000000000 : ℝ)|^4251 ≤ (5339517619781/12500000000000 : ℝ)^3227
        have hw : |(5242961503/10000000000 : ℝ)|=(5242961503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415322211/10000000000 : ℝ)|^4251 ≤ (2785975500853/6250000000000 : ℝ)^3227
        have hw : |(5415322211/10000000000 : ℝ)|=(5415322211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s5_5 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663190549/1250000000 : ℝ)*x 0 + (-125269799/625000000 : ℝ)*x 1 + (5415322779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663190549/1250000000 : ℝ)^4251 ≤ (43388875172919/100000000000000 : ℝ)^3227 := by
    have hnat : (663190549 : ℕ)^4251*100000000000000^3227 ≤ 43388875172919^3227*1250000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663190549 1250000000 43388875172919 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125269799/625000000 : ℝ)^4251 ≤ (6017755321573/50000000000000 : ℝ)^3227 := by
    have hnat : (125269799 : ℕ)^4251*50000000000000^3227 ≤ 6017755321573^3227*625000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125269799 625000000 6017755321573 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415322779/10000000000 : ℝ)^4251 ≤ (22287807086347/50000000000000 : ℝ)^3227 := by
    have hnat : (5415322779 : ℕ)^4251*50000000000000^3227 ≤ 22287807086347^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415322779 10000000000 22287807086347 50000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663190549/1250000000 : ℝ), (-125269799/625000000 : ℝ), (5415322779/10000000000 : ℝ)] ![(43388875172919/100000000000000 : ℝ), (6017755321573/50000000000000 : ℝ), (22287807086347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663190549/1250000000 : ℝ)|^4251 ≤ (43388875172919/100000000000000 : ℝ)^3227
        have hw : |(663190549/1250000000 : ℝ)|=(663190549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-125269799/625000000 : ℝ)|^4251 ≤ (6017755321573/50000000000000 : ℝ)^3227
        have hw : |(-125269799/625000000 : ℝ)|=(125269799/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415322779/10000000000 : ℝ)|^4251 ≤ (22287807086347/50000000000000 : ℝ)^3227
        have hw : |(5415322779/10000000000 : ℝ)|=(5415322779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s5_6 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530552429/1000000000 : ℝ)*x 0 + (1083064567/2000000000 : ℝ)*x 1 + (-400863369/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530552429/1000000000 : ℝ)^4251 ≤ (43388874074059/100000000000000 : ℝ)^3227 := by
    have hnat : (530552429 : ℕ)^4251*100000000000000^3227 ≤ 43388874074059^3227*1000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530552429 1000000000 43388874074059 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083064567/2000000000 : ℝ)^4251 ≤ (11143903694981/25000000000000 : ℝ)^3227 := by
    have hnat : (1083064567 : ℕ)^4251*25000000000000^3227 ≤ 11143903694981^3227*2000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083064567 2000000000 11143903694981 25000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (400863369/2000000000 : ℝ)^4251 ≤ (12035511125671/100000000000000 : ℝ)^3227 := by
    have hnat : (400863369 : ℕ)^4251*100000000000000^3227 ≤ 12035511125671^3227*2000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400863369 2000000000 12035511125671 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530552429/1000000000 : ℝ), (1083064567/2000000000 : ℝ), (-400863369/2000000000 : ℝ)] ![(43388874074059/100000000000000 : ℝ), (11143903694981/25000000000000 : ℝ), (12035511125671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530552429/1000000000 : ℝ)|^4251 ≤ (43388874074059/100000000000000 : ℝ)^3227
        have hw : |(530552429/1000000000 : ℝ)|=(530552429/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083064567/2000000000 : ℝ)|^4251 ≤ (11143903694981/25000000000000 : ℝ)^3227
        have hw : |(1083064567/2000000000 : ℝ)|=(1083064567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-400863369/2000000000 : ℝ)|^4251 ≤ (12035511125671/100000000000000 : ℝ)^3227
        have hw : |(-400863369/2000000000 : ℝ)|=(400863369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1291_s5_7 (p : ℝ) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2170058227/5000000000 : ℝ)*x 0 + (4520650569/10000000000 : ℝ)*x 1 + (4166542959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170058227/5000000000 : ℝ)^4251 ≤ (4162769801141/12500000000000 : ℝ)^3227 := by
    have hnat : (2170058227 : ℕ)^4251*12500000000000^3227 ≤ 4162769801141^3227*5000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170058227 5000000000 4162769801141 12500000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4520650569/10000000000 : ℝ)^4251 ≤ (35138919857591/100000000000000 : ℝ)^3227 := by
    have hnat : (4520650569 : ℕ)^4251*100000000000000^3227 ≤ 35138919857591^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520650569 10000000000 35138919857591 100000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4166542959/10000000000 : ℝ)^4251 ≤ (1262356868589/4000000000000 : ℝ)^3227 := by
    have hnat : (4166542959 : ℕ)^4251*4000000000000^3227 ≤ 1262356868589^3227*10000000000^4251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166542959 10000000000 1262356868589 4000000000000 4251 3227 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4251/1024 : ℝ)) 4251 3227 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2170058227/5000000000 : ℝ), (4520650569/10000000000 : ℝ), (4166542959/10000000000 : ℝ)] ![(4162769801141/12500000000000 : ℝ), (35138919857591/100000000000000 : ℝ), (1262356868589/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2170058227/5000000000 : ℝ)|^4251 ≤ (4162769801141/12500000000000 : ℝ)^3227
        have hw : |(2170058227/5000000000 : ℝ)|=(2170058227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4520650569/10000000000 : ℝ)|^4251 ≤ (35138919857591/100000000000000 : ℝ)^3227
        have hw : |(4520650569/10000000000 : ℝ)|=(4520650569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4166542959/10000000000 : ℝ)|^4251 ≤ (1262356868589/4000000000000 : ℝ)^3227
        have hw : |(4166542959/10000000000 : ℝ)|=(4166542959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1291_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76361297/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10951/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2753/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7343/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10951/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10951/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10951/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10951/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10951/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10951/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10951/100000 : ℝ) ^ (2125/512 : ℝ) ≤ (2578089428231771/25000000000000000000 : ℝ) := by
    have hpowers : (10951/100000 : ℝ)^2125 ≤ (2578089428231771/25000000000000000000 : ℝ)^512 := by
      have hnat : (10951 : ℕ)^2125*25000000000000000000^512 ≤ 2578089428231771^512*100000^2125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10951 100000 2578089428231771 25000000000000000000 2125 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10951/100000 : ℝ)) (X := (2578089428231771/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have hpowhi : (59/400 : ℝ) ^ (2125/512 : ℝ) ≤ (35494592427978367/100000000000000000000 : ℝ) := by
    have hpowers : (59/400 : ℝ)^2125 ≤ (35494592427978367/100000000000000000000 : ℝ)^512 := by
      have hnat : (59 : ℕ)^2125*100000000000000000000^512 ≤ 35494592427978367^512*400^2125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59 400 35494592427978367 100000000000000000000 2125 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59/400 : ℝ)) (X := (35494592427978367/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502578089428231771/12500000000000000000 : ℝ) ≤ (10000496895426153/10000000000000000 : ℝ) ^ (2125/512 : ℝ) := by
    have hpowers : (12502578089428231771/12500000000000000000 : ℝ)^512 ≤ (10000496895426153/10000000000000000 : ℝ)^2125 := by
      have hnat : (12502578089428231771 : ℕ)^512*10000000000000000^2125 ≤ 10000496895426153^2125*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502578089428231771 12500000000000000000 10000496895426153 10000000000000000 512 2125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000496895426153/10000000000000000 : ℝ)) (X := (12502578089428231771/12500000000000000000 : ℝ)) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045806950140905451/100000000000000000000 : ℝ) ≤ (10001103486221903/10000000000000000 : ℝ) ^ (2125/512 : ℝ) := by
    have hpowers : (100045806950140905451/100000000000000000000 : ℝ)^512 ≤ (10001103486221903/10000000000000000 : ℝ)^2125 := by
      have hnat : (100045806950140905451 : ℕ)^512*10000000000000000^2125 ≤ 10001103486221903^2125*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045806950140905451 100000000000000000000 10001103486221903 10000000000000000 512 2125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001103486221903/10000000000000000 : ℝ)) (X := (100045806950140905451/100000000000000000000 : ℝ)) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035494592427978367/50000000000000000000 : ℝ) ≤ (10001710077017653/10000000000000000 : ℝ) ^ (2125/512 : ℝ) := by
    have hpowers : (50035494592427978367/50000000000000000000 : ℝ)^512 ≤ (10001710077017653/10000000000000000 : ℝ)^2125 := by
      have hnat : (50035494592427978367 : ℕ)^512*10000000000000000^2125 ≤ 10001710077017653^2125*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035494592427978367 50000000000000000000 10001710077017653 10000000000000000 512 2125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001710077017653/10000000000000000 : ℝ)) (X := (50035494592427978367/50000000000000000000 : ℝ)) (by norm_num) 2125 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2578089428231771/25000000000000000000 : ℝ) ≤ ((37978602154115438747/37990000000000000000 : ℝ)+2*(2426363183/1519600000000 : ℝ)*(10951/100000 : ℝ))^(2125/512 : ℝ) := by
    rw [show (37978602154115438747/37990000000000000000 : ℝ)+2*(2426363183/1519600000000 : ℝ)*(10951/100000 : ℝ)=(10000496895426153/10000000000000000 : ℝ) by norm_num, show 1+2*(2578089428231771/25000000000000000000 : ℝ)=(12502578089428231771/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35494592427978367/100000000000000000000 : ℝ)+(2578089428231771/25000000000000000000 : ℝ) ≤ ((37978602154115438747/37990000000000000000 : ℝ)+(2426363183/1519600000000 : ℝ)*((59/400 : ℝ)+(10951/100000 : ℝ)))^(2125/512 : ℝ) := by
    rw [show (37978602154115438747/37990000000000000000 : ℝ)+(2426363183/1519600000000 : ℝ)*((59/400 : ℝ)+(10951/100000 : ℝ))=(10001103486221903/10000000000000000 : ℝ) by norm_num, show 1+(35494592427978367/100000000000000000000 : ℝ)+(2578089428231771/25000000000000000000 : ℝ)=(100045806950140905451/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35494592427978367/100000000000000000000 : ℝ) ≤ ((37978602154115438747/37990000000000000000 : ℝ)+2*(2426363183/1519600000000 : ℝ)*(59/400 : ℝ))^(2125/512 : ℝ) := by
    rw [show (37978602154115438747/37990000000000000000 : ℝ)+2*(2426363183/1519600000000 : ℝ)*(59/400 : ℝ)=(10001710077017653/10000000000000000 : ℝ) by norm_num, show 1+2*(35494592427978367/100000000000000000000 : ℝ)=(50035494592427978367/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37978602154115438747/37990000000000000000 : ℝ)*(X 1 0+X 2 0)+(2426363183/1519600000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2125/512 : ℝ)) (lo := (10951/100000 : ℝ)) (hi := (59/400 : ℝ)) (c := (37978602154115438747/37990000000000000000 : ℝ)) (alpha := (2426363183/1519600000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37978602154115438747/37990000000000000000 : ℝ)*(X 0 1+X 2 1)+(2426363183/1519600000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2125/512 : ℝ)) (lo := (10951/100000 : ℝ)) (hi := (59/400 : ℝ)) (c := (37978602154115438747/37990000000000000000 : ℝ)) (alpha := (2426363183/1519600000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37978602154115438747/37990000000000000000 : ℝ)*(X 0 2+X 1 2)+(2426363183/1519600000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2125/512 : ℝ)) (lo := (10951/100000 : ℝ)) (hi := (59/400 : ℝ)) (c := (37978602154115438747/37990000000000000000 : ℝ)) (alpha := (2426363183/1519600000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-522197533/2500000000 : ℝ)*X 0 0+(5415949131/10000000000 : ℝ)*X 0 1+(655292279/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069993573/2000000000 : ℝ)*X 1 0+(-2177301107/10000000000 : ℝ)*X 1 1+(5242338229/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534996787/1000000000 : ℝ)*X 2 0+(327646139/625000000 : ℝ)*X 2 1+(-2177301109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4340089613/10000000000 : ℝ)*X 0 0+(1041313971/2500000000 : ℝ)*X 0 1+(904386227/2000000000 : ℝ)*X 0 2+(4340089613/10000000000 : ℝ)*X 1 0+(1041313971/2500000000 : ℝ)*X 1 1+(904386227/2000000000 : ℝ)*X 1 2+(4340089613/10000000000 : ℝ)*X 2 0+(1041313971/2500000000 : ℝ)*X 2 1+(904386227/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-16318779/78125000 : ℝ)*X 0 0+(5242961503/10000000000 : ℝ)*X 0 1+(5415322211/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663190549/1250000000 : ℝ)*X 1 0+(-125269799/625000000 : ℝ)*X 1 1+(5415322779/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530552429/1000000000 : ℝ)*X 2 0+(1083064567/2000000000 : ℝ)*X 2 1+(-400863369/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2170058227/5000000000 : ℝ)*X 0 0+(4520650569/10000000000 : ℝ)*X 0 1+(4166542959/10000000000 : ℝ)*X 0 2+(2170058227/5000000000 : ℝ)*X 1 0+(4520650569/10000000000 : ℝ)*X 1 1+(4166542959/10000000000 : ℝ)*X 1 2+(2170058227/5000000000 : ℝ)*X 2 0+(4520650569/10000000000 : ℝ)*X 2 1+(4166542959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1291_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (791254277585759220510657921/237437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (82893019/12500000000000 : ℝ)*(base19) + (621400033/100000000000000 : ℝ)*(base23) + (5042597/20000000000000 : ℝ)*(lower2) + (22495479/25000000000000 : ℝ)*(upper3) + (54532837/100000000000000 : ℝ)*(upper5) + (1070464695331019/25000000000000 : ℝ)*(major0) + (1070464695331019/25000000000000 : ℝ)*(major1) + (1070464695331019/25000000000000 : ℝ)*(major2) + (5760020613332697/100000000000000 : ℝ)*(sp0) + (5760032887319067/100000000000000 : ℝ)*(sp1) + (1152006585812637/20000000000000 : ℝ)*(sp2) + (350459623936693/12500000000000 : ℝ)*(sp3) + (12937130521/100000000000000 : ℝ)*(sp4) + (172740223/2500000000000 : ℝ)*(sp7) + (2803683901102463/100000000000000 : ℝ)*(f.failure) + (2880016775231609/50000000000000 : ℝ)*(f.sum) + (3132388040301/949750000000000000000000000 : ℝ)*base66 + (4966188006754906807/949750000000000000000000000000000 : ℝ)*base68 + (13266730115347343193/949750000000000000000000000000000 : ℝ)*base69 + (5797753888385343193/949750000000000000000000000000000 : ℝ)*base71 + (23812175709993/3799000000000000000000000000 : ℝ)*base74 + (2953738002424343193/949750000000000000000000000000000 : ℝ)*base75 + (1525698614134093193/949750000000000000000000000000000 : ℝ)*base77 + (7365067705262593193/949750000000000000000000000000000 : ℝ)*base79 + (40227499809/759800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (4574511/5000000000000000000000 : ℝ)*base89 + (4574511/5000000000000000000000 : ℝ)*base91 + (4574511/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26018625991666803811917/3799000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1338279039/100000000000000 : ℝ)*(base19) + (898050841/50000000000000 : ℝ)*(base23) + (249198403/100000000000000 : ℝ)*(upper2) + (105022033/25000000000000 : ℝ)*(upper3) + (122286353/50000000000000 : ℝ)*(upper5) + (2156443825358203/50000000000000 : ℝ)*(major0) + (2156443825358203/50000000000000 : ℝ)*(major1) + (2156443825358203/50000000000000 : ℝ)*(major2) + (30234513793/100000000000000 : ℝ)*(sp1) + (42132356051/100000000000000 : ℝ)*(sp2) + (290088701400237/5000000000000 : ℝ)*(sp4) + (5801742455211907/100000000000000 : ℝ)*(sp5) + (5801730099547007/100000000000000 : ℝ)*(sp6) + (1412000522567213/50000000000000 : ℝ)*(sp7) + (1412000522567213/50000000000000 : ℝ)*(f.failure) + (290088701400237/5000000000000 : ℝ)*(f.sum) + (425809320361/237437500000000000000000000 : ℝ)*base66 + (6683953993212491641/1899500000000000000000000000000000 : ℝ)*base67 + (17761042133757508359/1899500000000000000000000000000000 : ℝ)*base70 + (14811035471748008359/1899500000000000000000000000000000 : ℝ)*base72 + (964584931671/759800000000000000000000000 : ℝ)*base73 + (10758920818247491641/1899500000000000000000000000000000 : ℝ)*base75 + (28713065510692508359/1899500000000000000000000000000000 : ℝ)*base78 + (29902541537136991641/1899500000000000000000000000000000 : ℝ)*base79 + (186978785001/94975000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (4355261/2500000000000000000000 : ℝ)*base89 + (4355261/2500000000000000000000 : ℝ)*base91 + (4355261/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1291_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76361297/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10951/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2753/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1291_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1291_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76361297/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8161/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9497/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2753/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1291_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1291_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1291_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2125/512 : ℝ) ≤ p) (hpb : p ≤ (4251/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76361297/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8161/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9497/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2753/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1291_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
