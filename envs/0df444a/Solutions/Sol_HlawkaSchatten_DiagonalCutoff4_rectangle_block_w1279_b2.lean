-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1279_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:22:25.618707+00:00
-- url     : https://prove2.me/submissions/5bd0d07d-b6f2-4d6f-82a8-0d78fd9ca228

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
theorem support_rectangle_w1279_s6_0 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2099666149/10000000000 : ℝ)*x 0 + (5416004879/10000000000 : ℝ)*x 1 + (2621207081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099666149/10000000000 : ℝ)^4239 ≤ (12771748450663/100000000000000 : ℝ)^3215 := by
    have hnat : (2099666149 : ℕ)^4239*100000000000000^3215 ≤ 12771748450663^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099666149 10000000000 12771748450663 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416004879/10000000000 : ℝ)^4239 ≤ (22275320624131/50000000000000 : ℝ)^3215 := by
    have hnat : (5416004879 : ℕ)^4239*50000000000000^3215 ≤ 22275320624131^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416004879 10000000000 22275320624131 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621207081/5000000000 : ℝ)^4239 ≤ (21338805144747/50000000000000 : ℝ)^3215 := by
    have hnat : (2621207081 : ℕ)^4239*50000000000000^3215 ≤ 21338805144747^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621207081 5000000000 21338805144747 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2099666149/10000000000 : ℝ), (5416004879/10000000000 : ℝ), (2621207081/5000000000 : ℝ)] ![(12771748450663/100000000000000 : ℝ), (22275320624131/50000000000000 : ℝ), (21338805144747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2099666149/10000000000 : ℝ)|^4239 ≤ (12771748450663/100000000000000 : ℝ)^3215
        have hw : |(-2099666149/10000000000 : ℝ)|=(2099666149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416004879/10000000000 : ℝ)|^4239 ≤ (22275320624131/50000000000000 : ℝ)^3215
        have hw : |(5416004879/10000000000 : ℝ)|=(5416004879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621207081/5000000000 : ℝ)|^4239 ≤ (21338805144747/50000000000000 : ℝ)^3215
        have hw : |(2621207081/5000000000 : ℝ)|=(2621207081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s6_1 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349996909/10000000000 : ℝ)*x 0 + (-13676043/62500000 : ℝ)*x 1 + (2621207081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349996909/10000000000 : ℝ)^4239 ≤ (43836132367717/100000000000000 : ℝ)^3215 := by
    have hnat : (5349996909 : ℕ)^4239*100000000000000^3215 ≤ 43836132367717^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349996909 10000000000 43836132367717 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13676043/62500000 : ℝ)^4239 ≤ (674312866427/5000000000000 : ℝ)^3215 := by
    have hnat : (13676043 : ℕ)^4239*5000000000000^3215 ≤ 674312866427^3215*62500000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13676043 62500000 674312866427 5000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621207081/5000000000 : ℝ)^4239 ≤ (21338805144747/50000000000000 : ℝ)^3215 := by
    have hnat : (2621207081 : ℕ)^4239*50000000000000^3215 ≤ 21338805144747^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621207081 5000000000 21338805144747 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349996909/10000000000 : ℝ), (-13676043/62500000 : ℝ), (2621207081/5000000000 : ℝ)] ![(43836132367717/100000000000000 : ℝ), (674312866427/5000000000000 : ℝ), (21338805144747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349996909/10000000000 : ℝ)|^4239 ≤ (43836132367717/100000000000000 : ℝ)^3215
        have hw : |(5349996909/10000000000 : ℝ)|=(5349996909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13676043/62500000 : ℝ)|^4239 ≤ (674312866427/5000000000000 : ℝ)^3215
        have hw : |(-13676043/62500000 : ℝ)|=(13676043/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621207081/5000000000 : ℝ)|^4239 ≤ (21338805144747/50000000000000 : ℝ)^3215
        have hw : |(2621207081/5000000000 : ℝ)|=(2621207081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s6_2 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349996909/10000000000 : ℝ)*x 0 + (2621207081/5000000000 : ℝ)*x 1 + (-13676043/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349996909/10000000000 : ℝ)^4239 ≤ (43836132367717/100000000000000 : ℝ)^3215 := by
    have hnat : (5349996909 : ℕ)^4239*100000000000000^3215 ≤ 43836132367717^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349996909 10000000000 43836132367717 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621207081/5000000000 : ℝ)^4239 ≤ (21338805144747/50000000000000 : ℝ)^3215 := by
    have hnat : (2621207081 : ℕ)^4239*50000000000000^3215 ≤ 21338805144747^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621207081 5000000000 21338805144747 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13676043/62500000 : ℝ)^4239 ≤ (674312866427/5000000000000 : ℝ)^3215 := by
    have hnat : (13676043 : ℕ)^4239*5000000000000^3215 ≤ 674312866427^3215*62500000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13676043 62500000 674312866427 5000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349996909/10000000000 : ℝ), (2621207081/5000000000 : ℝ), (-13676043/62500000 : ℝ)] ![(43836132367717/100000000000000 : ℝ), (21338805144747/50000000000000 : ℝ), (674312866427/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349996909/10000000000 : ℝ)|^4239 ≤ (43836132367717/100000000000000 : ℝ)^3215
        have hw : |(5349996909/10000000000 : ℝ)|=(5349996909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621207081/5000000000 : ℝ)|^4239 ≤ (21338805144747/50000000000000 : ℝ)^3215
        have hw : |(2621207081/5000000000 : ℝ)|=(2621207081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13676043/62500000 : ℝ)|^4239 ≤ (674312866427/5000000000000 : ℝ)^3215
        have hw : |(-13676043/62500000 : ℝ)|=(13676043/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s6_3 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (108584011/250000000 : ℝ)*x 0 + (4169348631/10000000000 : ℝ)*x 1 + (4524347337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108584011/250000000 : ℝ)^4239 ≤ (1332081718633/4000000000000 : ℝ)^3215 := by
    have hnat : (108584011 : ℕ)^4239*4000000000000^3215 ≤ 1332081718633^3215*250000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108584011 250000000 1332081718633 4000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4169348631/10000000000 : ℝ)^4239 ≤ (31554207541133/100000000000000 : ℝ)^3215 := by
    have hnat : (4169348631 : ℕ)^4239*100000000000000^3215 ≤ 31554207541133^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169348631 10000000000 31554207541133 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4524347337/10000000000 : ℝ)^4239 ≤ (7028749896597/20000000000000 : ℝ)^3215 := by
    have hnat : (4524347337 : ℕ)^4239*20000000000000^3215 ≤ 7028749896597^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524347337 10000000000 7028749896597 20000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108584011/250000000 : ℝ), (4169348631/10000000000 : ℝ), (4524347337/10000000000 : ℝ)] ![(1332081718633/4000000000000 : ℝ), (31554207541133/100000000000000 : ℝ), (7028749896597/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108584011/250000000 : ℝ)|^4239 ≤ (1332081718633/4000000000000 : ℝ)^3215
        have hw : |(108584011/250000000 : ℝ)|=(108584011/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4169348631/10000000000 : ℝ)|^4239 ≤ (31554207541133/100000000000000 : ℝ)^3215
        have hw : |(4169348631/10000000000 : ℝ)|=(4169348631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4524347337/10000000000 : ℝ)|^4239 ≤ (7028749896597/20000000000000 : ℝ)^3215
        have hw : |(4524347337/10000000000 : ℝ)|=(4524347337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s6_4 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2099679081/10000000000 : ℝ)*x 0 + (1048606597/2000000000 : ℝ)*x 1 + (5415382857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099679081/10000000000 : ℝ)^4239 ≤ (12771852167359/100000000000000 : ℝ)^3215 := by
    have hnat : (2099679081 : ℕ)^4239*100000000000000^3215 ≤ 12771852167359^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099679081 10000000000 12771852167359 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048606597/2000000000 : ℝ)^4239 ≤ (42684252701581/100000000000000 : ℝ)^3215 := by
    have hnat : (1048606597 : ℕ)^4239*100000000000000^3215 ≤ 42684252701581^3215*2000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048606597 2000000000 42684252701581 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415382857/10000000000 : ℝ)^4239 ≤ (44543895111307/100000000000000 : ℝ)^3215 := by
    have hnat : (5415382857 : ℕ)^4239*100000000000000^3215 ≤ 44543895111307^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415382857 10000000000 44543895111307 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2099679081/10000000000 : ℝ), (1048606597/2000000000 : ℝ), (5415382857/10000000000 : ℝ)] ![(12771852167359/100000000000000 : ℝ), (42684252701581/100000000000000 : ℝ), (44543895111307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2099679081/10000000000 : ℝ)|^4239 ≤ (12771852167359/100000000000000 : ℝ)^3215
        have hw : |(-2099679081/10000000000 : ℝ)|=(2099679081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048606597/2000000000 : ℝ)|^4239 ≤ (42684252701581/100000000000000 : ℝ)^3215
        have hw : |(1048606597/2000000000 : ℝ)|=(1048606597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415382857/10000000000 : ℝ)|^4239 ≤ (44543895111307/100000000000000 : ℝ)^3215
        have hw : |(5415382857/10000000000 : ℝ)|=(5415382857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s6_5 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305627091/10000000000 : ℝ)*x 0 + (-12594989/62500000 : ℝ)*x 1 + (1353845721/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305627091/10000000000 : ℝ)^4239 ≤ (21678710509987/50000000000000 : ℝ)^3215 := by
    have hnat : (5305627091 : ℕ)^4239*50000000000000^3215 ≤ 21678710509987^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305627091 10000000000 21678710509987 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12594989/62500000 : ℝ)^4239 ≤ (6049341779399/50000000000000 : ℝ)^3215 := by
    have hnat : (12594989 : ℕ)^4239*50000000000000^3215 ≤ 6049341779399^3215*62500000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12594989 62500000 6049341779399 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353845721/2500000000 : ℝ)^4239 ≤ (4454389540413/10000000000000 : ℝ)^3215 := by
    have hnat : (1353845721 : ℕ)^4239*10000000000000^3215 ≤ 4454389540413^3215*2500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353845721 2500000000 4454389540413 10000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305627091/10000000000 : ℝ), (-12594989/62500000 : ℝ), (1353845721/2500000000 : ℝ)] ![(21678710509987/50000000000000 : ℝ), (6049341779399/50000000000000 : ℝ), (4454389540413/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305627091/10000000000 : ℝ)|^4239 ≤ (21678710509987/50000000000000 : ℝ)^3215
        have hw : |(5305627091/10000000000 : ℝ)|=(5305627091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-12594989/62500000 : ℝ)|^4239 ≤ (6049341779399/50000000000000 : ℝ)^3215
        have hw : |(-12594989/62500000 : ℝ)|=(12594989/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353845721/2500000000 : ℝ)|^4239 ≤ (4454389540413/10000000000000 : ℝ)^3215
        have hw : |(1353845721/2500000000 : ℝ)|=(1353845721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s6_6 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652813553/5000000000 : ℝ)*x 0 + (5415382909/10000000000 : ℝ)*x 1 + (-1007599093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652813553/5000000000 : ℝ)^4239 ≤ (10839355295399/25000000000000 : ℝ)^3215 := by
    have hnat : (2652813553 : ℕ)^4239*25000000000000^3215 ≤ 10839355295399^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652813553 5000000000 10839355295399 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415382909/10000000000 : ℝ)^4239 ≤ (44543895675263/100000000000000 : ℝ)^3215 := by
    have hnat : (5415382909 : ℕ)^4239*100000000000000^3215 ≤ 44543895675263^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415382909 10000000000 44543895675263 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1007599093/5000000000 : ℝ)^4239 ≤ (12098683131337/100000000000000 : ℝ)^3215 := by
    have hnat : (1007599093 : ℕ)^4239*100000000000000^3215 ≤ 12098683131337^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007599093 5000000000 12098683131337 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652813553/5000000000 : ℝ), (5415382909/10000000000 : ℝ), (-1007599093/5000000000 : ℝ)] ![(10839355295399/25000000000000 : ℝ), (44543895675263/100000000000000 : ℝ), (12098683131337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652813553/5000000000 : ℝ)|^4239 ≤ (10839355295399/25000000000000 : ℝ)^3215
        have hw : |(2652813553/5000000000 : ℝ)|=(2652813553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415382909/10000000000 : ℝ)|^4239 ≤ (44543895675263/100000000000000 : ℝ)^3215
        have hw : |(5415382909/10000000000 : ℝ)|=(5415382909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1007599093/5000000000 : ℝ)|^4239 ≤ (12098683131337/100000000000000 : ℝ)^3215
        have hw : |(-1007599093/5000000000 : ℝ)|=(1007599093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s6_7 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (542923357/1250000000 : ℝ)*x 0 + (4523081839/10000000000 : ℝ)*x 1 + (834124123/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542923357/1250000000 : ℝ)^4239 ≤ (33302310017263/100000000000000 : ℝ)^3215 := by
    have hnat : (542923357 : ℕ)^4239*100000000000000^3215 ≤ 33302310017263^3215*1250000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542923357 1250000000 33302310017263 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4523081839/10000000000 : ℝ)^4239 ≤ (35130789133547/100000000000000 : ℝ)^3215 := by
    have hnat : (4523081839 : ℕ)^4239*100000000000000^3215 ≤ 35130789133547^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523081839 10000000000 35130789133547 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (834124123/2000000000 : ℝ)^4239 ≤ (6313380166519/20000000000000 : ℝ)^3215 := by
    have hnat : (834124123 : ℕ)^4239*20000000000000^3215 ≤ 6313380166519^3215*2000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834124123 2000000000 6313380166519 20000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542923357/1250000000 : ℝ), (4523081839/10000000000 : ℝ), (834124123/2000000000 : ℝ)] ![(33302310017263/100000000000000 : ℝ), (35130789133547/100000000000000 : ℝ), (6313380166519/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542923357/1250000000 : ℝ)|^4239 ≤ (33302310017263/100000000000000 : ℝ)^3215
        have hw : |(542923357/1250000000 : ℝ)|=(542923357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4523081839/10000000000 : ℝ)|^4239 ≤ (35130789133547/100000000000000 : ℝ)^3215
        have hw : |(4523081839/10000000000 : ℝ)|=(4523081839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(834124123/2000000000 : ℝ)|^4239 ≤ (6313380166519/20000000000000 : ℝ)^3215
        have hw : |(834124123/2000000000 : ℝ)|=(834124123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1279_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10979/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (687/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7333/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14679/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10979/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14679/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10979/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14679/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10979/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14679/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10979/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14679/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10979/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14679/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10979/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10979/100000 : ℝ) ^ (2119/512 : ℝ) ≤ (10695576116661267/100000000000000000000 : ℝ) := by
    have hpowers : (10979/100000 : ℝ)^2119 ≤ (10695576116661267/100000000000000000000 : ℝ)^512 := by
      have hnat : (10979 : ℕ)^2119*100000000000000000000^512 ≤ 10695576116661267^512*100000^2119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10979 100000 10695576116661267 100000000000000000000 2119 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10979/100000 : ℝ)) (X := (10695576116661267/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14679/100000 : ℝ) ^ (2119/512 : ℝ) ≤ (35581980639212027/100000000000000000000 : ℝ) := by
    have hpowers : (14679/100000 : ℝ)^2119 ≤ (35581980639212027/100000000000000000000 : ℝ)^512 := by
      have hnat : (14679 : ℕ)^2119*100000000000000000000^512 ≤ 35581980639212027^512*100000^2119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14679 100000 35581980639212027 100000000000000000000 2119 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14679/100000 : ℝ)) (X := (35581980639212027/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010695576116661267/50000000000000000000 : ℝ) ≤ (10000516818390097/10000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (50010695576116661267/50000000000000000000 : ℝ)^512 ≤ (10000516818390097/10000000000000000 : ℝ)^2119 := by
      have hnat : (50010695576116661267 : ℕ)^512*10000000000000000^2119 ≤ 10000516818390097^2119*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010695576116661267 50000000000000000000 10000516818390097 10000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000516818390097/10000000000000000 : ℝ)) (X := (50010695576116661267/50000000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023138778377936647/50000000000000000000 : ℝ) ≤ (10001117977931383/10000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (50023138778377936647/50000000000000000000 : ℝ)^512 ≤ (10001117977931383/10000000000000000 : ℝ)^2119 := by
      have hnat : (50023138778377936647 : ℕ)^512*10000000000000000^2119 ≤ 10001117977931383^2119*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023138778377936647 50000000000000000000 10001117977931383 10000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001117977931383/10000000000000000 : ℝ)) (X := (50023138778377936647/50000000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035581980639212027/50000000000000000000 : ℝ) ≤ (10001719137472669/10000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (50035581980639212027/50000000000000000000 : ℝ)^512 ≤ (10001719137472669/10000000000000000 : ℝ)^2119 := by
      have hnat : (50035581980639212027 : ℕ)^512*10000000000000000^2119 ≤ 10001719137472669^2119*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035581980639212027 50000000000000000000 10001719137472669 10000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001719137472669/10000000000000000 : ℝ)) (X := (50035581980639212027/50000000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10695576116661267/100000000000000000000 : ℝ) ≤ ((2311794497927237557/2312500000000000000 : ℝ)+2*(300579770643/185000000000000 : ℝ)*(10979/100000 : ℝ))^(2119/512 : ℝ) := by
    rw [show (2311794497927237557/2312500000000000000 : ℝ)+2*(300579770643/185000000000000 : ℝ)*(10979/100000 : ℝ)=(10000516818390097/10000000000000000 : ℝ) by norm_num, show 1+2*(10695576116661267/100000000000000000000 : ℝ)=(50010695576116661267/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35581980639212027/100000000000000000000 : ℝ)+(10695576116661267/100000000000000000000 : ℝ) ≤ ((2311794497927237557/2312500000000000000 : ℝ)+(300579770643/185000000000000 : ℝ)*((14679/100000 : ℝ)+(10979/100000 : ℝ)))^(2119/512 : ℝ) := by
    rw [show (2311794497927237557/2312500000000000000 : ℝ)+(300579770643/185000000000000 : ℝ)*((14679/100000 : ℝ)+(10979/100000 : ℝ))=(10001117977931383/10000000000000000 : ℝ) by norm_num, show 1+(35581980639212027/100000000000000000000 : ℝ)+(10695576116661267/100000000000000000000 : ℝ)=(50023138778377936647/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35581980639212027/100000000000000000000 : ℝ) ≤ ((2311794497927237557/2312500000000000000 : ℝ)+2*(300579770643/185000000000000 : ℝ)*(14679/100000 : ℝ))^(2119/512 : ℝ) := by
    rw [show (2311794497927237557/2312500000000000000 : ℝ)+2*(300579770643/185000000000000 : ℝ)*(14679/100000 : ℝ)=(10001719137472669/10000000000000000 : ℝ) by norm_num, show 1+2*(35581980639212027/100000000000000000000 : ℝ)=(50035581980639212027/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2311794497927237557/2312500000000000000 : ℝ)*(X 1 0+X 2 0)+(300579770643/185000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (10979/100000 : ℝ)) (hi := (14679/100000 : ℝ)) (c := (2311794497927237557/2312500000000000000 : ℝ)) (alpha := (300579770643/185000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2311794497927237557/2312500000000000000 : ℝ)*(X 0 1+X 2 1)+(300579770643/185000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (10979/100000 : ℝ)) (hi := (14679/100000 : ℝ)) (c := (2311794497927237557/2312500000000000000 : ℝ)) (alpha := (300579770643/185000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2311794497927237557/2312500000000000000 : ℝ)*(X 0 2+X 1 2)+(300579770643/185000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (10979/100000 : ℝ)) (hi := (14679/100000 : ℝ)) (c := (2311794497927237557/2312500000000000000 : ℝ)) (alpha := (300579770643/185000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2099666149/10000000000 : ℝ)*X 0 0+(5416004879/10000000000 : ℝ)*X 0 1+(2621207081/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349996909/10000000000 : ℝ)*X 1 0+(-13676043/62500000 : ℝ)*X 1 1+(2621207081/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349996909/10000000000 : ℝ)*X 2 0+(2621207081/5000000000 : ℝ)*X 2 1+(-13676043/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((108584011/250000000 : ℝ)*X 0 0+(4169348631/10000000000 : ℝ)*X 0 1+(4524347337/10000000000 : ℝ)*X 0 2+(108584011/250000000 : ℝ)*X 1 0+(4169348631/10000000000 : ℝ)*X 1 1+(4524347337/10000000000 : ℝ)*X 1 2+(108584011/250000000 : ℝ)*X 2 0+(4169348631/10000000000 : ℝ)*X 2 1+(4524347337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2099679081/10000000000 : ℝ)*X 0 0+(1048606597/2000000000 : ℝ)*X 0 1+(5415382857/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305627091/10000000000 : ℝ)*X 1 0+(-12594989/62500000 : ℝ)*X 1 1+(1353845721/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652813553/5000000000 : ℝ)*X 2 0+(5415382909/10000000000 : ℝ)*X 2 1+(-1007599093/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((542923357/1250000000 : ℝ)*X 0 0+(4523081839/10000000000 : ℝ)*X 0 1+(834124123/2000000000 : ℝ)*X 0 2+(542923357/1250000000 : ℝ)*X 1 0+(4523081839/10000000000 : ℝ)*X 1 1+(834124123/2000000000 : ℝ)*X 1 2+(542923357/1250000000 : ℝ)*X 2 0+(4523081839/10000000000 : ℝ)*X 2 1+(834124123/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (579580823758177344230523489/115625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (968497023/100000000000000 : ℝ)*(base19) + (902838573/100000000000000 : ℝ)*(base23) + (140509/400000000000 : ℝ)*(lower2) + (15863299/12500000000000 : ℝ)*(upper3) + (77975751/100000000000000 : ℝ)*(upper5) + (4288823710457959/100000000000000 : ℝ)*(major0) + (4288823710457959/100000000000000 : ℝ)*(major1) + (4288823710457959/100000000000000 : ℝ)*(major2) + (1440174222608319/25000000000000 : ℝ)*(sp0) + (5760715223948043/100000000000000 : ℝ)*(sp1) + (1440178822401623/25000000000000 : ℝ)*(sp2) + (2816920845516191/100000000000000 : ℝ)*(sp3) + (1930201179/10000000000000 : ℝ)*(sp4) + (2553967071/25000000000000 : ℝ)*(sp7) + (1408465530692237/50000000000000 : ℝ)*(f.failure) + (2880358096222533/50000000000000 : ℝ)*(f.sum) + (20411221379863/9250000000000000000000000000 : ℝ)*base66 + (441475226306078663/231250000000000000000000000000000 : ℝ)*base67 + (201867180356421337/231250000000000000000000000000000 : ℝ)*base70 + (1665358580943921337/231250000000000000000000000000000 : ℝ)*base72 + (51807968454613/9250000000000000000000000000 : ℝ)*base74 + (2648271619656421337/231250000000000000000000000000000 : ℝ)*base76 + (1480297101050171337/231250000000000000000000000000000 : ℝ)*base78 + (4604184981618578663/231250000000000000000000000000000 : ℝ)*base79 + (57465824472113/9250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (62173557/5000000000000000000000 : ℝ)*base90 + (62173557/5000000000000000000000 : ℝ)*base92 + (62173557/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (165763101549692749586370891/14453125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1930818799/100000000000000 : ℝ)*(base19) + (425400493/20000000000000 : ℝ)*(base23) + (253930993/100000000000000 : ℝ)*(upper3) + (8962373/12500000000000 : ℝ)*(lower4) + (116870281/50000000000000 : ℝ)*(upper5) + (539958819180973/12500000000000 : ℝ)*(major0) + (539958819180973/12500000000000 : ℝ)*(major1) + (539958819180973/12500000000000 : ℝ)*(major2) + (9350553299/25000000000000 : ℝ)*(sp1) + (8548087193/20000000000000 : ℝ)*(sp2) + (5802149229107929/100000000000000 : ℝ)*(sp4) + (1160421979215187/20000000000000 : ℝ)*(sp5) + (11604208723339/200000000000 : ℝ)*(sp6) + (1418595747743571/50000000000000 : ℝ)*(sp7) + (1418595747743571/50000000000000 : ℝ)*(f.failure) + (5802149229107929/100000000000000 : ℝ)*(f.sum) + (2042336098819/4625000000000000000000000000 : ℝ)*base66 + (38233822527078289/28906250000000000000000000000000 : ℝ)*base68 + (613186456402078289/28906250000000000000000000000000 : ℝ)*base70 + (266085014031765789/28906250000000000000000000000000 : ℝ)*base72 + (1174808132847/2312500000000000000000000000 : ℝ)*base74 + (668328167451297039/28906250000000000000000000000000 : ℝ)*base76 + (410261669213015789/28906250000000000000000000000000 : ℝ)*base78 + (132177951453390461/28906250000000000000000000000000 : ℝ)*base79 + (8236153774347/2312500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (36462869/5000000000000000000000 : ℝ)*base89 + (36462869/5000000000000000000000 : ℝ)*base91 + (36462869/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1279_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10979/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (687/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7333/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1279_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1279_s7_0 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2099677961/10000000000 : ℝ)*x 0 + (108317721/200000000 : ℝ)*x 1 + (5242525403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099677961/10000000000 : ℝ)^4239 ≤ (12771843184773/100000000000000 : ℝ)^3215 := by
    have hnat : (2099677961 : ℕ)^4239*100000000000000^3215 ≤ 12771843184773^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099677961 10000000000 12771843184773 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108317721/200000000 : ℝ)^4239 ≤ (44549352469779/100000000000000 : ℝ)^3215 := by
    have hnat : (108317721 : ℕ)^4239*100000000000000^3215 ≤ 44549352469779^3215*200000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108317721 200000000 44549352469779 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242525403/10000000000 : ℝ)^4239 ≤ (42678804325867/100000000000000 : ℝ)^3215 := by
    have hnat : (5242525403 : ℕ)^4239*100000000000000^3215 ≤ 42678804325867^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242525403 10000000000 42678804325867 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2099677961/10000000000 : ℝ), (108317721/200000000 : ℝ), (5242525403/10000000000 : ℝ)] ![(12771843184773/100000000000000 : ℝ), (44549352469779/100000000000000 : ℝ), (42678804325867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2099677961/10000000000 : ℝ)|^4239 ≤ (12771843184773/100000000000000 : ℝ)^3215
        have hw : |(-2099677961/10000000000 : ℝ)|=(2099677961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108317721/200000000 : ℝ)|^4239 ≤ (44549352469779/100000000000000 : ℝ)^3215
        have hw : |(108317721/200000000 : ℝ)|=(108317721/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242525403/10000000000 : ℝ)|^4239 ≤ (42678804325867/100000000000000 : ℝ)^3215
        have hw : |(5242525403/10000000000 : ℝ)|=(5242525403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s7_1 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674983899/5000000000 : ℝ)*x 0 + (-273507373/1250000000 : ℝ)*x 1 + (2621262573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674983899/5000000000 : ℝ)^4239 ≤ (21917908934859/50000000000000 : ℝ)^3215 := by
    have hnat : (2674983899 : ℕ)^4239*50000000000000^3215 ≤ 21917908934859^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674983899 5000000000 21917908934859 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273507373/1250000000 : ℝ)^4239 ≤ (13485380538969/100000000000000 : ℝ)^3215 := by
    have hnat : (273507373 : ℕ)^4239*100000000000000^3215 ≤ 13485380538969^3215*1250000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273507373 1250000000 13485380538969 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621262573/5000000000 : ℝ)^4239 ≤ (10669700391819/25000000000000 : ℝ)^3215 := by
    have hnat : (2621262573 : ℕ)^4239*25000000000000^3215 ≤ 10669700391819^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621262573 5000000000 10669700391819 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674983899/5000000000 : ℝ), (-273507373/1250000000 : ℝ), (2621262573/5000000000 : ℝ)] ![(21917908934859/50000000000000 : ℝ), (13485380538969/100000000000000 : ℝ), (10669700391819/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674983899/5000000000 : ℝ)|^4239 ≤ (21917908934859/50000000000000 : ℝ)^3215
        have hw : |(2674983899/5000000000 : ℝ)|=(2674983899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-273507373/1250000000 : ℝ)|^4239 ≤ (13485380538969/100000000000000 : ℝ)^3215
        have hw : |(-273507373/1250000000 : ℝ)|=(273507373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621262573/5000000000 : ℝ)|^4239 ≤ (10669700391819/25000000000000 : ℝ)^3215
        have hw : |(2621262573/5000000000 : ℝ)|=(2621262573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s7_2 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349967041/10000000000 : ℝ)*x 0 + (1048505073/2000000000 : ℝ)*x 1 + (-2188059701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349967041/10000000000 : ℝ)^4239 ≤ (21917904845773/50000000000000 : ℝ)^3215 := by
    have hnat : (5349967041 : ℕ)^4239*50000000000000^3215 ≤ 21917904845773^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349967041 10000000000 21917904845773 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048505073/2000000000 : ℝ)^4239 ≤ (21339401958991/50000000000000 : ℝ)^3215 := by
    have hnat : (1048505073 : ℕ)^4239*50000000000000^3215 ≤ 21339401958991^3215*2000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048505073 2000000000 21339401958991 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2188059701/10000000000 : ℝ)^4239 ≤ (13485386365443/100000000000000 : ℝ)^3215 := by
    have hnat : (2188059701 : ℕ)^4239*100000000000000^3215 ≤ 13485386365443^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188059701 10000000000 13485386365443 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349967041/10000000000 : ℝ), (1048505073/2000000000 : ℝ), (-2188059701/10000000000 : ℝ)] ![(21917904845773/50000000000000 : ℝ), (21339401958991/50000000000000 : ℝ), (13485386365443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349967041/10000000000 : ℝ)|^4239 ≤ (21917904845773/50000000000000 : ℝ)^3215
        have hw : |(5349967041/10000000000 : ℝ)|=(5349967041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048505073/2000000000 : ℝ)|^4239 ≤ (21339401958991/50000000000000 : ℝ)^3215
        have hw : |(1048505073/2000000000 : ℝ)|=(1048505073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2188059701/10000000000 : ℝ)|^4239 ≤ (13485386365443/100000000000000 : ℝ)^3215
        have hw : |(-2188059701/10000000000 : ℝ)|=(2188059701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s7_3 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (217168429/500000000 : ℝ)*x 0 + (4169582931/10000000000 : ℝ)*x 1 + (4524111017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217168429/500000000 : ℝ)^4239 ≤ (8325531314189/25000000000000 : ℝ)^3215 := by
    have hnat : (217168429 : ℕ)^4239*25000000000000^3215 ≤ 8325531314189^3215*500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217168429 500000000 8325531314189 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4169582931/10000000000 : ℝ)^4239 ≤ (31556545558221/100000000000000 : ℝ)^3215 := by
    have hnat : (4169582931 : ℕ)^4239*100000000000000^3215 ≤ 31556545558221^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169582931 10000000000 31556545558221 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4524111017/10000000000 : ℝ)^4239 ≤ (4392666146299/12500000000000 : ℝ)^3215 := by
    have hnat : (4524111017 : ℕ)^4239*12500000000000^3215 ≤ 4392666146299^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524111017 10000000000 4392666146299 12500000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(217168429/500000000 : ℝ), (4169582931/10000000000 : ℝ), (4524111017/10000000000 : ℝ)] ![(8325531314189/25000000000000 : ℝ), (31556545558221/100000000000000 : ℝ), (4392666146299/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(217168429/500000000 : ℝ)|^4239 ≤ (8325531314189/25000000000000 : ℝ)^3215
        have hw : |(217168429/500000000 : ℝ)|=(217168429/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4169582931/10000000000 : ℝ)|^4239 ≤ (31556545558221/100000000000000 : ℝ)^3215
        have hw : |(4169582931/10000000000 : ℝ)|=(4169582931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4524111017/10000000000 : ℝ)|^4239 ≤ (4392666146299/12500000000000 : ℝ)^3215
        have hw : |(4524111017/10000000000 : ℝ)|=(4524111017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s7_4 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1049845353/5000000000 : ℝ)*x 0 + (5243142549/10000000000 : ℝ)*x 1 + (2707632909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049845353/5000000000 : ℝ)^4239 ≤ (319298635047/2500000000000 : ℝ)^3215 := by
    have hnat : (1049845353 : ℕ)^4239*2500000000000^3215 ≤ 319298635047^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049845353 5000000000 319298635047 2500000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243142549/10000000000 : ℝ)^4239 ≤ (42685428781559/100000000000000 : ℝ)^3215 := by
    have hnat : (5243142549 : ℕ)^4239*100000000000000^3215 ≤ 42685428781559^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243142549 10000000000 42685428781559 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707632909/5000000000 : ℝ)^4239 ≤ (22271312896459/50000000000000 : ℝ)^3215 := by
    have hnat : (2707632909 : ℕ)^4239*50000000000000^3215 ≤ 22271312896459^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707632909 5000000000 22271312896459 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1049845353/5000000000 : ℝ), (5243142549/10000000000 : ℝ), (2707632909/5000000000 : ℝ)] ![(319298635047/2500000000000 : ℝ), (42685428781559/100000000000000 : ℝ), (22271312896459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1049845353/5000000000 : ℝ)|^4239 ≤ (319298635047/2500000000000 : ℝ)^3215
        have hw : |(-1049845353/5000000000 : ℝ)|=(1049845353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243142549/10000000000 : ℝ)|^4239 ≤ (42685428781559/100000000000000 : ℝ)^3215
        have hw : |(5243142549/10000000000 : ℝ)|=(5243142549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707632909/5000000000 : ℝ)|^4239 ≤ (22271312896459/50000000000000 : ℝ)^3215
        have hw : |(2707632909/5000000000 : ℝ)|=(2707632909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s7_5 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305656439/10000000000 : ℝ)*x 0 + (-1007659339/5000000000 : ℝ)*x 1 + (2707632909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305656439/10000000000 : ℝ)^4239 ≤ (16936616109/39062500000 : ℝ)^3215 := by
    have hnat : (5305656439 : ℕ)^4239*39062500000^3215 ≤ 16936616109^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305656439 10000000000 16936616109 39062500000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1007659339/5000000000 : ℝ)^4239 ≤ (12099636948487/100000000000000 : ℝ)^3215 := by
    have hnat : (1007659339 : ℕ)^4239*100000000000000^3215 ≤ 12099636948487^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007659339 5000000000 12099636948487 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707632909/5000000000 : ℝ)^4239 ≤ (22271312896459/50000000000000 : ℝ)^3215 := by
    have hnat : (2707632909 : ℕ)^4239*50000000000000^3215 ≤ 22271312896459^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707632909 5000000000 22271312896459 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305656439/10000000000 : ℝ), (-1007659339/5000000000 : ℝ), (2707632909/5000000000 : ℝ)] ![(16936616109/39062500000 : ℝ), (12099636948487/100000000000000 : ℝ), (22271312896459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305656439/10000000000 : ℝ)|^4239 ≤ (16936616109/39062500000 : ℝ)^3215
        have hw : |(5305656439/10000000000 : ℝ)|=(5305656439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1007659339/5000000000 : ℝ)|^4239 ≤ (12099636948487/100000000000000 : ℝ)^3215
        have hw : |(-1007659339/5000000000 : ℝ)|=(1007659339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707632909/5000000000 : ℝ)|^4239 ≤ (22271312896459/50000000000000 : ℝ)^3215
        have hw : |(2707632909/5000000000 : ℝ)|=(2707632909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s7_6 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326414111/2500000000 : ℝ)*x 0 + (5415265817/10000000000 : ℝ)*x 1 + (-1007659337/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326414111/2500000000 : ℝ)^4239 ≤ (21678868646457/50000000000000 : ℝ)^3215 := by
    have hnat : (1326414111 : ℕ)^4239*50000000000000^3215 ≤ 21678868646457^3215*2500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326414111 2500000000 21678868646457 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415265817/10000000000 : ℝ)^4239 ≤ (5567828222759/12500000000000 : ℝ)^3215 := by
    have hnat : (5415265817 : ℕ)^4239*12500000000000^3215 ≤ 5567828222759^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415265817 10000000000 5567828222759 12500000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1007659337/5000000000 : ℝ)^4239 ≤ (12099636916823/100000000000000 : ℝ)^3215 := by
    have hnat : (1007659337 : ℕ)^4239*100000000000000^3215 ≤ 12099636916823^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007659337 5000000000 12099636916823 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326414111/2500000000 : ℝ), (5415265817/10000000000 : ℝ), (-1007659337/5000000000 : ℝ)] ![(21678868646457/50000000000000 : ℝ), (5567828222759/12500000000000 : ℝ), (12099636916823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326414111/2500000000 : ℝ)|^4239 ≤ (21678868646457/50000000000000 : ℝ)^3215
        have hw : |(1326414111/2500000000 : ℝ)|=(1326414111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415265817/10000000000 : ℝ)|^4239 ≤ (5567828222759/12500000000000 : ℝ)^3215
        have hw : |(5415265817/10000000000 : ℝ)|=(5415265817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1007659337/5000000000 : ℝ)|^4239 ≤ (12099636916823/100000000000000 : ℝ)^3215
        have hw : |(-1007659337/5000000000 : ℝ)|=(1007659337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s7_7 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2171697459/5000000000 : ℝ)*x 0 + (2261424523/5000000000 : ℝ)*x 1 + (4170851331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171697459/5000000000 : ℝ)^4239 ≤ (6660478303963/20000000000000 : ℝ)^3215 := by
    have hnat : (2171697459 : ℕ)^4239*20000000000000^3215 ≤ 6660478303963^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171697459 5000000000 6660478303963 20000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2261424523/5000000000 : ℝ)^4239 ≤ (8782101288869/25000000000000 : ℝ)^3215 := by
    have hnat : (2261424523 : ℕ)^4239*25000000000000^3215 ≤ 8782101288869^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261424523 5000000000 8782101288869 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4170851331/10000000000 : ℝ)^4239 ≤ (31569203309269/100000000000000 : ℝ)^3215 := by
    have hnat : (4170851331 : ℕ)^4239*100000000000000^3215 ≤ 31569203309269^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170851331 10000000000 31569203309269 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171697459/5000000000 : ℝ), (2261424523/5000000000 : ℝ), (4170851331/10000000000 : ℝ)] ![(6660478303963/20000000000000 : ℝ), (8782101288869/25000000000000 : ℝ), (31569203309269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171697459/5000000000 : ℝ)|^4239 ≤ (6660478303963/20000000000000 : ℝ)^3215
        have hw : |(2171697459/5000000000 : ℝ)|=(2171697459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2261424523/5000000000 : ℝ)|^4239 ≤ (8782101288869/25000000000000 : ℝ)^3215
        have hw : |(2261424523/5000000000 : ℝ)|=(2261424523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4170851331/10000000000 : ℝ)|^4239 ≤ (31569203309269/100000000000000 : ℝ)^3215
        have hw : |(4170851331/10000000000 : ℝ)|=(4170851331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1279_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7333/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (687/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (5497/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14663/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7333/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (687/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7333/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (687/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7333/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (687/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7333/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (687/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7333/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (687/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7333/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (687/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (687/6250 : ℝ) ^ (2119/512 : ℝ) ≤ (10748087407047103/100000000000000000000 : ℝ) := by
    have hpowers : (687/6250 : ℝ)^2119 ≤ (10748087407047103/100000000000000000000 : ℝ)^512 := by
      have hnat : (687 : ℕ)^2119*100000000000000000000^512 ≤ 10748087407047103^512*6250^2119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        687 6250 10748087407047103 100000000000000000000 2119 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (687/6250 : ℝ)) (X := (10748087407047103/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7333/50000 : ℝ) ^ (2119/512 : ℝ) ≤ (1772587182297979/5000000000000000000 : ℝ) := by
    have hpowers : (7333/50000 : ℝ)^2119 ≤ (1772587182297979/5000000000000000000 : ℝ)^512 := by
      have hnat : (7333 : ℕ)^2119*5000000000000000000^512 ≤ 1772587182297979^512*50000^2119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7333 50000 1772587182297979 5000000000000000000 2119 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7333/50000 : ℝ)) (X := (1772587182297979/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010748087407047103/50000000000000000000 : ℝ) ≤ (10000519355568883/10000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (50010748087407047103/50000000000000000000 : ℝ)^512 ≤ (10000519355568883/10000000000000000 : ℝ)^2119 := by
      have hnat : (50010748087407047103 : ℕ)^512*10000000000000000^2119 ≤ 10000519355568883^2119*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010748087407047103 50000000000000000000 10000519355568883 10000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000519355568883/10000000000000000 : ℝ)) (X := (50010748087407047103/50000000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046199831053006683/100000000000000000000 : ℝ) ≤ (5000558050277379/5000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (100046199831053006683/100000000000000000000 : ℝ)^512 ≤ (5000558050277379/5000000000000000 : ℝ)^2119 := by
      have hnat : (100046199831053006683 : ℕ)^512*5000000000000000^2119 ≤ 5000558050277379^2119*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046199831053006683 100000000000000000000 5000558050277379 5000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000558050277379/5000000000000000 : ℝ)) (X := (100046199831053006683/100000000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501772587182297979/2500000000000000000 : ℝ) ≤ (10001712845540633/10000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (2501772587182297979/2500000000000000000 : ℝ)^512 ≤ (10001712845540633/10000000000000000 : ℝ)^2119 := by
      have hnat : (2501772587182297979 : ℕ)^512*10000000000000000^2119 ≤ 10001712845540633^2119*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501772587182297979 2500000000000000000 10001712845540633 10000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001712845540633/10000000000000000 : ℝ)) (X := (2501772587182297979/2500000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10748087407047103/100000000000000000000 : ℝ) ≤ ((18364394635295300071/18370000000000000000 : ℝ)+2*(4773959887/2939200000000 : ℝ)*(687/6250 : ℝ))^(2119/512 : ℝ) := by
    rw [show (18364394635295300071/18370000000000000000 : ℝ)+2*(4773959887/2939200000000 : ℝ)*(687/6250 : ℝ)=(10000519355568883/10000000000000000 : ℝ) by norm_num, show 1+2*(10748087407047103/100000000000000000000 : ℝ)=(50010748087407047103/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1772587182297979/5000000000000000000 : ℝ)+(10748087407047103/100000000000000000000 : ℝ) ≤ ((18364394635295300071/18370000000000000000 : ℝ)+(4773959887/2939200000000 : ℝ)*((7333/50000 : ℝ)+(687/6250 : ℝ)))^(2119/512 : ℝ) := by
    rw [show (18364394635295300071/18370000000000000000 : ℝ)+(4773959887/2939200000000 : ℝ)*((7333/50000 : ℝ)+(687/6250 : ℝ))=(5000558050277379/5000000000000000 : ℝ) by norm_num, show 1+(1772587182297979/5000000000000000000 : ℝ)+(10748087407047103/100000000000000000000 : ℝ)=(100046199831053006683/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1772587182297979/5000000000000000000 : ℝ) ≤ ((18364394635295300071/18370000000000000000 : ℝ)+2*(4773959887/2939200000000 : ℝ)*(7333/50000 : ℝ))^(2119/512 : ℝ) := by
    rw [show (18364394635295300071/18370000000000000000 : ℝ)+2*(4773959887/2939200000000 : ℝ)*(7333/50000 : ℝ)=(10001712845540633/10000000000000000 : ℝ) by norm_num, show 1+2*(1772587182297979/5000000000000000000 : ℝ)=(2501772587182297979/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18364394635295300071/18370000000000000000 : ℝ)*(X 1 0+X 2 0)+(4773959887/2939200000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (687/6250 : ℝ)) (hi := (7333/50000 : ℝ)) (c := (18364394635295300071/18370000000000000000 : ℝ)) (alpha := (4773959887/2939200000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18364394635295300071/18370000000000000000 : ℝ)*(X 0 1+X 2 1)+(4773959887/2939200000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (687/6250 : ℝ)) (hi := (7333/50000 : ℝ)) (c := (18364394635295300071/18370000000000000000 : ℝ)) (alpha := (4773959887/2939200000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18364394635295300071/18370000000000000000 : ℝ)*(X 0 2+X 1 2)+(4773959887/2939200000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (687/6250 : ℝ)) (hi := (7333/50000 : ℝ)) (c := (18364394635295300071/18370000000000000000 : ℝ)) (alpha := (4773959887/2939200000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2099677961/10000000000 : ℝ)*X 0 0+(108317721/200000000 : ℝ)*X 0 1+(5242525403/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674983899/5000000000 : ℝ)*X 1 0+(-273507373/1250000000 : ℝ)*X 1 1+(2621262573/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349967041/10000000000 : ℝ)*X 2 0+(1048505073/2000000000 : ℝ)*X 2 1+(-2188059701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((217168429/500000000 : ℝ)*X 0 0+(4169582931/10000000000 : ℝ)*X 0 1+(4524111017/10000000000 : ℝ)*X 0 2+(217168429/500000000 : ℝ)*X 1 0+(4169582931/10000000000 : ℝ)*X 1 1+(4524111017/10000000000 : ℝ)*X 1 2+(217168429/500000000 : ℝ)*X 2 0+(4169582931/10000000000 : ℝ)*X 2 1+(4524111017/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1049845353/5000000000 : ℝ)*X 0 0+(5243142549/10000000000 : ℝ)*X 0 1+(2707632909/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305656439/10000000000 : ℝ)*X 1 0+(-1007659339/5000000000 : ℝ)*X 1 1+(2707632909/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326414111/2500000000 : ℝ)*X 2 0+(5415265817/10000000000 : ℝ)*X 2 1+(-1007659337/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2171697459/5000000000 : ℝ)*X 0 0+(2261424523/5000000000 : ℝ)*X 0 1+(4170851331/10000000000 : ℝ)*X 0 2+(2171697459/5000000000 : ℝ)*X 1 0+(2261424523/5000000000 : ℝ)*X 1 1+(4170851331/10000000000 : ℝ)*X 1 2+(2171697459/5000000000 : ℝ)*X 2 0+(2261424523/5000000000 : ℝ)*X 2 1+(4170851331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8063181254881639954389272061/918500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (492544239/25000000000000 : ℝ)*(base19) + (1028450581/100000000000000 : ℝ)*(base23) + (4900473/50000000000000 : ℝ)*(upper2) + (100423529/25000000000000 : ℝ)*(upper3) + (4294535732337897/100000000000000 : ℝ)*(major0) + (4294535732337897/100000000000000 : ℝ)*(major1) + (4294535732337897/100000000000000 : ℝ)*(major2) + (5768365987858249/100000000000000 : ℝ)*(sp0) + (5768386442371757/100000000000000 : ℝ)*(sp1) + (5768370017011393/100000000000000 : ℝ)*(sp2) + (2820665661186459/100000000000000 : ℝ)*(sp3) + (700771577/3125000000000 : ℝ)*(sp4) + (17367086739/100000000000000 : ℝ)*(sp6) + (17098319267/100000000000000 : ℝ)*(sp7) + (1410341379752863/50000000000000 : ℝ)*(f.failure) + (5768388412548713/100000000000000 : ℝ)*(f.sum) + (25228233347/3674000000000000000000000000 : ℝ)*base66 + (5091397063865159313/1837000000000000000000000000000000 : ℝ)*base68 + (5583424114100840687/1837000000000000000000000000000000 : ℝ)*base69 + (14938066778379840687/1837000000000000000000000000000000 : ℝ)*base71 + (5429756705327/3674000000000000000000000000 : ℝ)*base74 + (7417654284350159313/1837000000000000000000000000000000 : ℝ)*base76 + (2438324065311159313/1837000000000000000000000000000000 : ℝ)*base78 + (1027411189279159313/1837000000000000000000000000000000 : ℝ)*base80 + (5298360482901/3674000000000000000000000000 : ℝ)*base81 + (43307543/5000000000000000000000 : ℝ)*base90 + (43307543/5000000000000000000000 : ℝ)*base92 + (43307543/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1445395106460221207608153557/229625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1086433919/100000000000000 : ℝ)*(base19) + (240631961/20000000000000 : ℝ)*(base23) + (18745507/5000000000000 : ℝ)*(lower1) + (123190937/100000000000000 : ℝ)*(upper3) + (10028677/20000000000000 : ℝ)*(lower4) + (63948493/50000000000000 : ℝ)*(upper5) + (1081335482965711/25000000000000 : ℝ)*(major0) + (1081335482965711/25000000000000 : ℝ)*(major1) + (1081335482965711/25000000000000 : ℝ)*(major2) + (2004593853/100000000000000 : ℝ)*(sp2) + (5809767155225281/100000000000000 : ℝ)*(sp4) + (2904883034395681/50000000000000 : ℝ)*(sp5) + (726220493433953/12500000000000 : ℝ)*(sp6) + (1420458249340371/50000000000000 : ℝ)*(sp7) + (1420458249340371/50000000000000 : ℝ)*(f.failure) + (5809767155225281/100000000000000 : ℝ)*(f.sum) + (221758022291/45925000000000000000000000 : ℝ)*base66 + (8111020220945865481/459250000000000000000000000000000 : ℝ)*base67 + (2863051498100115481/459250000000000000000000000000000 : ℝ)*base69 + (4122249666879384519/459250000000000000000000000000000 : ℝ)*base72 + (2146551605149/918500000000000000000000000 : ℝ)*base73 + (23564425278863615481/459250000000000000000000000000000 : ℝ)*base75 + (1948546640143865481/459250000000000000000000000000000 : ℝ)*base77 + (1720914638031134519/459250000000000000000000000000000 : ℝ)*base80 + (9431546992251/1837000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (46381931/5000000000000000000000 : ℝ)*base90 + (46381931/5000000000000000000000 : ℝ)*base92 + (46381931/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1279_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7333/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (687/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5497/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14663/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1279_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1279_s8_0 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-524920759/2500000000 : ℝ)*x 0 + (1353965481/2500000000 : ℝ)*x 1 + (1310636497/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524920759/2500000000 : ℝ)^4239 ≤ (1596485485891/12500000000000 : ℝ)^3215 := by
    have hnat : (524920759 : ℕ)^4239*12500000000000^3215 ≤ 1596485485891^3215*2500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524920759 2500000000 1596485485891 12500000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353965481/2500000000 : ℝ)^4239 ≤ (44549090808577/100000000000000 : ℝ)^3215 := by
    have hnat : (1353965481 : ℕ)^4239*100000000000000^3215 ≤ 44549090808577^3215*2500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353965481 2500000000 44549090808577 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310636497/2500000000 : ℝ)^4239 ≤ (10669756320401/25000000000000 : ℝ)^3215 := by
    have hnat : (1310636497 : ℕ)^4239*25000000000000^3215 ≤ 10669756320401^3215*2500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310636497 2500000000 10669756320401 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-524920759/2500000000 : ℝ), (1353965481/2500000000 : ℝ), (1310636497/2500000000 : ℝ)] ![(1596485485891/12500000000000 : ℝ), (44549090808577/100000000000000 : ℝ), (10669756320401/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-524920759/2500000000 : ℝ)|^4239 ≤ (1596485485891/12500000000000 : ℝ)^3215
        have hw : |(-524920759/2500000000 : ℝ)|=(524920759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353965481/2500000000 : ℝ)|^4239 ≤ (44549090808577/100000000000000 : ℝ)^3215
        have hw : |(1353965481/2500000000 : ℝ)|=(1353965481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310636497/2500000000 : ℝ)|^4239 ≤ (10669756320401/25000000000000 : ℝ)^3215
        have hw : |(1310636497/2500000000 : ℝ)|=(1310636497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s8_1 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674980307/5000000000 : ℝ)*x 0 + (-547010249/2500000000 : ℝ)*x 1 + (1310636499/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674980307/5000000000 : ℝ)^4239 ≤ (21917870129061/50000000000000 : ℝ)^3215 := by
    have hnat : (2674980307 : ℕ)^4239*50000000000000^3215 ≤ 21917870129061^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674980307 5000000000 21917870129061 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547010249/2500000000 : ℝ)^4239 ≤ (13485234365373/100000000000000 : ℝ)^3215 := by
    have hnat : (547010249 : ℕ)^4239*100000000000000^3215 ≤ 13485234365373^3215*2500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547010249 2500000000 13485234365373 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310636499/2500000000 : ℝ)^4239 ≤ (1707161014699/4000000000000 : ℝ)^3215 := by
    have hnat : (1310636499 : ℕ)^4239*4000000000000^3215 ≤ 1707161014699^3215*2500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310636499 2500000000 1707161014699 4000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674980307/5000000000 : ℝ), (-547010249/2500000000 : ℝ), (1310636499/2500000000 : ℝ)] ![(21917870129061/50000000000000 : ℝ), (13485234365373/100000000000000 : ℝ), (1707161014699/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674980307/5000000000 : ℝ)|^4239 ≤ (21917870129061/50000000000000 : ℝ)^3215
        have hw : |(2674980307/5000000000 : ℝ)|=(2674980307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-547010249/2500000000 : ℝ)|^4239 ≤ (13485234365373/100000000000000 : ℝ)^3215
        have hw : |(-547010249/2500000000 : ℝ)|=(547010249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310636499/2500000000 : ℝ)|^4239 ≤ (1707161014699/4000000000000 : ℝ)^3215
        have hw : |(1310636499/2500000000 : ℝ)|=(1310636499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s8_2 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349960633/10000000000 : ℝ)*x 0 + (5242545997/10000000000 : ℝ)*x 1 + (-2188040969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349960633/10000000000 : ℝ)^4239 ≤ (21917870231693/50000000000000 : ℝ)^3215 := by
    have hnat : (5349960633 : ℕ)^4239*50000000000000^3215 ≤ 21917870231693^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349960633 10000000000 21917870231693 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242545997/10000000000 : ℝ)^4239 ≤ (1333719543069/3125000000000 : ℝ)^3215 := by
    have hnat : (5242545997 : ℕ)^4239*3125000000000^3215 ≤ 1333719543069^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242545997 10000000000 1333719543069 3125000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2188040969/10000000000 : ℝ)^4239 ≤ (13485234145967/100000000000000 : ℝ)^3215 := by
    have hnat : (2188040969 : ℕ)^4239*100000000000000^3215 ≤ 13485234145967^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188040969 10000000000 13485234145967 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349960633/10000000000 : ℝ), (5242545997/10000000000 : ℝ), (-2188040969/10000000000 : ℝ)] ![(21917870231693/50000000000000 : ℝ), (1333719543069/3125000000000 : ℝ), (13485234145967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349960633/10000000000 : ℝ)|^4239 ≤ (21917870231693/50000000000000 : ℝ)^3215
        have hw : |(5349960633/10000000000 : ℝ)|=(5349960633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242545997/10000000000 : ℝ)|^4239 ≤ (1333719543069/3125000000000 : ℝ)^3215
        have hw : |(5242545997/10000000000 : ℝ)|=(5242545997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2188040969/10000000000 : ℝ)|^4239 ≤ (13485234145967/100000000000000 : ℝ)^3215
        have hw : |(-2188040969/10000000000 : ℝ)|=(2188040969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s8_3 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4343370241/10000000000 : ℝ)*x 0 + (4169628379/10000000000 : ℝ)*x 1 + (904813019/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4343370241/10000000000 : ℝ)^4239 ≤ (33302142048561/100000000000000 : ℝ)^3215 := by
    have hnat : (4343370241 : ℕ)^4239*100000000000000^3215 ≤ 33302142048561^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343370241 10000000000 33302142048561 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4169628379/10000000000 : ℝ)^4239 ≤ (31556999076513/100000000000000 : ℝ)^3215 := by
    have hnat : (4169628379 : ℕ)^4239*100000000000000^3215 ≤ 31556999076513^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169628379 10000000000 31556999076513 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (904813019/2000000000 : ℝ)^4239 ≤ (17570429428437/50000000000000 : ℝ)^3215 := by
    have hnat : (904813019 : ℕ)^4239*50000000000000^3215 ≤ 17570429428437^3215*2000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904813019 2000000000 17570429428437 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4343370241/10000000000 : ℝ), (4169628379/10000000000 : ℝ), (904813019/2000000000 : ℝ)] ![(33302142048561/100000000000000 : ℝ), (31556999076513/100000000000000 : ℝ), (17570429428437/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4343370241/10000000000 : ℝ)|^4239 ≤ (33302142048561/100000000000000 : ℝ)^3215
        have hw : |(4343370241/10000000000 : ℝ)|=(4343370241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4169628379/10000000000 : ℝ)|^4239 ≤ (31556999076513/100000000000000 : ℝ)^3215
        have hw : |(4169628379/10000000000 : ℝ)|=(4169628379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(904813019/2000000000 : ℝ)|^4239 ≤ (17570429428437/50000000000000 : ℝ)^3215
        have hw : |(904813019/2000000000 : ℝ)|=(904813019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s8_4 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2099695879/10000000000 : ℝ)*x 0 + (655395359/1250000000 : ℝ)*x 1 + (2707620939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099695879/10000000000 : ℝ)^4239 ≤ (3192996722573/25000000000000 : ℝ)^3215 := by
    have hnat : (2099695879 : ℕ)^4239*25000000000000^3215 ≤ 3192996722573^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099695879 10000000000 3192996722573 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655395359/1250000000 : ℝ)^4239 ≤ (42685646933211/100000000000000 : ℝ)^3215 := by
    have hnat : (655395359 : ℕ)^4239*100000000000000^3215 ≤ 42685646933211^3215*1250000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655395359 1250000000 42685646933211 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707620939/5000000000 : ℝ)^4239 ≤ (44542366158469/100000000000000 : ℝ)^3215 := by
    have hnat : (2707620939 : ℕ)^4239*100000000000000^3215 ≤ 44542366158469^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707620939 5000000000 44542366158469 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2099695879/10000000000 : ℝ), (655395359/1250000000 : ℝ), (2707620939/5000000000 : ℝ)] ![(3192996722573/25000000000000 : ℝ), (42685646933211/100000000000000 : ℝ), (44542366158469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2099695879/10000000000 : ℝ)|^4239 ≤ (3192996722573/25000000000000 : ℝ)^3215
        have hw : |(-2099695879/10000000000 : ℝ)|=(2099695879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655395359/1250000000 : ℝ)|^4239 ≤ (42685646933211/100000000000000 : ℝ)^3215
        have hw : |(655395359/1250000000 : ℝ)|=(655395359/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707620939/5000000000 : ℝ)|^4239 ≤ (44542366158469/100000000000000 : ℝ)^3215
        have hw : |(2707620939/5000000000 : ℝ)|=(2707620939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s8_5 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (271462281/625000000 : ℝ)*x 0 + (2261401793/5000000000 : ℝ)*x 1 + (4170896381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271462281/625000000 : ℝ)^4239 ≤ (6660481494513/20000000000000 : ℝ)^3215 := by
    have hnat : (271462281 : ℕ)^4239*20000000000000^3215 ≤ 6660481494513^3215*625000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271462281 625000000 6660481494513 20000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2261401793/5000000000 : ℝ)^4239 ≤ (1405117584597/4000000000000 : ℝ)^3215 := by
    have hnat : (2261401793 : ℕ)^4239*4000000000000^3215 ≤ 1405117584597^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261401793 5000000000 1405117584597 4000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4170896381/10000000000 : ℝ)^4239 ≤ (31569652899529/100000000000000 : ℝ)^3215 := by
    have hnat : (4170896381 : ℕ)^4239*100000000000000^3215 ≤ 31569652899529^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170896381 10000000000 31569652899529 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271462281/625000000 : ℝ), (2261401793/5000000000 : ℝ), (4170896381/10000000000 : ℝ)] ![(6660481494513/20000000000000 : ℝ), (1405117584597/4000000000000 : ℝ), (31569652899529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271462281/625000000 : ℝ)|^4239 ≤ (6660481494513/20000000000000 : ℝ)^3215
        have hw : |(271462281/625000000 : ℝ)|=(271462281/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2261401793/5000000000 : ℝ)|^4239 ≤ (1405117584597/4000000000000 : ℝ)^3215
        have hw : |(2261401793/5000000000 : ℝ)|=(2261401793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4170896381/10000000000 : ℝ)|^4239 ≤ (31569652899529/100000000000000 : ℝ)^3215
        have hw : |(4170896381/10000000000 : ℝ)|=(4170896381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1279_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14663/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5497/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2199/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14663/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14663/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5497/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14663/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5497/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14663/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5497/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14663/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5497/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14663/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5497/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14663/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5497/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5497/50000 : ℝ) ^ (2119/512 : ℝ) ≤ (2689045846958077/25000000000000000000 : ℝ) := by
    have hpowers : (5497/50000 : ℝ)^2119 ≤ (2689045846958077/25000000000000000000 : ℝ)^512 := by
      have hnat : (5497 : ℕ)^2119*25000000000000000000^512 ≤ 2689045846958077^512*50000^2119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5497 50000 2689045846958077 25000000000000000000 2119 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5497/50000 : ℝ)) (X := (2689045846958077/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14663/100000 : ℝ) ^ (2119/512 : ℝ) ≤ (35421740364723377/100000000000000000000 : ℝ) := by
    have hpowers : (14663/100000 : ℝ)^2119 ≤ (35421740364723377/100000000000000000000 : ℝ)^512 := by
      have hnat : (14663 : ℕ)^2119*100000000000000000000^512 ≤ 35421740364723377^512*100000^2119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14663 100000 35421740364723377 100000000000000000000 2119 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14663/100000 : ℝ)) (X := (35421740364723377/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502689045846958077/12500000000000000000 : ℝ) ≤ (10000519746740783/10000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (12502689045846958077/12500000000000000000 : ℝ)^512 ≤ (10000519746740783/10000000000000000 : ℝ)^2119 := by
      have hnat : (12502689045846958077 : ℕ)^512*10000000000000000^2119 ≤ 10000519746740783^2119*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502689045846958077 12500000000000000000 10000519746740783 10000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000519746740783/10000000000000000 : ℝ)) (X := (12502689045846958077/12500000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009235584750511137/20000000000000000000 : ℝ) ≤ (5000557785704221/5000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (20009235584750511137/20000000000000000000 : ℝ)^512 ≤ (5000557785704221/5000000000000000 : ℝ)^2119 := by
      have hnat : (20009235584750511137 : ℕ)^512*5000000000000000^2119 ≤ 5000557785704221^2119*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009235584750511137 20000000000000000000 5000557785704221 5000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000557785704221/5000000000000000 : ℝ)) (X := (20009235584750511137/20000000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035421740364723377/50000000000000000000 : ℝ) ≤ (10001711396076101/10000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (50035421740364723377/50000000000000000000 : ℝ)^512 ≤ (10001711396076101/10000000000000000 : ℝ)^2119 := by
      have hnat : (50035421740364723377 : ℕ)^512*10000000000000000^2119 ≤ 10001711396076101^2119*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035421740364723377 50000000000000000000 10001711396076101 10000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001711396076101/10000000000000000 : ℝ)) (X := (50035421740364723377/50000000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2689045846958077/25000000000000000000 : ℝ) ≤ ((2445253730533296449/2446000000000000000 : ℝ)+2*(198608222553/122300000000000 : ℝ)*(5497/50000 : ℝ))^(2119/512 : ℝ) := by
    rw [show (2445253730533296449/2446000000000000000 : ℝ)+2*(198608222553/122300000000000 : ℝ)*(5497/50000 : ℝ)=(10000519746740783/10000000000000000 : ℝ) by norm_num, show 1+2*(2689045846958077/25000000000000000000 : ℝ)=(12502689045846958077/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35421740364723377/100000000000000000000 : ℝ)+(2689045846958077/25000000000000000000 : ℝ) ≤ ((2445253730533296449/2446000000000000000 : ℝ)+(198608222553/122300000000000 : ℝ)*((14663/100000 : ℝ)+(5497/50000 : ℝ)))^(2119/512 : ℝ) := by
    rw [show (2445253730533296449/2446000000000000000 : ℝ)+(198608222553/122300000000000 : ℝ)*((14663/100000 : ℝ)+(5497/50000 : ℝ))=(5000557785704221/5000000000000000 : ℝ) by norm_num, show 1+(35421740364723377/100000000000000000000 : ℝ)+(2689045846958077/25000000000000000000 : ℝ)=(20009235584750511137/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35421740364723377/100000000000000000000 : ℝ) ≤ ((2445253730533296449/2446000000000000000 : ℝ)+2*(198608222553/122300000000000 : ℝ)*(14663/100000 : ℝ))^(2119/512 : ℝ) := by
    rw [show (2445253730533296449/2446000000000000000 : ℝ)+2*(198608222553/122300000000000 : ℝ)*(14663/100000 : ℝ)=(10001711396076101/10000000000000000 : ℝ) by norm_num, show 1+2*(35421740364723377/100000000000000000000 : ℝ)=(50035421740364723377/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2445253730533296449/2446000000000000000 : ℝ)*(X 1 0+X 2 0)+(198608222553/122300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (5497/50000 : ℝ)) (hi := (14663/100000 : ℝ)) (c := (2445253730533296449/2446000000000000000 : ℝ)) (alpha := (198608222553/122300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2445253730533296449/2446000000000000000 : ℝ)*(X 0 1+X 2 1)+(198608222553/122300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (5497/50000 : ℝ)) (hi := (14663/100000 : ℝ)) (c := (2445253730533296449/2446000000000000000 : ℝ)) (alpha := (198608222553/122300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2445253730533296449/2446000000000000000 : ℝ)*(X 0 2+X 1 2)+(198608222553/122300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (5497/50000 : ℝ)) (hi := (14663/100000 : ℝ)) (c := (2445253730533296449/2446000000000000000 : ℝ)) (alpha := (198608222553/122300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-524920759/2500000000 : ℝ)*X 0 0+(1353965481/2500000000 : ℝ)*X 0 1+(1310636497/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674980307/5000000000 : ℝ)*X 1 0+(-547010249/2500000000 : ℝ)*X 1 1+(1310636499/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349960633/10000000000 : ℝ)*X 2 0+(5242545997/10000000000 : ℝ)*X 2 1+(-2188040969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4343370241/10000000000 : ℝ)*X 0 0+(4169628379/10000000000 : ℝ)*X 0 1+(904813019/2000000000 : ℝ)*X 0 2+(4343370241/10000000000 : ℝ)*X 1 0+(4169628379/10000000000 : ℝ)*X 1 1+(904813019/2000000000 : ℝ)*X 1 2+(4343370241/10000000000 : ℝ)*X 2 0+(4169628379/10000000000 : ℝ)*X 2 1+(904813019/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2099695879/10000000000 : ℝ)*X 0 0+(655395359/1250000000 : ℝ)*X 0 1+(2707620939/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((271462281/625000000 : ℝ)*X 0 0+(2261401793/5000000000 : ℝ)*X 0 1+(4170896381/10000000000 : ℝ)*X 0 2+(271462281/625000000 : ℝ)*X 1 0+(2261401793/5000000000 : ℝ)*X 1 1+(4170896381/10000000000 : ℝ)*X 1 2+(271462281/625000000 : ℝ)*X 2 0+(2261401793/5000000000 : ℝ)*X 2 1+(4170896381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (49628376342524392973331009/15287500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (124939449/20000000000000 : ℝ)*(base19) + (119523921/20000000000000 : ℝ)*(base23) + (12724559/50000000000000 : ℝ)*(lower2) + (70371087/100000000000000 : ℝ)*(upper3) + (3527147/5000000000000 : ℝ)*(upper5) + (536951652314549/12500000000000 : ℝ)*(major0) + (536951652314549/12500000000000 : ℝ)*(major1) + (536951652314549/12500000000000 : ℝ)*(major2) + (576982246675591/10000000000000 : ℝ)*(sp0) + (144245881093637/2500000000000 : ℝ)*(sp1) + (5769835270823121/100000000000000 : ℝ)*(sp2) + (705346035074581/25000000000000 : ℝ)*(sp3) + (418802713/3125000000000 : ℝ)*(sp4) + (1580020123/25000000000000 : ℝ)*(sp5) + (44084225943419/1562500000000 : ℝ)*(f.failure) + (2884917934221363/50000000000000 : ℝ)*(f.sum) + (2088501464049/1528750000000000000000000000 : ℝ)*base65 + (495105406727823499/30575000000000000000000000000000 : ℝ)*base68 + (437515017327323499/30575000000000000000000000000000 : ℝ)*base70 + (439982024676023499/30575000000000000000000000000000 : ℝ)*base72 + (4243772031861/1528750000000000000000000000 : ℝ)*base74 + (102034760304723499/30575000000000000000000000000000 : ℝ)*base76 + (532186161617998499/30575000000000000000000000000000 : ℝ)*base78 + (167938543968698499/30575000000000000000000000000000 : ℝ)*base80 + (21956836252731/6115000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1513741/156250000000000000000 : ℝ)*base89 + (1513741/156250000000000000000 : ℝ)*base91 + (1513741/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1279_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14663/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5497/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2199/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14663/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1279_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1279_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10979/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2199/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14663/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1279_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1279_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1279_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14679/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10979/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2199/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14663/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1279_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
