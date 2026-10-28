-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1049_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:53:43.309557+00:00
-- url     : https://prove2.me/submissions/216db275-4c11-4aba-a5e5-ee84fd2da58e

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
theorem support_rectangle_w1049_s3_0 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2207187553/10000000000 : ℝ)*x 0 + (5439562401/10000000000 : ℝ)*x 1 + (261124051/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2207187553/10000000000 : ℝ)^4121 ≤ (535728261441/4000000000000 : ℝ)^3097 := by
    have hnat : (2207187553 : ℕ)^4121*4000000000000^3097 ≤ 535728261441^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207187553 10000000000 535728261441 4000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439562401/10000000000 : ℝ)^4121 ≤ (44476454108383/100000000000000 : ℝ)^3097 := by
    have hnat : (5439562401 : ℕ)^4121*100000000000000^3097 ≤ 44476454108383^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439562401 10000000000 44476454108383 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261124051/500000000 : ℝ)^4121 ≤ (21065169672231/50000000000000 : ℝ)^3097 := by
    have hnat : (261124051 : ℕ)^4121*50000000000000^3097 ≤ 21065169672231^3097*500000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261124051 500000000 21065169672231 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2207187553/10000000000 : ℝ), (5439562401/10000000000 : ℝ), (261124051/500000000 : ℝ)] ![(535728261441/4000000000000 : ℝ), (44476454108383/100000000000000 : ℝ), (21065169672231/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2207187553/10000000000 : ℝ)|^4121 ≤ (535728261441/4000000000000 : ℝ)^3097
        have hw : |(-2207187553/10000000000 : ℝ)|=(2207187553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439562401/10000000000 : ℝ)|^4121 ≤ (44476454108383/100000000000000 : ℝ)^3097
        have hw : |(5439562401/10000000000 : ℝ)|=(5439562401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(261124051/500000000 : ℝ)|^4121 ≤ (21065169672231/50000000000000 : ℝ)^3097
        have hw : |(261124051/500000000 : ℝ)|=(261124051/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s3_1 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356137007/10000000000 : ℝ)*x 0 + (-92735957/400000000 : ℝ)*x 1 + (5222481107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356137007/10000000000 : ℝ)^4121 ≤ (43571097834487/100000000000000 : ℝ)^3097 := by
    have hnat : (5356137007 : ℕ)^4121*100000000000000^3097 ≤ 43571097834487^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356137007 10000000000 43571097834487 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (92735957/400000000 : ℝ)^4121 ≤ (14298561866193/100000000000000 : ℝ)^3097 := by
    have hnat : (92735957 : ℕ)^4121*100000000000000^3097 ≤ 14298561866193^3097*400000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92735957 400000000 14298561866193 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5222481107/10000000000 : ℝ)^4121 ≤ (42130340278359/100000000000000 : ℝ)^3097 := by
    have hnat : (5222481107 : ℕ)^4121*100000000000000^3097 ≤ 42130340278359^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5222481107 10000000000 42130340278359 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356137007/10000000000 : ℝ), (-92735957/400000000 : ℝ), (5222481107/10000000000 : ℝ)] ![(43571097834487/100000000000000 : ℝ), (14298561866193/100000000000000 : ℝ), (42130340278359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356137007/10000000000 : ℝ)|^4121 ≤ (43571097834487/100000000000000 : ℝ)^3097
        have hw : |(5356137007/10000000000 : ℝ)|=(5356137007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-92735957/400000000 : ℝ)|^4121 ≤ (14298561866193/100000000000000 : ℝ)^3097
        have hw : |(-92735957/400000000 : ℝ)|=(92735957/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5222481107/10000000000 : ℝ)|^4121 ≤ (42130340278359/100000000000000 : ℝ)^3097
        have hw : |(5222481107/10000000000 : ℝ)|=(5222481107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s3_2 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356137009/10000000000 : ℝ)*x 0 + (2611240609/5000000000 : ℝ)*x 1 + (-1159199389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356137009/10000000000 : ℝ)^4121 ≤ (5446387232017/12500000000000 : ℝ)^3097 := by
    have hnat : (5356137009 : ℕ)^4121*12500000000000^3097 ≤ 5446387232017^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356137009 10000000000 5446387232017 12500000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2611240609/5000000000 : ℝ)^4121 ≤ (21065170734941/50000000000000 : ℝ)^3097 := by
    have hnat : (2611240609 : ℕ)^4121*50000000000000^3097 ≤ 21065170734941^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611240609 5000000000 21065170734941 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1159199389/5000000000 : ℝ)^4121 ≤ (1787320082477/12500000000000 : ℝ)^3097 := by
    have hnat : (1159199389 : ℕ)^4121*12500000000000^3097 ≤ 1787320082477^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1159199389 5000000000 1787320082477 12500000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356137009/10000000000 : ℝ), (2611240609/5000000000 : ℝ), (-1159199389/5000000000 : ℝ)] ![(5446387232017/12500000000000 : ℝ), (21065170734941/50000000000000 : ℝ), (1787320082477/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356137009/10000000000 : ℝ)|^4121 ≤ (5446387232017/12500000000000 : ℝ)^3097
        have hw : |(5356137009/10000000000 : ℝ)|=(5356137009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2611240609/5000000000 : ℝ)|^4121 ≤ (21065170734941/50000000000000 : ℝ)^3097
        have hw : |(2611240609/5000000000 : ℝ)|=(2611240609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1159199389/5000000000 : ℝ)|^4121 ≤ (1787320082477/12500000000000 : ℝ)^3097
        have hw : |(-1159199389/5000000000 : ℝ)|=(1159199389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s3_3 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1093750223/2500000000 : ℝ)*x 0 + (833642143/2000000000 : ℝ)*x 1 + (71753501/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093750223/2500000000 : ℝ)^4121 ≤ (166433308399/500000000000 : ℝ)^3097 := by
    have hnat : (1093750223 : ℕ)^4121*500000000000^3097 ≤ 166433308399^3097*2500000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093750223 2500000000 166433308399 500000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833642143/2000000000 : ℝ)^4121 ≤ (3901205827117/12500000000000 : ℝ)^3097 := by
    have hnat : (833642143 : ℕ)^4121*12500000000000^3097 ≤ 3901205827117^3097*2000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833642143 2000000000 3901205827117 12500000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (71753501/156250000 : ℝ)^4121 ≤ (35503691693359/100000000000000 : ℝ)^3097 := by
    have hnat : (71753501 : ℕ)^4121*100000000000000^3097 ≤ 35503691693359^3097*156250000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71753501 156250000 35503691693359 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093750223/2500000000 : ℝ), (833642143/2000000000 : ℝ), (71753501/156250000 : ℝ)] ![(166433308399/500000000000 : ℝ), (3901205827117/12500000000000 : ℝ), (35503691693359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093750223/2500000000 : ℝ)|^4121 ≤ (166433308399/500000000000 : ℝ)^3097
        have hw : |(1093750223/2500000000 : ℝ)|=(1093750223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(833642143/2000000000 : ℝ)|^4121 ≤ (3901205827117/12500000000000 : ℝ)^3097
        have hw : |(833642143/2000000000 : ℝ)|=(833642143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(71753501/156250000 : ℝ)|^4121 ≤ (35503691693359/100000000000000 : ℝ)^3097
        have hw : |(71753501/156250000 : ℝ)|=(71753501/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s3_4 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2207211111/10000000000 : ℝ)*x 0 + (2611690911/5000000000 : ℝ)*x 1 + (2719328057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2207211111/10000000000 : ℝ)^4121 ≤ (3348349187883/25000000000000 : ℝ)^3097 := by
    have hnat : (2207211111 : ℕ)^4121*25000000000000^3097 ≤ 3348349187883^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207211111 10000000000 3348349187883 25000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2611690911/5000000000 : ℝ)^4121 ≤ (8428001845501/20000000000000 : ℝ)^3097 := by
    have hnat : (2611690911 : ℕ)^4121*20000000000000^3097 ≤ 8428001845501^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611690911 5000000000 8428001845501 20000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719328057/5000000000 : ℝ)^4121 ≤ (44466594006801/100000000000000 : ℝ)^3097 := by
    have hnat : (2719328057 : ℕ)^4121*100000000000000^3097 ≤ 44466594006801^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719328057 5000000000 44466594006801 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2207211111/10000000000 : ℝ), (2611690911/5000000000 : ℝ), (2719328057/5000000000 : ℝ)] ![(3348349187883/25000000000000 : ℝ), (8428001845501/20000000000000 : ℝ), (44466594006801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2207211111/10000000000 : ℝ)|^4121 ≤ (3348349187883/25000000000000 : ℝ)^3097
        have hw : |(-2207211111/10000000000 : ℝ)|=(2207211111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2611690911/5000000000 : ℝ)|^4121 ≤ (8428001845501/20000000000000 : ℝ)^3097
        have hw : |(2611690911/5000000000 : ℝ)|=(2611690911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719328057/5000000000 : ℝ)|^4121 ≤ (44466594006801/100000000000000 : ℝ)^3097
        have hw : |(2719328057/5000000000 : ℝ)|=(2719328057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s3_5 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5301527679/10000000000 : ℝ)*x 0 + (-2102224589/10000000000 : ℝ)*x 1 + (5438655483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301527679/10000000000 : ℝ)^4121 ≤ (42980977275677/100000000000000 : ℝ)^3097 := by
    have hnat : (5301527679 : ℕ)^4121*100000000000000^3097 ≤ 42980977275677^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301527679 10000000000 42980977275677 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2102224589/10000000000 : ℝ)^4121 ≤ (12552435570817/100000000000000 : ℝ)^3097 := by
    have hnat : (2102224589 : ℕ)^4121*100000000000000^3097 ≤ 12552435570817^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102224589 10000000000 12552435570817 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5438655483/10000000000 : ℝ)^4121 ≤ (277916169637/625000000000 : ℝ)^3097 := by
    have hnat : (5438655483 : ℕ)^4121*625000000000^3097 ≤ 277916169637^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438655483 10000000000 277916169637 625000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301527679/10000000000 : ℝ), (-2102224589/10000000000 : ℝ), (5438655483/10000000000 : ℝ)] ![(42980977275677/100000000000000 : ℝ), (12552435570817/100000000000000 : ℝ), (277916169637/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301527679/10000000000 : ℝ)|^4121 ≤ (42980977275677/100000000000000 : ℝ)^3097
        have hw : |(5301527679/10000000000 : ℝ)|=(5301527679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2102224589/10000000000 : ℝ)|^4121 ≤ (12552435570817/100000000000000 : ℝ)^3097
        have hw : |(-2102224589/10000000000 : ℝ)|=(2102224589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5438655483/10000000000 : ℝ)|^4121 ≤ (277916169637/625000000000 : ℝ)^3097
        have hw : |(5438655483/10000000000 : ℝ)|=(5438655483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s3_6 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5301527341/10000000000 : ℝ)*x 0 + (2719327983/5000000000 : ℝ)*x 1 + (-1051112193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301527341/10000000000 : ℝ)^4121 ≤ (42980973629369/100000000000000 : ℝ)^3097 := by
    have hnat : (5301527341 : ℕ)^4121*100000000000000^3097 ≤ 42980973629369^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301527341 10000000000 42980973629369 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719327983/5000000000 : ℝ)^4121 ≤ (8893318479331/20000000000000 : ℝ)^3097 := by
    have hnat : (2719327983 : ℕ)^4121*20000000000000^3097 ≤ 8893318479331^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719327983 5000000000 8893318479331 20000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051112193/5000000000 : ℝ)^4121 ≤ (12552433957921/100000000000000 : ℝ)^3097 := by
    have hnat : (1051112193 : ℕ)^4121*100000000000000^3097 ≤ 12552433957921^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051112193 5000000000 12552433957921 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301527341/10000000000 : ℝ), (2719327983/5000000000 : ℝ), (-1051112193/5000000000 : ℝ)] ![(42980973629369/100000000000000 : ℝ), (8893318479331/20000000000000 : ℝ), (12552433957921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301527341/10000000000 : ℝ)|^4121 ≤ (42980973629369/100000000000000 : ℝ)^3097
        have hw : |(5301527341/10000000000 : ℝ)|=(5301527341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719327983/5000000000 : ℝ)|^4121 ≤ (8893318479331/20000000000000 : ℝ)^3097
        have hw : |(2719327983/5000000000 : ℝ)|=(2719327983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1051112193/5000000000 : ℝ)|^4121 ≤ (12552433957921/100000000000000 : ℝ)^3097
        have hw : |(-1051112193/5000000000 : ℝ)|=(1051112193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s3_7 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (437504649/1000000000 : ℝ)*x 0 + (4590463953/10000000000 : ℝ)*x 1 + (833996309/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437504649/1000000000 : ℝ)^4121 ≤ (33287123316203/100000000000000 : ℝ)^3097 := by
    have hnat : (437504649 : ℕ)^4121*100000000000000^3097 ≤ 33287123316203^3097*1000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437504649 1000000000 33287123316203 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4590463953/10000000000 : ℝ)^4121 ≤ (8871396403831/25000000000000 : ℝ)^3097 := by
    have hnat : (4590463953 : ℕ)^4121*25000000000000^3097 ≤ 8871396403831^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4590463953 10000000000 8871396403831 25000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (833996309/2000000000 : ℝ)^4121 ≤ (7806822765099/25000000000000 : ℝ)^3097 := by
    have hnat : (833996309 : ℕ)^4121*25000000000000^3097 ≤ 7806822765099^3097*2000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833996309 2000000000 7806822765099 25000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(437504649/1000000000 : ℝ), (4590463953/10000000000 : ℝ), (833996309/2000000000 : ℝ)] ![(33287123316203/100000000000000 : ℝ), (8871396403831/25000000000000 : ℝ), (7806822765099/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(437504649/1000000000 : ℝ)|^4121 ≤ (33287123316203/100000000000000 : ℝ)^3097
        have hw : |(437504649/1000000000 : ℝ)|=(437504649/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4590463953/10000000000 : ℝ)|^4121 ≤ (8871396403831/25000000000000 : ℝ)^3097
        have hw : |(4590463953/10000000000 : ℝ)|=(4590463953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(833996309/2000000000 : ℝ)|^4121 ≤ (7806822765099/25000000000000 : ℝ)^3097
        have hw : |(833996309/2000000000 : ℝ)|=(833996309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1049_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147662441/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8399/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8627/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10339/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14931/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8399/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8627/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8399/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8627/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8399/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8627/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8399/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8627/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8399/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8627/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8399/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8627/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8627/100000 : ℝ) ^ (8241/2048 : ℝ) ≤ (5223706967241149/100000000000000000000 : ℝ) := by
    have hpowers : (8627/100000 : ℝ)^8241 ≤ (5223706967241149/100000000000000000000 : ℝ)^2048 := by
      have hnat : (8627 : ℕ)^8241*100000000000000000000^2048 ≤ 5223706967241149^2048*100000^8241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8627 100000 5223706967241149 100000000000000000000 8241 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8627/100000 : ℝ)) (X := (5223706967241149/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (8399/50000 : ℝ) ^ (8241/2048 : ℝ) ≤ (7629463329519561/10000000000000000000 : ℝ) := by
    have hpowers : (8399/50000 : ℝ)^8241 ≤ (7629463329519561/10000000000000000000 : ℝ)^2048 := by
      have hnat : (8399 : ℕ)^8241*10000000000000000000^2048 ≤ 7629463329519561^2048*50000^8241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8399 50000 7629463329519561 10000000000000000000 8241 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8399/50000 : ℝ)) (X := (7629463329519561/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005223706967241149/50000000000000000000 : ℝ) ≤ (10000259622180167/10000000000000000 : ℝ) ^ (8241/2048 : ℝ) := by
    have hpowers : (50005223706967241149/50000000000000000000 : ℝ)^2048 ≤ (10000259622180167/10000000000000000 : ℝ)^8241 := by
      have hnat : (50005223706967241149 : ℕ)^2048*10000000000000000^8241 ≤ 10000259622180167^8241*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005223706967241149 50000000000000000000 10000259622180167 10000000000000000 2048 8241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000259622180167/10000000000000000 : ℝ)) (X := (50005223706967241149/50000000000000000000 : ℝ)) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100081518340262436759/100000000000000000000 : ℝ) ≤ (10002025220829867/10000000000000000 : ℝ) ^ (8241/2048 : ℝ) := by
    have hpowers : (100081518340262436759/100000000000000000000 : ℝ)^2048 ≤ (10002025220829867/10000000000000000 : ℝ)^8241 := by
      have hnat : (100081518340262436759 : ℕ)^2048*10000000000000000^8241 ≤ 10002025220829867^8241*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100081518340262436759 100000000000000000000 10002025220829867 10000000000000000 2048 8241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002025220829867/10000000000000000 : ℝ)) (X := (100081518340262436759/100000000000000000000 : ℝ)) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5007629463329519561/5000000000000000000 : ℝ) ≤ (10003790819479567/10000000000000000 : ℝ) ^ (8241/2048 : ℝ) := by
    have hpowers : (5007629463329519561/5000000000000000000 : ℝ)^2048 ≤ (10003790819479567/10000000000000000 : ℝ)^8241 := by
      have hnat : (5007629463329519561 : ℕ)^2048*10000000000000000^8241 ≤ 10003790819479567^8241*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5007629463329519561 5000000000000000000 10003790819479567 10000000000000000 2048 8241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003790819479567/10000000000000000 : ℝ)) (X := (5007629463329519561/5000000000000000000 : ℝ)) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5223706967241149/100000000000000000000 : ℝ) ≤ ((81681657733732220757/81710000000000000000 : ℝ)+2*(17655986497/8171000000000 : ℝ)*(8627/100000 : ℝ))^(8241/2048 : ℝ) := by
    rw [show (81681657733732220757/81710000000000000000 : ℝ)+2*(17655986497/8171000000000 : ℝ)*(8627/100000 : ℝ)=(10000259622180167/10000000000000000 : ℝ) by norm_num, show 1+2*(5223706967241149/100000000000000000000 : ℝ)=(50005223706967241149/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7629463329519561/10000000000000000000 : ℝ)+(5223706967241149/100000000000000000000 : ℝ) ≤ ((81681657733732220757/81710000000000000000 : ℝ)+(17655986497/8171000000000 : ℝ)*((8399/50000 : ℝ)+(8627/100000 : ℝ)))^(8241/2048 : ℝ) := by
    rw [show (81681657733732220757/81710000000000000000 : ℝ)+(17655986497/8171000000000 : ℝ)*((8399/50000 : ℝ)+(8627/100000 : ℝ))=(10002025220829867/10000000000000000 : ℝ) by norm_num, show 1+(7629463329519561/10000000000000000000 : ℝ)+(5223706967241149/100000000000000000000 : ℝ)=(100081518340262436759/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7629463329519561/10000000000000000000 : ℝ) ≤ ((81681657733732220757/81710000000000000000 : ℝ)+2*(17655986497/8171000000000 : ℝ)*(8399/50000 : ℝ))^(8241/2048 : ℝ) := by
    rw [show (81681657733732220757/81710000000000000000 : ℝ)+2*(17655986497/8171000000000 : ℝ)*(8399/50000 : ℝ)=(10003790819479567/10000000000000000 : ℝ) by norm_num, show 1+2*(7629463329519561/10000000000000000000 : ℝ)=(5007629463329519561/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (81681657733732220757/81710000000000000000 : ℝ)*(X 1 0+X 2 0)+(17655986497/8171000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8241/2048 : ℝ)) (lo := (8627/100000 : ℝ)) (hi := (8399/50000 : ℝ)) (c := (81681657733732220757/81710000000000000000 : ℝ)) (alpha := (17655986497/8171000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (81681657733732220757/81710000000000000000 : ℝ)*(X 0 1+X 2 1)+(17655986497/8171000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8241/2048 : ℝ)) (lo := (8627/100000 : ℝ)) (hi := (8399/50000 : ℝ)) (c := (81681657733732220757/81710000000000000000 : ℝ)) (alpha := (17655986497/8171000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (81681657733732220757/81710000000000000000 : ℝ)*(X 0 2+X 1 2)+(17655986497/8171000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8241/2048 : ℝ)) (lo := (8627/100000 : ℝ)) (hi := (8399/50000 : ℝ)) (c := (81681657733732220757/81710000000000000000 : ℝ)) (alpha := (17655986497/8171000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2207187553/10000000000 : ℝ)*X 0 0+(5439562401/10000000000 : ℝ)*X 0 1+(261124051/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356137007/10000000000 : ℝ)*X 1 0+(-92735957/400000000 : ℝ)*X 1 1+(5222481107/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5356137009/10000000000 : ℝ)*X 2 0+(2611240609/5000000000 : ℝ)*X 2 1+(-1159199389/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1093750223/2500000000 : ℝ)*X 0 0+(833642143/2000000000 : ℝ)*X 0 1+(71753501/156250000 : ℝ)*X 0 2+(1093750223/2500000000 : ℝ)*X 1 0+(833642143/2000000000 : ℝ)*X 1 1+(71753501/156250000 : ℝ)*X 1 2+(1093750223/2500000000 : ℝ)*X 2 0+(833642143/2000000000 : ℝ)*X 2 1+(71753501/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2207211111/10000000000 : ℝ)*X 0 0+(2611690911/5000000000 : ℝ)*X 0 1+(2719328057/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301527679/10000000000 : ℝ)*X 1 0+(-2102224589/10000000000 : ℝ)*X 1 1+(5438655483/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301527341/10000000000 : ℝ)*X 2 0+(2719327983/5000000000 : ℝ)*X 2 1+(-1051112193/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((437504649/1000000000 : ℝ)*X 0 0+(4590463953/10000000000 : ℝ)*X 0 1+(833996309/2000000000 : ℝ)*X 0 2+(437504649/1000000000 : ℝ)*X 1 0+(4590463953/10000000000 : ℝ)*X 1 1+(833996309/2000000000 : ℝ)*X 1 2+(437504649/1000000000 : ℝ)*X 2 0+(4590463953/10000000000 : ℝ)*X 2 1+(833996309/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1475861727298069148600873103/1021375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21259471/4000000000000 : ℝ)*(base19) + (388374579/100000000000000 : ℝ)*(base23) + (7757417/10000000000000 : ℝ)*(lower2) + (10085311/50000000000000 : ℝ)*(upper3) + (49005397/100000000000000 : ℝ)*(upper5) + (1741253828428993/50000000000000 : ℝ)*(major0) + (1741253828428993/50000000000000 : ℝ)*(major1) + (870626914214497/25000000000000 : ℝ)*(major2) + (4606577779728931/100000000000000 : ℝ)*(sp0) + (4606589915081793/100000000000000 : ℝ)*(sp1) + (4606590058193989/100000000000000 : ℝ)*(sp2) + (471684096322227/20000000000000 : ℝ)*(sp3) + (12666839637/100000000000000 : ℝ)*(sp4) + (2168685207/50000000000000 : ℝ)*(sp7) + (47168496379631/2000000000000 : ℝ)*(f.failure) + (575823805821071/12500000000000 : ℝ)*(f.sum) + (56418705399/163420000000000000000000000 : ℝ)*base65 + (73495617714470792299/4085500000000000000000000000000000 : ℝ)*base68 + (9557052043441714229/2042750000000000000000000000000000 : ℝ)*base69 + (29936395926495292299/4085500000000000000000000000000000 : ℝ)*base72 + (5888793313549/4085500000000000000000000000 : ℝ)*base73 + (7974246429764035771/2042750000000000000000000000000000 : ℝ)*base76 + (67965216858890292299/4085500000000000000000000000000000 : ℝ)*base78 + (71296854221614292299/4085500000000000000000000000000000 : ℝ)*base80 + (8336749813/2042750000000000000000000000 : ℝ)*base81 + (4139271/200000000000000000000 : ℝ)*base89 + (4139271/200000000000000000000 : ℝ)*base91 + (139271/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9672914283188718276295444527/2042750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (938000953/100000000000000 : ℝ)*(base19) + (632575971/100000000000000 : ℝ)*(base23) + (3278959/100000000000000 : ℝ)*(lower4) + (107998509/50000000000000 : ℝ)*(upper5) + (3511733465205537/100000000000000 : ℝ)*(major0) + (3511733465205537/100000000000000 : ℝ)*(major1) + (3511733465205537/100000000000000 : ℝ)*(major2) + (4262591639/100000000000000 : ℝ)*(sp0) + (10495504463/100000000000000 : ℝ)*(sp1) + (281107521/3125000000000 : ℝ)*(sp2) + (2322622690406399/50000000000000 : ℝ)*(sp4) + (4645238209899021/100000000000000 : ℝ)*(sp5) + (4645240015387793/100000000000000 : ℝ)*(sp6) + (1189108564582627/50000000000000 : ℝ)*(sp7) + (1189108564582627/50000000000000 : ℝ)*(f.failure) + (1161312410851109/25000000000000 : ℝ)*(f.sum) + (9609213755943/1634200000000000000000000000 : ℝ)*base65 + (66546509760594268491/8171000000000000000000000000000000 : ℝ)*base68 + (65744639891769268491/8171000000000000000000000000000000 : ℝ)*base70 + (15318512714807268491/8171000000000000000000000000000000 : ℝ)*base72 + (75568863349/4085500000000000000000000000 : ℝ)*base74 + (58140085740141268491/8171000000000000000000000000000000 : ℝ)*base76 + (2365868509861731509/8171000000000000000000000000000000 : ℝ)*base77 + (4257328988563268491/8171000000000000000000000000000000 : ℝ)*base80 + (1291177277057/1021375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (987493/5000000000000000000000 : ℝ)*base90 + (987493/5000000000000000000000 : ℝ)*base92 + (987493/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1049_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147662441/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8399/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8627/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10339/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14931/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1049_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1049_s4_0 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2211036033/10000000000 : ℝ)*x 0 + (1081354597/2000000000 : ℝ)*x 1 + (656594649/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2211036033/10000000000 : ℝ)^4121 ≤ (1342428940461/10000000000000 : ℝ)^3097 := by
    have hnat : (2211036033 : ℕ)^4121*10000000000000^3097 ≤ 1342428940461^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211036033 10000000000 1342428940461 10000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081354597/2000000000 : ℝ)^4121 ≤ (22060031160407/50000000000000 : ℝ)^3097 := by
    have hnat : (1081354597 : ℕ)^4121*50000000000000^3097 ≤ 22060031160407^3097*2000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081354597 2000000000 22060031160407 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (656594649/1250000000 : ℝ)^4121 ≤ (21227824126903/50000000000000 : ℝ)^3097 := by
    have hnat : (656594649 : ℕ)^4121*50000000000000^3097 ≤ 21227824126903^3097*1250000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656594649 1250000000 21227824126903 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2211036033/10000000000 : ℝ), (1081354597/2000000000 : ℝ), (656594649/1250000000 : ℝ)] ![(1342428940461/10000000000000 : ℝ), (22060031160407/50000000000000 : ℝ), (21227824126903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2211036033/10000000000 : ℝ)|^4121 ≤ (1342428940461/10000000000000 : ℝ)^3097
        have hw : |(-2211036033/10000000000 : ℝ)|=(2211036033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081354597/2000000000 : ℝ)|^4121 ≤ (22060031160407/50000000000000 : ℝ)^3097
        have hw : |(1081354597/2000000000 : ℝ)|=(1081354597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(656594649/1250000000 : ℝ)|^4121 ≤ (21227824126903/50000000000000 : ℝ)^3097
        have hw : |(656594649/1250000000 : ℝ)|=(656594649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s4_1 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674015111/5000000000 : ℝ)*x 0 + (-1144694577/5000000000 : ℝ)*x 1 + (5252757289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674015111/5000000000 : ℝ)^4121 ≤ (43483367826433/100000000000000 : ℝ)^3097 := by
    have hnat : (2674015111 : ℕ)^4121*100000000000000^3097 ≤ 43483367826433^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674015111 5000000000 43483367826433 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1144694577/5000000000 : ℝ)^4121 ≤ (3515245717131/25000000000000 : ℝ)^3097 := by
    have hnat : (1144694577 : ℕ)^4121*25000000000000^3097 ≤ 3515245717131^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144694577 5000000000 3515245717131 25000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252757289/10000000000 : ℝ)^4121 ≤ (42455649297039/100000000000000 : ℝ)^3097 := by
    have hnat : (5252757289 : ℕ)^4121*100000000000000^3097 ≤ 42455649297039^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252757289 10000000000 42455649297039 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674015111/5000000000 : ℝ), (-1144694577/5000000000 : ℝ), (5252757289/10000000000 : ℝ)] ![(43483367826433/100000000000000 : ℝ), (3515245717131/25000000000000 : ℝ), (42455649297039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674015111/5000000000 : ℝ)|^4121 ≤ (43483367826433/100000000000000 : ℝ)^3097
        have hw : |(2674015111/5000000000 : ℝ)|=(2674015111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1144694577/5000000000 : ℝ)|^4121 ≤ (3515245717131/25000000000000 : ℝ)^3097
        have hw : |(-1144694577/5000000000 : ℝ)|=(1144694577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252757289/10000000000 : ℝ)|^4121 ≤ (42455649297039/100000000000000 : ℝ)^3097
        have hw : |(5252757289/10000000000 : ℝ)|=(5252757289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s4_2 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668503767/1250000000 : ℝ)*x 0 + (5252757411/10000000000 : ℝ)*x 1 + (-1144694553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668503767/1250000000 : ℝ)^4121 ≤ (43483366895991/100000000000000 : ℝ)^3097 := by
    have hnat : (668503767 : ℕ)^4121*100000000000000^3097 ≤ 43483366895991^3097*1250000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668503767 1250000000 43483366895991 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5252757411/10000000000 : ℝ)^4121 ≤ (42455650609147/100000000000000 : ℝ)^3097 := by
    have hnat : (5252757411 : ℕ)^4121*100000000000000^3097 ≤ 42455650609147^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252757411 10000000000 42455650609147 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1144694553/5000000000 : ℝ)^4121 ≤ (14060982476241/100000000000000 : ℝ)^3097 := by
    have hnat : (1144694553 : ℕ)^4121*100000000000000^3097 ≤ 14060982476241^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144694553 5000000000 14060982476241 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668503767/1250000000 : ℝ), (5252757411/10000000000 : ℝ), (-1144694553/5000000000 : ℝ)] ![(43483366895991/100000000000000 : ℝ), (42455650609147/100000000000000 : ℝ), (14060982476241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668503767/1250000000 : ℝ)|^4121 ≤ (43483366895991/100000000000000 : ℝ)^3097
        have hw : |(668503767/1250000000 : ℝ)|=(668503767/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5252757411/10000000000 : ℝ)|^4121 ≤ (42455650609147/100000000000000 : ℝ)^3097
        have hw : |(5252757411/10000000000 : ℝ)|=(5252757411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1144694553/5000000000 : ℝ)|^4121 ≤ (14060982476241/100000000000000 : ℝ)^3097
        have hw : |(-1144694553/5000000000 : ℝ)|=(1144694553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s4_3 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2188644367/5000000000 : ℝ)*x 0 + (2114750559/5000000000 : ℝ)*x 1 + (4530331977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188644367/5000000000 : ℝ)^4121 ≤ (33309825867397/100000000000000 : ℝ)^3097 := by
    have hnat : (2188644367 : ℕ)^4121*100000000000000^3097 ≤ 33309825867397^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188644367 5000000000 33309825867397 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114750559/5000000000 : ℝ)^4121 ≤ (10182968711/32000000000 : ℝ)^3097 := by
    have hnat : (2114750559 : ℕ)^4121*32000000000^3097 ≤ 10182968711^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114750559 5000000000 10182968711 32000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4530331977/10000000000 : ℝ)^4121 ≤ (3486839689081/10000000000000 : ℝ)^3097 := by
    have hnat : (4530331977 : ℕ)^4121*10000000000000^3097 ≤ 3486839689081^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530331977 10000000000 3486839689081 10000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188644367/5000000000 : ℝ), (2114750559/5000000000 : ℝ), (4530331977/10000000000 : ℝ)] ![(33309825867397/100000000000000 : ℝ), (10182968711/32000000000 : ℝ), (3486839689081/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188644367/5000000000 : ℝ)|^4121 ≤ (33309825867397/100000000000000 : ℝ)^3097
        have hw : |(2188644367/5000000000 : ℝ)|=(2188644367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2114750559/5000000000 : ℝ)|^4121 ≤ (10182968711/32000000000 : ℝ)^3097
        have hw : |(2114750559/5000000000 : ℝ)|=(2114750559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4530331977/10000000000 : ℝ)|^4121 ≤ (3486839689081/10000000000000 : ℝ)^3097
        have hw : |(4530331977/10000000000 : ℝ)|=(4530331977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s4_4 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-44220889/200000000 : ℝ)*x 0 + (21012847/40000000 : ℝ)*x 1 + (216252659/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44220889/200000000 : ℝ)^4121 ≤ (3356089351371/25000000000000 : ℝ)^3097 := by
    have hnat : (44220889 : ℕ)^4121*25000000000000^3097 ≤ 3356089351371^3097*200000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44220889 200000000 3356089351371 25000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21012847/40000000 : ℝ)^4121 ≤ (4246053708541/10000000000000 : ℝ)^3097 := by
    have hnat : (21012847 : ℕ)^4121*10000000000000^3097 ≤ 4246053708541^3097*40000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21012847 40000000 4246053708541 10000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216252659/400000000 : ℝ)^4121 ≤ (22057552747691/50000000000000 : ℝ)^3097 := by
    have hnat : (216252659 : ℕ)^4121*50000000000000^3097 ≤ 22057552747691^3097*400000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216252659 400000000 22057552747691 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-44220889/200000000 : ℝ), (21012847/40000000 : ℝ), (216252659/400000000 : ℝ)] ![(3356089351371/25000000000000 : ℝ), (4246053708541/10000000000000 : ℝ), (22057552747691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-44220889/200000000 : ℝ)|^4121 ≤ (3356089351371/25000000000000 : ℝ)^3097
        have hw : |(-44220889/200000000 : ℝ)|=(44220889/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21012847/40000000 : ℝ)|^4121 ≤ (4246053708541/10000000000000 : ℝ)^3097
        have hw : |(21012847/40000000 : ℝ)|=(21012847/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216252659/400000000 : ℝ)|^4121 ≤ (22057552747691/50000000000000 : ℝ)^3097
        have hw : |(216252659/400000000 : ℝ)|=(216252659/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s4_5 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061858269/2000000000 : ℝ)*x 0 + (-533957493/2500000000 : ℝ)*x 1 + (675789557/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061858269/2000000000 : ℝ)^4121 ≤ (43064751150011/100000000000000 : ℝ)^3097 := by
    have hnat : (1061858269 : ℕ)^4121*100000000000000^3097 ≤ 43064751150011^3097*2000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061858269 2000000000 43064751150011 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (533957493/2500000000 : ℝ)^4121 ≤ (12820143550289/100000000000000 : ℝ)^3097 := by
    have hnat : (533957493 : ℕ)^4121*100000000000000^3097 ≤ 12820143550289^3097*2500000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533957493 2500000000 12820143550289 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675789557/1250000000 : ℝ)^4121 ≤ (22057552644541/50000000000000 : ℝ)^3097 := by
    have hnat : (675789557 : ℕ)^4121*50000000000000^3097 ≤ 22057552644541^3097*1250000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675789557 1250000000 22057552644541 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061858269/2000000000 : ℝ), (-533957493/2500000000 : ℝ), (675789557/1250000000 : ℝ)] ![(43064751150011/100000000000000 : ℝ), (12820143550289/100000000000000 : ℝ), (22057552644541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061858269/2000000000 : ℝ)|^4121 ≤ (43064751150011/100000000000000 : ℝ)^3097
        have hw : |(1061858269/2000000000 : ℝ)|=(1061858269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-533957493/2500000000 : ℝ)|^4121 ≤ (12820143550289/100000000000000 : ℝ)^3097
        have hw : |(-533957493/2500000000 : ℝ)|=(533957493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675789557/1250000000 : ℝ)|^4121 ≤ (22057552644541/50000000000000 : ℝ)^3097
        have hw : |(675789557/1250000000 : ℝ)|=(675789557/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s4_6 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5309291373/10000000000 : ℝ)*x 0 + (5406316407/10000000000 : ℝ)*x 1 + (-2135829999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309291373/10000000000 : ℝ)^4121 ≤ (21532375726109/50000000000000 : ℝ)^3097 := by
    have hnat : (5309291373 : ℕ)^4121*50000000000000^3097 ≤ 21532375726109^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309291373 10000000000 21532375726109 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406316407/10000000000 : ℝ)^4121 ≤ (44115104757043/100000000000000 : ℝ)^3097 := by
    have hnat : (5406316407 : ℕ)^4121*100000000000000^3097 ≤ 44115104757043^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406316407 10000000000 44115104757043 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2135829999/10000000000 : ℝ)^4121 ≤ (641007188297/5000000000000 : ℝ)^3097 := by
    have hnat : (2135829999 : ℕ)^4121*5000000000000^3097 ≤ 641007188297^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135829999 10000000000 641007188297 5000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309291373/10000000000 : ℝ), (5406316407/10000000000 : ℝ), (-2135829999/10000000000 : ℝ)] ![(21532375726109/50000000000000 : ℝ), (44115104757043/100000000000000 : ℝ), (641007188297/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309291373/10000000000 : ℝ)|^4121 ≤ (21532375726109/50000000000000 : ℝ)^3097
        have hw : |(5309291373/10000000000 : ℝ)|=(5309291373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406316407/10000000000 : ℝ)|^4121 ≤ (44115104757043/100000000000000 : ℝ)^3097
        have hw : |(5406316407/10000000000 : ℝ)|=(5406316407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2135829999/10000000000 : ℝ)|^4121 ≤ (641007188297/5000000000000 : ℝ)^3097
        have hw : |(-2135829999/10000000000 : ℝ)|=(2135829999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s4_7 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4377305429/10000000000 : ℝ)*x 0 + (4529443729/10000000000 : ℝ)*x 1 + (4131243/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377305429/10000000000 : ℝ)^4121 ≤ (6661998983487/20000000000000 : ℝ)^3097 := by
    have hnat : (4377305429 : ℕ)^4121*20000000000000^3097 ≤ 6661998983487^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377305429 10000000000 6661998983487 20000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4529443729/10000000000 : ℝ)^4121 ≤ (34859300198141/100000000000000 : ℝ)^3097 := by
    have hnat : (4529443729 : ℕ)^4121*100000000000000^3097 ≤ 34859300198141^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529443729 10000000000 34859300198141 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4131243/9765625 : ℝ)^4121 ≤ (3978838109657/12500000000000 : ℝ)^3097 := by
    have hnat : (4131243 : ℕ)^4121*12500000000000^3097 ≤ 3978838109657^3097*9765625^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131243 9765625 3978838109657 12500000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377305429/10000000000 : ℝ), (4529443729/10000000000 : ℝ), (4131243/9765625 : ℝ)] ![(6661998983487/20000000000000 : ℝ), (34859300198141/100000000000000 : ℝ), (3978838109657/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377305429/10000000000 : ℝ)|^4121 ≤ (6661998983487/20000000000000 : ℝ)^3097
        have hw : |(4377305429/10000000000 : ℝ)|=(4377305429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4529443729/10000000000 : ℝ)|^4121 ≤ (34859300198141/100000000000000 : ℝ)^3097
        have hw : |(4529443729/10000000000 : ℝ)|=(4529443729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4131243/9765625 : ℝ)|^4121 ≤ (3978838109657/12500000000000 : ℝ)^3097
        have hw : |(4131243/9765625 : ℝ)|=(4131243/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1049_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147662441/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14931/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2197/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7123/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14931/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10339/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14931/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10339/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14931/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10339/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14931/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10339/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14931/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10339/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14931/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10339/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10339/100000 : ℝ) ^ (8241/2048 : ℝ) ≤ (10822678821419099/100000000000000000000 : ℝ) := by
    have hpowers : (10339/100000 : ℝ)^8241 ≤ (10822678821419099/100000000000000000000 : ℝ)^2048 := by
      have hnat : (10339 : ℕ)^8241*100000000000000000000^2048 ≤ 10822678821419099^2048*100000^8241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10339 100000 10822678821419099 100000000000000000000 8241 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10339/100000 : ℝ)) (X := (10822678821419099/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14931/100000 : ℝ) ^ (8241/2048 : ℝ) ≤ (47489217483516867/100000000000000000000 : ℝ) := by
    have hpowers : (14931/100000 : ℝ)^8241 ≤ (47489217483516867/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14931 : ℕ)^8241*100000000000000000000^2048 ≤ 47489217483516867^2048*100000^8241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14931 100000 47489217483516867 100000000000000000000 8241 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14931/100000 : ℝ)) (X := (47489217483516867/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010822678821419099/50000000000000000000 : ℝ) ≤ (10000537872679667/10000000000000000 : ℝ) ^ (8241/2048 : ℝ) := by
    have hpowers : (50010822678821419099/50000000000000000000 : ℝ)^2048 ≤ (10000537872679667/10000000000000000 : ℝ)^8241 := by
      have hnat : (50010822678821419099 : ℕ)^2048*10000000000000000^8241 ≤ 10000537872679667^8241*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010822678821419099 50000000000000000000 10000537872679667 10000000000000000 2048 8241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000537872679667/10000000000000000 : ℝ)) (X := (50010822678821419099/50000000000000000000 : ℝ)) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50029155948152467983/50000000000000000000 : ℝ) ≤ (5000724406059037/5000000000000000 : ℝ) ^ (8241/2048 : ℝ) := by
    have hpowers : (50029155948152467983/50000000000000000000 : ℝ)^2048 ≤ (5000724406059037/5000000000000000 : ℝ)^8241 := by
      have hnat : (50029155948152467983 : ℕ)^2048*5000000000000000^8241 ≤ 5000724406059037^8241*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029155948152467983 50000000000000000000 5000724406059037 5000000000000000 2048 8241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000724406059037/5000000000000000 : ℝ)) (X := (50029155948152467983/50000000000000000000 : ℝ)) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50047489217483516867/50000000000000000000 : ℝ) ≤ (10002359751556481/10000000000000000 : ℝ) ^ (8241/2048 : ℝ) := by
    have hpowers : (50047489217483516867/50000000000000000000 : ℝ)^2048 ≤ (10002359751556481/10000000000000000 : ℝ)^8241 := by
      have hnat : (50047489217483516867 : ℕ)^2048*10000000000000000^8241 ≤ 10002359751556481^8241*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50047489217483516867 50000000000000000000 10002359751556481 10000000000000000 2048 8241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002359751556481/10000000000000000 : ℝ)) (X := (50047489217483516867/50000000000000000000 : ℝ)) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10822678821419099/100000000000000000000 : ℝ) ≤ ((3278830964688403637/3280000000000000000 : ℝ)+2*(910939438407/459200000000000 : ℝ)*(10339/100000 : ℝ))^(8241/2048 : ℝ) := by
    rw [show (3278830964688403637/3280000000000000000 : ℝ)+2*(910939438407/459200000000000 : ℝ)*(10339/100000 : ℝ)=(10000537872679667/10000000000000000 : ℝ) by norm_num, show 1+2*(10822678821419099/100000000000000000000 : ℝ)=(50010822678821419099/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(47489217483516867/100000000000000000000 : ℝ)+(10822678821419099/100000000000000000000 : ℝ) ≤ ((3278830964688403637/3280000000000000000 : ℝ)+(910939438407/459200000000000 : ℝ)*((14931/100000 : ℝ)+(10339/100000 : ℝ)))^(8241/2048 : ℝ) := by
    rw [show (3278830964688403637/3280000000000000000 : ℝ)+(910939438407/459200000000000 : ℝ)*((14931/100000 : ℝ)+(10339/100000 : ℝ))=(5000724406059037/5000000000000000 : ℝ) by norm_num, show 1+(47489217483516867/100000000000000000000 : ℝ)+(10822678821419099/100000000000000000000 : ℝ)=(50029155948152467983/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(47489217483516867/100000000000000000000 : ℝ) ≤ ((3278830964688403637/3280000000000000000 : ℝ)+2*(910939438407/459200000000000 : ℝ)*(14931/100000 : ℝ))^(8241/2048 : ℝ) := by
    rw [show (3278830964688403637/3280000000000000000 : ℝ)+2*(910939438407/459200000000000 : ℝ)*(14931/100000 : ℝ)=(10002359751556481/10000000000000000 : ℝ) by norm_num, show 1+2*(47489217483516867/100000000000000000000 : ℝ)=(50047489217483516867/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3278830964688403637/3280000000000000000 : ℝ)*(X 1 0+X 2 0)+(910939438407/459200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8241/2048 : ℝ)) (lo := (10339/100000 : ℝ)) (hi := (14931/100000 : ℝ)) (c := (3278830964688403637/3280000000000000000 : ℝ)) (alpha := (910939438407/459200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3278830964688403637/3280000000000000000 : ℝ)*(X 0 1+X 2 1)+(910939438407/459200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8241/2048 : ℝ)) (lo := (10339/100000 : ℝ)) (hi := (14931/100000 : ℝ)) (c := (3278830964688403637/3280000000000000000 : ℝ)) (alpha := (910939438407/459200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3278830964688403637/3280000000000000000 : ℝ)*(X 0 2+X 1 2)+(910939438407/459200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8241/2048 : ℝ)) (lo := (10339/100000 : ℝ)) (hi := (14931/100000 : ℝ)) (c := (3278830964688403637/3280000000000000000 : ℝ)) (alpha := (910939438407/459200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2211036033/10000000000 : ℝ)*X 0 0+(1081354597/2000000000 : ℝ)*X 0 1+(656594649/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674015111/5000000000 : ℝ)*X 1 0+(-1144694577/5000000000 : ℝ)*X 1 1+(5252757289/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668503767/1250000000 : ℝ)*X 2 0+(5252757411/10000000000 : ℝ)*X 2 1+(-1144694553/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2188644367/5000000000 : ℝ)*X 0 0+(2114750559/5000000000 : ℝ)*X 0 1+(4530331977/10000000000 : ℝ)*X 0 2+(2188644367/5000000000 : ℝ)*X 1 0+(2114750559/5000000000 : ℝ)*X 1 1+(4530331977/10000000000 : ℝ)*X 1 2+(2188644367/5000000000 : ℝ)*X 2 0+(2114750559/5000000000 : ℝ)*X 2 1+(4530331977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-44220889/200000000 : ℝ)*X 0 0+(21012847/40000000 : ℝ)*X 0 1+(216252659/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061858269/2000000000 : ℝ)*X 1 0+(-533957493/2500000000 : ℝ)*X 1 1+(675789557/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309291373/10000000000 : ℝ)*X 2 0+(5406316407/10000000000 : ℝ)*X 2 1+(-2135829999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4377305429/10000000000 : ℝ)*X 0 0+(4529443729/10000000000 : ℝ)*X 0 1+(4131243/9765625 : ℝ)*X 0 2+(4377305429/10000000000 : ℝ)*X 1 0+(4529443729/10000000000 : ℝ)*X 1 1+(4131243/9765625 : ℝ)*X 1 2+(4377305429/10000000000 : ℝ)*X 2 0+(4529443729/10000000000 : ℝ)*X 2 1+(4131243/9765625 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9588717439130997160291047201/1148000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (715501489/50000000000000 : ℝ)*(base19) + (295787287/25000000000000 : ℝ)*(base23) + (2397309/3125000000000 : ℝ)*(lower2) + (78144327/50000000000000 : ℝ)*(upper3) + (90348571/100000000000000 : ℝ)*(upper5) + (613567655768239/12500000000000 : ℝ)*(major0) + (613567655768239/12500000000000 : ℝ)*(major1) + (4908541246145913/100000000000000 : ℝ)*(major2) + (1298576072406143/20000000000000 : ℝ)*(sp0) + (6492917093780817/100000000000000 : ℝ)*(sp1) + (6492917341634647/100000000000000 : ℝ)*(sp2) + (51939760144013/1562500000000 : ℝ)*(sp3) + (954068827/2500000000000 : ℝ)*(sp4) + (19039873147/100000000000000 : ℝ)*(sp7) + (1662081844544989/50000000000000 : ℝ)*(f.failure) + (1298583704956759/20000000000000 : ℝ)*(f.sum) + (57447884792149/9184000000000000000000000000 : ℝ)*base66 + (918934404332490451/287000000000000000000000000000000 : ℝ)*base67 + (8523019395305600933/2296000000000000000000000000000000 : ℝ)*base70 + (603672205324509549/287000000000000000000000000000000 : ℝ)*base72 + (37343910096309/9184000000000000000000000000 : ℝ)*base74 + (39204421091873600933/2296000000000000000000000000000000 : ℝ)*base76 + (1211454444180553299/287000000000000000000000000000000 : ℝ)*base78 + (1178229670588446701/287000000000000000000000000000000 : ℝ)*base79 + (17726236136547/2870000000000000000000000000 : ℝ)*base82 + (10058149/5000000000000000000000 : ℝ)*base89 + (10058149/5000000000000000000000 : ℝ)*base91 + (39941851/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (81326661609347814462845049/20500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (754597319/100000000000000 : ℝ)*(base19) + (510960553/50000000000000 : ℝ)*(base23) + (129588443/100000000000000 : ℝ)*(lower4) + (38557233/20000000000000 : ℝ)*(upper5) + (1234424063623359/25000000000000 : ℝ)*(major0) + (1234424063623359/25000000000000 : ℝ)*(major1) + (1234424063623359/25000000000000 : ℝ)*(major2) + (532660579/50000000000000 : ℝ)*(sp0) + (713461361/3125000000000 : ℝ)*(sp1) + (10647888461/50000000000000 : ℝ)*(sp2) + (1632870814837391/25000000000000 : ℝ)*(sp4) + (130629214786197/2000000000000 : ℝ)*(sp5) + (6531462006972693/100000000000000 : ℝ)*(sp6) + (835977013019417/25000000000000 : ℝ)*(sp7) + (835977013019417/25000000000000 : ℝ)*(f.failure) + (6531484324670721/100000000000000 : ℝ)*(f.sum) + (8699993646599/820000000000000000000000000 : ℝ)*base65 + (825229889422293317/82000000000000000000000000000000 : ℝ)*base68 + (1206790109042293317/82000000000000000000000000000000 : ℝ)*base70 + (564888331929706683/82000000000000000000000000000000 : ℝ)*base71 + (1063537657679/820000000000000000000000000 : ℝ)*base73 + (1143640834186293317/82000000000000000000000000000000 : ℝ)*base76 + (80491199204293317/82000000000000000000000000000000 : ℝ)*base78 + (351241137188293317/82000000000000000000000000000000 : ℝ)*base80 + (3960727239819/820000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (5383103/2500000000000000000000 : ℝ)*base90 + (5383103/2500000000000000000000 : ℝ)*base92 + (5383103/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1049_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147662441/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14931/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2197/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7123/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1049_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1049_s5_0 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-276489739/1250000000 : ℝ)*x 0 + (5397491393/10000000000 : ℝ)*x 1 + (1315365089/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (276489739/1250000000 : ℝ)^4121 ≤ (6715707281553/50000000000000 : ℝ)^3097 := by
    have hnat : (276489739 : ℕ)^4121*50000000000000^3097 ≤ 6715707281553^3097*1250000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276489739 1250000000 6715707281553 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397491393/10000000000 : ℝ)^4121 ≤ (22009654595353/50000000000000 : ℝ)^3097 := by
    have hnat : (5397491393 : ℕ)^4121*50000000000000^3097 ≤ 22009654595353^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397491393 10000000000 22009654595353 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315365089/2500000000 : ℝ)^4121 ≤ (21274638114051/50000000000000 : ℝ)^3097 := by
    have hnat : (1315365089 : ℕ)^4121*50000000000000^3097 ≤ 21274638114051^3097*2500000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315365089 2500000000 21274638114051 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-276489739/1250000000 : ℝ), (5397491393/10000000000 : ℝ), (1315365089/2500000000 : ℝ)] ![(6715707281553/50000000000000 : ℝ), (22009654595353/50000000000000 : ℝ), (21274638114051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-276489739/1250000000 : ℝ)|^4121 ≤ (6715707281553/50000000000000 : ℝ)^3097
        have hw : |(-276489739/1250000000 : ℝ)|=(276489739/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397491393/10000000000 : ℝ)|^4121 ≤ (22009654595353/50000000000000 : ℝ)^3097
        have hw : |(5397491393/10000000000 : ℝ)|=(5397491393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315365089/2500000000 : ℝ)|^4121 ≤ (21274638114051/50000000000000 : ℝ)^3097
        have hw : |(1315365089/2500000000 : ℝ)|=(1315365089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s5_1 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336430507/2500000000 : ℝ)*x 0 + (-1140491531/5000000000 : ℝ)*x 1 + (1315365119/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336430507/2500000000 : ℝ)^4121 ≤ (5432299631257/12500000000000 : ℝ)^3097 := by
    have hnat : (1336430507 : ℕ)^4121*12500000000000^3097 ≤ 5432299631257^3097*2500000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336430507 2500000000 5432299631257 12500000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1140491531/5000000000 : ℝ)^4121 ≤ (6996162708101/50000000000000 : ℝ)^3097 := by
    have hnat : (1140491531 : ℕ)^4121*50000000000000^3097 ≤ 6996162708101^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140491531 5000000000 6996162708101 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315365119/2500000000 : ℝ)^4121 ≤ (21274638759703/50000000000000 : ℝ)^3097 := by
    have hnat : (1315365119 : ℕ)^4121*50000000000000^3097 ≤ 21274638759703^3097*2500000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315365119 2500000000 21274638759703 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336430507/2500000000 : ℝ), (-1140491531/5000000000 : ℝ), (1315365119/2500000000 : ℝ)] ![(5432299631257/12500000000000 : ℝ), (6996162708101/50000000000000 : ℝ), (21274638759703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336430507/2500000000 : ℝ)|^4121 ≤ (5432299631257/12500000000000 : ℝ)^3097
        have hw : |(1336430507/2500000000 : ℝ)|=(1336430507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1140491531/5000000000 : ℝ)|^4121 ≤ (6996162708101/50000000000000 : ℝ)^3097
        have hw : |(-1140491531/5000000000 : ℝ)|=(1140491531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315365119/2500000000 : ℝ)|^4121 ≤ (21274638759703/50000000000000 : ℝ)^3097
        have hw : |(1315365119/2500000000 : ℝ)|=(1315365119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s5_2 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672860993/5000000000 : ℝ)*x 0 + (5261460503/10000000000 : ℝ)*x 1 + (-1140491541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672860993/5000000000 : ℝ)^4121 ≤ (43458396595719/100000000000000 : ℝ)^3097 := by
    have hnat : (2672860993 : ℕ)^4121*100000000000000^3097 ≤ 43458396595719^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672860993 5000000000 43458396595719 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261460503/10000000000 : ℝ)^4121 ≤ (850985556199/2000000000000 : ℝ)^3097 := by
    have hnat : (5261460503 : ℕ)^4121*2000000000000^3097 ≤ 850985556199^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261460503 10000000000 850985556199 2000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1140491541/5000000000 : ℝ)^4121 ≤ (6996162789727/50000000000000 : ℝ)^3097 := by
    have hnat : (1140491541 : ℕ)^4121*50000000000000^3097 ≤ 6996162789727^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140491541 5000000000 6996162789727 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672860993/5000000000 : ℝ), (5261460503/10000000000 : ℝ), (-1140491541/5000000000 : ℝ)] ![(43458396595719/100000000000000 : ℝ), (850985556199/2000000000000 : ℝ), (6996162789727/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672860993/5000000000 : ℝ)|^4121 ≤ (43458396595719/100000000000000 : ℝ)^3097
        have hw : |(2672860993/5000000000 : ℝ)|=(2672860993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261460503/10000000000 : ℝ)|^4121 ≤ (850985556199/2000000000000 : ℝ)^3097
        have hw : |(5261460503/10000000000 : ℝ)|=(5261460503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1140491541/5000000000 : ℝ)|^4121 ≤ (6996162789727/50000000000000 : ℝ)^3097
        have hw : |(-1140491541/5000000000 : ℝ)|=(1140491541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s5_3 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4377799073/10000000000 : ℝ)*x 0 + (4246998043/10000000000 : ℝ)*x 1 + (4512700457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377799073/10000000000 : ℝ)^4121 ≤ (4164374193563/12500000000000 : ℝ)^3097 := by
    have hnat : (4377799073 : ℕ)^4121*12500000000000^3097 ≤ 4164374193563^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377799073 10000000000 4164374193563 12500000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4246998043/10000000000 : ℝ)^4121 ≤ (31997066386479/100000000000000 : ℝ)^3097 := by
    have hnat : (4246998043 : ℕ)^4121*100000000000000^3097 ≤ 31997066386479^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246998043 10000000000 31997066386479 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4512700457/10000000000 : ℝ)^4121 ≤ (17343970024331/50000000000000 : ℝ)^3097 := by
    have hnat : (4512700457 : ℕ)^4121*50000000000000^3097 ≤ 17343970024331^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512700457 10000000000 17343970024331 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377799073/10000000000 : ℝ), (4246998043/10000000000 : ℝ), (4512700457/10000000000 : ℝ)] ![(4164374193563/12500000000000 : ℝ), (31997066386479/100000000000000 : ℝ), (17343970024331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377799073/10000000000 : ℝ)|^4121 ≤ (4164374193563/12500000000000 : ℝ)^3097
        have hw : |(4377799073/10000000000 : ℝ)|=(4377799073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4246998043/10000000000 : ℝ)|^4121 ≤ (31997066386479/100000000000000 : ℝ)^3097
        have hw : |(4246998043/10000000000 : ℝ)|=(4246998043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4512700457/10000000000 : ℝ)|^4121 ≤ (17343970024331/50000000000000 : ℝ)^3097
        have hw : |(4512700457/10000000000 : ℝ)|=(4512700457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s5_4 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1105961827/5000000000 : ℝ)*x 0 + (2630907613/5000000000 : ℝ)*x 1 + (2698567611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1105961827/5000000000 : ℝ)^4121 ≤ (2686292191757/20000000000000 : ℝ)^3097 := by
    have hnat : (1105961827 : ℕ)^4121*20000000000000^3097 ≤ 2686292191757^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105961827 5000000000 2686292191757 20000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630907613/5000000000 : ℝ)^4121 ≤ (4255309497973/10000000000000 : ℝ)^3097 := by
    have hnat : (2630907613 : ℕ)^4121*10000000000000^3097 ≤ 4255309497973^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630907613 5000000000 4255309497973 10000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698567611/5000000000 : ℝ)^4121 ≤ (1760617761579/4000000000000 : ℝ)^3097 := by
    have hnat : (2698567611 : ℕ)^4121*4000000000000^3097 ≤ 1760617761579^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698567611 5000000000 1760617761579 4000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1105961827/5000000000 : ℝ), (2630907613/5000000000 : ℝ), (2698567611/5000000000 : ℝ)] ![(2686292191757/20000000000000 : ℝ), (4255309497973/10000000000000 : ℝ), (1760617761579/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1105961827/5000000000 : ℝ)|^4121 ≤ (2686292191757/20000000000000 : ℝ)^3097
        have hw : |(-1105961827/5000000000 : ℝ)|=(1105961827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630907613/5000000000 : ℝ)|^4121 ≤ (4255309497973/10000000000000 : ℝ)^3097
        have hw : |(2630907613/5000000000 : ℝ)|=(2630907613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698567611/5000000000 : ℝ)|^4121 ≤ (1760617761579/4000000000000 : ℝ)^3097
        have hw : |(2698567611/5000000000 : ℝ)|=(2698567611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s5_5 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2655752897/5000000000 : ℝ)*x 0 + (-1072654101/5000000000 : ℝ)*x 1 + (2698567611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655752897/5000000000 : ℝ)^4121 ≤ (43088653600019/100000000000000 : ℝ)^3097 := by
    have hnat : (2655752897 : ℕ)^4121*100000000000000^3097 ≤ 43088653600019^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655752897 5000000000 43088653600019 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1072654101/5000000000 : ℝ)^4121 ≤ (20149847413/156250000000 : ℝ)^3097 := by
    have hnat : (1072654101 : ℕ)^4121*156250000000^3097 ≤ 20149847413^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072654101 5000000000 20149847413 156250000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698567611/5000000000 : ℝ)^4121 ≤ (1760617761579/4000000000000 : ℝ)^3097 := by
    have hnat : (2698567611 : ℕ)^4121*4000000000000^3097 ≤ 1760617761579^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698567611 5000000000 1760617761579 4000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655752897/5000000000 : ℝ), (-1072654101/5000000000 : ℝ), (2698567611/5000000000 : ℝ)] ![(43088653600019/100000000000000 : ℝ), (20149847413/156250000000 : ℝ), (1760617761579/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655752897/5000000000 : ℝ)|^4121 ≤ (43088653600019/100000000000000 : ℝ)^3097
        have hw : |(2655752897/5000000000 : ℝ)|=(2655752897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1072654101/5000000000 : ℝ)|^4121 ≤ (20149847413/156250000000 : ℝ)^3097
        have hw : |(-1072654101/5000000000 : ℝ)|=(1072654101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698567611/5000000000 : ℝ)|^4121 ≤ (1760617761579/4000000000000 : ℝ)^3097
        have hw : |(2698567611/5000000000 : ℝ)|=(2698567611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s5_6 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062301159/2000000000 : ℝ)*x 0 + (2698567611/5000000000 : ℝ)*x 1 + (-2145308201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062301159/2000000000 : ℝ)^4121 ≤ (21544326805407/50000000000000 : ℝ)^3097 := by
    have hnat : (1062301159 : ℕ)^4121*50000000000000^3097 ≤ 21544326805407^3097*2000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062301159 2000000000 21544326805407 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698567611/5000000000 : ℝ)^4121 ≤ (1760617761579/4000000000000 : ℝ)^3097 := by
    have hnat : (2698567611 : ℕ)^4121*4000000000000^3097 ≤ 1760617761579^3097*5000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698567611 5000000000 1760617761579 4000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2145308201/10000000000 : ℝ)^4121 ≤ (12895902336321/100000000000000 : ℝ)^3097 := by
    have hnat : (2145308201 : ℕ)^4121*100000000000000^3097 ≤ 12895902336321^3097*10000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145308201 10000000000 12895902336321 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062301159/2000000000 : ℝ), (2698567611/5000000000 : ℝ), (-2145308201/10000000000 : ℝ)] ![(21544326805407/50000000000000 : ℝ), (1760617761579/4000000000000 : ℝ), (12895902336321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062301159/2000000000 : ℝ)|^4121 ≤ (21544326805407/50000000000000 : ℝ)^3097
        have hw : |(1062301159/2000000000 : ℝ)|=(1062301159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698567611/5000000000 : ℝ)|^4121 ≤ (1760617761579/4000000000000 : ℝ)^3097
        have hw : |(2698567611/5000000000 : ℝ)|=(2698567611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2145308201/10000000000 : ℝ)|^4121 ≤ (12895902336321/100000000000000 : ℝ)^3097
        have hw : |(-2145308201/10000000000 : ℝ)|=(2145308201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1049_s5_7 (p : ℝ) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1094452579/2500000000 : ℝ)*x 0 + (451200739/1000000000 : ℝ)*x 1 + (1061923441/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094452579/2500000000 : ℝ)^4121 ≤ (8328776849277/25000000000000 : ℝ)^3097 := by
    have hnat : (1094452579 : ℕ)^4121*25000000000000^3097 ≤ 8328776849277^3097*2500000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094452579 2500000000 8328776849277 25000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451200739/1000000000 : ℝ)^4121 ≤ (34680851332203/100000000000000 : ℝ)^3097 := by
    have hnat : (451200739 : ℕ)^4121*100000000000000^3097 ≤ 34680851332203^3097*1000000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451200739 1000000000 34680851332203 100000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1061923441/2500000000 : ℝ)^4121 ≤ (16002020630381/50000000000000 : ℝ)^3097 := by
    have hnat : (1061923441 : ℕ)^4121*50000000000000^3097 ≤ 16002020630381^3097*2500000000^4121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061923441 2500000000 16002020630381 50000000000000 4121 3097 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4121/1024 : ℝ)) 4121 3097 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094452579/2500000000 : ℝ), (451200739/1000000000 : ℝ), (1061923441/2500000000 : ℝ)] ![(8328776849277/25000000000000 : ℝ), (34680851332203/100000000000000 : ℝ), (16002020630381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094452579/2500000000 : ℝ)|^4121 ≤ (8328776849277/25000000000000 : ℝ)^3097
        have hw : |(1094452579/2500000000 : ℝ)|=(1094452579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(451200739/1000000000 : ℝ)|^4121 ≤ (34680851332203/100000000000000 : ℝ)^3097
        have hw : |(451200739/1000000000 : ℝ)|=(451200739/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1061923441/2500000000 : ℝ)|^4121 ≤ (16002020630381/50000000000000 : ℝ)^3097
        have hw : |(1061923441/2500000000 : ℝ)|=(1061923441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1049_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147662441/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7123/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2197/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11171/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3513/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7123/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2197/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7123/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2197/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7123/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2197/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7123/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2197/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7123/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2197/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7123/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2197/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2197/20000 : ℝ) ^ (8241/2048 : ℝ) ≤ (1381181132624981/10000000000000000000 : ℝ) := by
    have hpowers : (2197/20000 : ℝ)^8241 ≤ (1381181132624981/10000000000000000000 : ℝ)^2048 := by
      have hnat : (2197 : ℕ)^8241*10000000000000000000^2048 ≤ 1381181132624981^2048*20000^8241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2197 20000 1381181132624981 10000000000000000000 8241 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2197/20000 : ℝ)) (X := (1381181132624981/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7123/50000 : ℝ) ^ (8241/2048 : ℝ) ≤ (39311824692758841/100000000000000000000 : ℝ) := by
    have hpowers : (7123/50000 : ℝ)^8241 ≤ (39311824692758841/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7123 : ℕ)^8241*100000000000000000000^2048 ≤ 39311824692758841^2048*50000^8241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7123 50000 39311824692758841 100000000000000000000 8241 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7123/50000 : ℝ)) (X := (39311824692758841/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001381181132624981/5000000000000000000 : ℝ) ≤ (10000686413156033/10000000000000000 : ℝ) ^ (8241/2048 : ℝ) := by
    have hpowers : (5001381181132624981/5000000000000000000 : ℝ)^2048 ≤ (10000686413156033/10000000000000000 : ℝ)^8241 := by
      have hnat : (5001381181132624981 : ℕ)^2048*10000000000000000^8241 ≤ 10000686413156033^8241*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001381181132624981 5000000000000000000 10000686413156033 10000000000000000 2048 8241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000686413156033/10000000000000000 : ℝ)) (X := (5001381181132624981/5000000000000000000 : ℝ)) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100053123636019008651/100000000000000000000 : ℝ) ≤ (2000263986158127/2000000000000000 : ℝ) ^ (8241/2048 : ℝ) := by
    have hpowers : (100053123636019008651/100000000000000000000 : ℝ)^2048 ≤ (2000263986158127/2000000000000000 : ℝ)^8241 := by
      have hnat : (100053123636019008651 : ℕ)^2048*2000000000000000^8241 ≤ 2000263986158127^8241*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100053123636019008651 100000000000000000000 2000263986158127 2000000000000000 2048 8241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000263986158127/2000000000000000 : ℝ)) (X := (100053123636019008651/100000000000000000000 : ℝ)) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039311824692758841/50000000000000000000 : ℝ) ≤ (10001953448425237/10000000000000000 : ℝ) ^ (8241/2048 : ℝ) := by
    have hpowers : (50039311824692758841/50000000000000000000 : ℝ)^2048 ≤ (10001953448425237/10000000000000000 : ℝ)^8241 := by
      have hnat : (50039311824692758841 : ℕ)^2048*10000000000000000^8241 ≤ 10001953448425237^8241*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039311824692758841 50000000000000000000 10001953448425237 10000000000000000 2048 8241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001953448425237/10000000000000000 : ℝ)) (X := (50039311824692758841/50000000000000000000 : ℝ)) (by norm_num) 8241 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1381181132624981/10000000000000000000 : ℝ) ≤ ((32598320010869617673/32610000000000000000 : ℝ)+2*(316758817301/163050000000000 : ℝ)*(2197/20000 : ℝ))^(8241/2048 : ℝ) := by
    rw [show (32598320010869617673/32610000000000000000 : ℝ)+2*(316758817301/163050000000000 : ℝ)*(2197/20000 : ℝ)=(10000686413156033/10000000000000000 : ℝ) by norm_num, show 1+2*(1381181132624981/10000000000000000000 : ℝ)=(5001381181132624981/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39311824692758841/100000000000000000000 : ℝ)+(1381181132624981/10000000000000000000 : ℝ) ≤ ((32598320010869617673/32610000000000000000 : ℝ)+(316758817301/163050000000000 : ℝ)*((7123/50000 : ℝ)+(2197/20000 : ℝ)))^(8241/2048 : ℝ) := by
    rw [show (32598320010869617673/32610000000000000000 : ℝ)+(316758817301/163050000000000 : ℝ)*((7123/50000 : ℝ)+(2197/20000 : ℝ))=(2000263986158127/2000000000000000 : ℝ) by norm_num, show 1+(39311824692758841/100000000000000000000 : ℝ)+(1381181132624981/10000000000000000000 : ℝ)=(100053123636019008651/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39311824692758841/100000000000000000000 : ℝ) ≤ ((32598320010869617673/32610000000000000000 : ℝ)+2*(316758817301/163050000000000 : ℝ)*(7123/50000 : ℝ))^(8241/2048 : ℝ) := by
    rw [show (32598320010869617673/32610000000000000000 : ℝ)+2*(316758817301/163050000000000 : ℝ)*(7123/50000 : ℝ)=(10001953448425237/10000000000000000 : ℝ) by norm_num, show 1+2*(39311824692758841/100000000000000000000 : ℝ)=(50039311824692758841/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (32598320010869617673/32610000000000000000 : ℝ)*(X 1 0+X 2 0)+(316758817301/163050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8241/2048 : ℝ)) (lo := (2197/20000 : ℝ)) (hi := (7123/50000 : ℝ)) (c := (32598320010869617673/32610000000000000000 : ℝ)) (alpha := (316758817301/163050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (32598320010869617673/32610000000000000000 : ℝ)*(X 0 1+X 2 1)+(316758817301/163050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8241/2048 : ℝ)) (lo := (2197/20000 : ℝ)) (hi := (7123/50000 : ℝ)) (c := (32598320010869617673/32610000000000000000 : ℝ)) (alpha := (316758817301/163050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (32598320010869617673/32610000000000000000 : ℝ)*(X 0 2+X 1 2)+(316758817301/163050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8241/2048 : ℝ)) (lo := (2197/20000 : ℝ)) (hi := (7123/50000 : ℝ)) (c := (32598320010869617673/32610000000000000000 : ℝ)) (alpha := (316758817301/163050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-276489739/1250000000 : ℝ)*X 0 0+(5397491393/10000000000 : ℝ)*X 0 1+(1315365089/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336430507/2500000000 : ℝ)*X 1 0+(-1140491531/5000000000 : ℝ)*X 1 1+(1315365119/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672860993/5000000000 : ℝ)*X 2 0+(5261460503/10000000000 : ℝ)*X 2 1+(-1140491541/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4377799073/10000000000 : ℝ)*X 0 0+(4246998043/10000000000 : ℝ)*X 0 1+(4512700457/10000000000 : ℝ)*X 0 2+(4377799073/10000000000 : ℝ)*X 1 0+(4246998043/10000000000 : ℝ)*X 1 1+(4512700457/10000000000 : ℝ)*X 1 2+(4377799073/10000000000 : ℝ)*X 2 0+(4246998043/10000000000 : ℝ)*X 2 1+(4512700457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1105961827/5000000000 : ℝ)*X 0 0+(2630907613/5000000000 : ℝ)*X 0 1+(2698567611/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655752897/5000000000 : ℝ)*X 1 0+(-1072654101/5000000000 : ℝ)*X 1 1+(2698567611/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062301159/2000000000 : ℝ)*X 2 0+(2698567611/5000000000 : ℝ)*X 2 1+(-2145308201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1094452579/2500000000 : ℝ)*X 0 0+(451200739/1000000000 : ℝ)*X 0 1+(1061923441/2500000000 : ℝ)*X 0 2+(1094452579/2500000000 : ℝ)*X 1 0+(451200739/1000000000 : ℝ)*X 1 1+(1061923441/2500000000 : ℝ)*X 1 2+(1094452579/2500000000 : ℝ)*X 2 0+(451200739/1000000000 : ℝ)*X 2 1+(1061923441/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1049_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2367586677748187745805366189/543500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (305083067/50000000000000 : ℝ)*(base19) + (513425347/100000000000000 : ℝ)*(base23) + (20839477/100000000000000 : ℝ)*(lower2) + (74668357/50000000000000 : ℝ)*(upper3) + (15763677/20000000000000 : ℝ)*(upper5) + (2778731925221853/50000000000000 : ℝ)*(major0) + (2778731925221853/50000000000000 : ℝ)*(major1) + (5557463850443707/100000000000000 : ℝ)*(major2) + (28715951217643/390625000000 : ℝ)*(sp0) + (1470259941411997/20000000000000 : ℝ)*(sp1) + (1837824950950193/25000000000000 : ℝ)*(sp2) + (376361746488887/10000000000000 : ℝ)*(sp3) + (2100688689/12500000000000 : ℝ)*(sp4) + (9773566239/100000000000000 : ℝ)*(sp7) + (376362723845511/10000000000000 : ℝ)*(f.failure) + (7351300317226119/100000000000000 : ℝ)*(f.sum) + (154248986286863/16305000000000000000000000000 : ℝ)*base65 + (761100060722691931/1630500000000000000000000000000000 : ℝ)*base68 + (12967049515222033811/3261000000000000000000000000000000 : ℝ)*base69 + (1021517549831691931/1630500000000000000000000000000000 : ℝ)*base72 + (66163606599563/16305000000000000000000000000 : ℝ)*base73 + (65571451167994033811/3261000000000000000000000000000000 : ℝ)*base75 + (2740187639690736023/543500000000000000000000000000000 : ℝ)*base77 + (3054176443305736023/543500000000000000000000000000000 : ℝ)*base79 + (14257501783167/2717500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1152351/1000000000000000000000 : ℝ)*base89 + (1152351/1000000000000000000000 : ℝ)*base91 + (8847649/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2772192216550967003275787/339687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1528957189/100000000000000 : ℝ)*(base19) + (83070909/5000000000000 : ℝ)*(base23) + (82513517/50000000000000 : ℝ)*(upper3) + (29607931/50000000000000 : ℝ)*(lower4) + (41585671/25000000000000 : ℝ)*(upper5) + (6983295916231/125000000000 : ℝ)*(major0) + (6983295916231/125000000000 : ℝ)*(major1) + (6983295916231/125000000000 : ℝ)*(major2) + (39707558079/100000000000000 : ℝ)*(sp1) + (21373827267/50000000000000 : ℝ)*(sp2) + (3694944743863397/50000000000000 : ℝ)*(sp4) + (7389848251211527/100000000000000 : ℝ)*(sp5) + (7389845078654079/100000000000000 : ℝ)*(sp6) + (1891691853104609/50000000000000 : ℝ)*(sp7) + (1891691853104609/50000000000000 : ℝ)*(f.failure) + (3694944743863397/50000000000000 : ℝ)*(f.sum) + (737361828203/815250000000000000000000000 : ℝ)*base66 + (7201616504156821/1358750000000000000000000000000 : ℝ)*base67 + (1622632000441821/1358750000000000000000000000000 : ℝ)*base69 + (5477366278890679/1358750000000000000000000000000 : ℝ)*base72 + (4043825833393/815250000000000000000000000 : ℝ)*base73 + (173455380804321/1358750000000000000000000000000 : ℝ)*base75 + (8700482498518071/1358750000000000000000000000000 : ℝ)*base77 + (18265407277216821/1358750000000000000000000000000 : ℝ)*base79 + (1206879319213/652200000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (6709431/5000000000000000000000 : ℝ)*base90 + (6709431/5000000000000000000000 : ℝ)*base92 + (6709431/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1049_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147662441/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7123/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2197/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11171/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1049_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1049_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147662441/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8399/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8627/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11171/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1049_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1049_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1049_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8241/2048 : ℝ) ≤ p) (hpb : p ≤ (4121/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147662441/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8399/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8627/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11171/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1049_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
