-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1516_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:56:27.682323+00:00
-- url     : https://prove2.me/submissions/d6d08923-cd16-4190-b1c2-8554ac50552a

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
theorem support_rectangle_w1516_s6_0 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351366719/10000000000 : ℝ)*x 0 + (5217838427/10000000000 : ℝ)*x 1 + (-394432579/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351366719/10000000000 : ℝ)^4529 ≤ (4457943659037/10000000000000 : ℝ)^3505 := by
    have hnat : (5351366719 : ℕ)^4529*10000000000000^3505 ≤ 4457943659037^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351366719 10000000000 4457943659037 10000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217838427/10000000000 : ℝ)^4529 ≤ (10786843393041/25000000000000 : ℝ)^3505 := by
    have hnat : (5217838427 : ℕ)^4529*25000000000000^3505 ≤ 10786843393041^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217838427 10000000000 10786843393041 25000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394432579/2000000000 : ℝ)^4529 ≤ (383537181981/3125000000000 : ℝ)^3505 := by
    have hnat : (394432579 : ℕ)^4529*3125000000000^3505 ≤ 383537181981^3505*2000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394432579 2000000000 383537181981 3125000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351366719/10000000000 : ℝ), (5217838427/10000000000 : ℝ), (-394432579/2000000000 : ℝ)] ![(4457943659037/10000000000000 : ℝ), (10786843393041/25000000000000 : ℝ), (383537181981/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351366719/10000000000 : ℝ)|^4529 ≤ (4457943659037/10000000000000 : ℝ)^3505
        have hw : |(5351366719/10000000000 : ℝ)|=(5351366719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217838427/10000000000 : ℝ)|^4529 ≤ (10786843393041/25000000000000 : ℝ)^3505
        have hw : |(5217838427/10000000000 : ℝ)|=(5217838427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-394432579/2000000000 : ℝ)|^4529 ≤ (383537181981/3125000000000 : ℝ)^3505
        have hw : |(-394432579/2000000000 : ℝ)|=(394432579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s6_1 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2133956609/5000000000 : ℝ)*x 0 + (503690281/1250000000 : ℝ)*x 1 + (2259069221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133956609/5000000000 : ℝ)^4529 ≤ (8319966297671/25000000000000 : ℝ)^3505 := by
    have hnat : (2133956609 : ℕ)^4529*25000000000000^3505 ≤ 8319966297671^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133956609 5000000000 8319966297671 25000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (503690281/1250000000 : ℝ)^4529 ≤ (30897744674401/100000000000000 : ℝ)^3505 := by
    have hnat : (503690281 : ℕ)^4529*100000000000000^3505 ≤ 30897744674401^3505*1250000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503690281 1250000000 30897744674401 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2259069221/5000000000 : ℝ)^4529 ≤ (7164478024987/20000000000000 : ℝ)^3505 := by
    have hnat : (2259069221 : ℕ)^4529*20000000000000^3505 ≤ 7164478024987^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259069221 5000000000 7164478024987 20000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2133956609/5000000000 : ℝ), (503690281/1250000000 : ℝ), (2259069221/5000000000 : ℝ)] ![(8319966297671/25000000000000 : ℝ), (30897744674401/100000000000000 : ℝ), (7164478024987/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2133956609/5000000000 : ℝ)|^4529 ≤ (8319966297671/25000000000000 : ℝ)^3505
        have hw : |(2133956609/5000000000 : ℝ)|=(2133956609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(503690281/1250000000 : ℝ)|^4529 ≤ (30897744674401/100000000000000 : ℝ)^3505
        have hw : |(503690281/1250000000 : ℝ)|=(503690281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2259069221/5000000000 : ℝ)|^4529 ≤ (7164478024987/20000000000000 : ℝ)^3505
        have hw : |(2259069221/5000000000 : ℝ)|=(2259069221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s6_2 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-931076189/5000000000 : ℝ)*x 0 + (2609472927/5000000000 : ℝ)*x 1 + (2715798033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (931076189/5000000000 : ℝ)^4529 ≤ (89030174341/781250000000 : ℝ)^3505 := by
    have hnat : (931076189 : ℕ)^4529*781250000000^3505 ≤ 89030174341^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931076189 5000000000 89030174341 781250000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609472927/5000000000 : ℝ)^4529 ≤ (43159206892133/100000000000000 : ℝ)^3505 := by
    have hnat : (2609472927 : ℕ)^4529*100000000000000^3505 ≤ 43159206892133^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609472927 5000000000 43159206892133 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715798033/5000000000 : ℝ)^4529 ≤ (45444930788467/100000000000000 : ℝ)^3505 := by
    have hnat : (2715798033 : ℕ)^4529*100000000000000^3505 ≤ 45444930788467^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715798033 5000000000 45444930788467 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-931076189/5000000000 : ℝ), (2609472927/5000000000 : ℝ), (2715798033/5000000000 : ℝ)] ![(89030174341/781250000000 : ℝ), (43159206892133/100000000000000 : ℝ), (45444930788467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-931076189/5000000000 : ℝ)|^4529 ≤ (89030174341/781250000000 : ℝ)^3505
        have hw : |(-931076189/5000000000 : ℝ)|=(931076189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609472927/5000000000 : ℝ)|^4529 ≤ (43159206892133/100000000000000 : ℝ)^3505
        have hw : |(2609472927/5000000000 : ℝ)|=(2609472927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715798033/5000000000 : ℝ)|^4529 ≤ (45444930788467/100000000000000 : ℝ)^3505
        have hw : |(2715798033/5000000000 : ℝ)|=(2715798033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s6_3 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294925183/10000000000 : ℝ)*x 0 + (-1758405287/10000000000 : ℝ)*x 1 + (5431596997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294925183/10000000000 : ℝ)^4529 ≤ (10993205909559/25000000000000 : ℝ)^3505 := by
    have hnat : (5294925183 : ℕ)^4529*25000000000000^3505 ≤ 10993205909559^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294925183 10000000000 10993205909559 25000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1758405287/10000000000 : ℝ)^4529 ≤ (1058223549671/10000000000000 : ℝ)^3505 := by
    have hnat : (1758405287 : ℕ)^4529*10000000000000^3505 ≤ 1058223549671^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1758405287 10000000000 1058223549671 10000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431596997/10000000000 : ℝ)^4529 ≤ (5680617606707/12500000000000 : ℝ)^3505 := by
    have hnat : (5431596997 : ℕ)^4529*12500000000000^3505 ≤ 5680617606707^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431596997 10000000000 5680617606707 12500000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294925183/10000000000 : ℝ), (-1758405287/10000000000 : ℝ), (5431596997/10000000000 : ℝ)] ![(10993205909559/25000000000000 : ℝ), (1058223549671/10000000000000 : ℝ), (5680617606707/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294925183/10000000000 : ℝ)|^4529 ≤ (10993205909559/25000000000000 : ℝ)^3505
        have hw : |(5294925183/10000000000 : ℝ)|=(5294925183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1758405287/10000000000 : ℝ)|^4529 ≤ (1058223549671/10000000000000 : ℝ)^3505
        have hw : |(-1758405287/10000000000 : ℝ)|=(1758405287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431596997/10000000000 : ℝ)|^4529 ≤ (5680617606707/12500000000000 : ℝ)^3505
        have hw : |(5431596997/10000000000 : ℝ)|=(5431596997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s6_4 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294925349/10000000000 : ℝ)*x 0 + (2715798533/5000000000 : ℝ)*x 1 + (-879202481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294925349/10000000000 : ℝ)^4529 ≤ (5496603177447/12500000000000 : ℝ)^3505 := by
    have hnat : (5294925349 : ℕ)^4529*12500000000000^3505 ≤ 5496603177447^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294925349 10000000000 5496603177447 12500000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715798533/5000000000 : ℝ)^4529 ≤ (22722470799813/50000000000000 : ℝ)^3505 := by
    have hnat : (2715798533 : ℕ)^4529*50000000000000^3505 ≤ 22722470799813^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715798533 5000000000 22722470799813 50000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (879202481/5000000000 : ℝ)^4529 ≤ (5291116484707/50000000000000 : ℝ)^3505 := by
    have hnat : (879202481 : ℕ)^4529*50000000000000^3505 ≤ 5291116484707^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879202481 5000000000 5291116484707 50000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294925349/10000000000 : ℝ), (2715798533/5000000000 : ℝ), (-879202481/5000000000 : ℝ)] ![(5496603177447/12500000000000 : ℝ), (22722470799813/50000000000000 : ℝ), (5291116484707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294925349/10000000000 : ℝ)|^4529 ≤ (5496603177447/12500000000000 : ℝ)^3505
        have hw : |(5294925349/10000000000 : ℝ)|=(5294925349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715798533/5000000000 : ℝ)|^4529 ≤ (22722470799813/50000000000000 : ℝ)^3505
        have hw : |(2715798533/5000000000 : ℝ)|=(2715798533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-879202481/5000000000 : ℝ)|^4529 ≤ (5291116484707/50000000000000 : ℝ)^3505
        have hw : |(-879202481/5000000000 : ℝ)|=(879202481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_s6_5 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133374351/312500000 : ℝ)*x 0 + (903124103/2000000000 : ℝ)*x 1 + (806411643/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133374351/312500000 : ℝ)^4529 ≤ (33280530337179/100000000000000 : ℝ)^3505 := by
    have hnat : (133374351 : ℕ)^4529*100000000000000^3505 ≤ 33280530337179^3505*312500000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133374351 312500000 33280530337179 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903124103/2000000000 : ℝ)^4529 ≤ (7159319243971/20000000000000 : ℝ)^3505 := by
    have hnat : (903124103 : ℕ)^4529*20000000000000^3505 ≤ 7159319243971^3505*2000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903124103 2000000000 7159319243971 20000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (806411643/2000000000 : ℝ)^4529 ≤ (15461436716567/50000000000000 : ℝ)^3505 := by
    have hnat : (806411643 : ℕ)^4529*50000000000000^3505 ≤ 15461436716567^3505*2000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806411643 2000000000 15461436716567 50000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133374351/312500000 : ℝ), (903124103/2000000000 : ℝ), (806411643/2000000000 : ℝ)] ![(33280530337179/100000000000000 : ℝ), (7159319243971/20000000000000 : ℝ), (15461436716567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133374351/312500000 : ℝ)|^4529 ≤ (33280530337179/100000000000000 : ℝ)^3505
        have hw : |(133374351/312500000 : ℝ)|=(133374351/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(903124103/2000000000 : ℝ)|^4529 ≤ (7159319243971/20000000000000 : ℝ)^3505
        have hw : |(903124103/2000000000 : ℝ)|=(903124103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(806411643/2000000000 : ℝ)|^4529 ≤ (15461436716567/50000000000000 : ℝ)^3505
        have hw : |(806411643/2000000000 : ℝ)|=(806411643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1516_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20462363/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10931/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10931/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7741/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10931/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10931/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10931/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10931/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10931/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10931/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (10931/100000 : ℝ) ^ (4527/1024 : ℝ) ≤ (2811790978295139/50000000000000000000 : ℝ) := by
    have hpowers : (10931/100000 : ℝ)^4527 ≤ (2811790978295139/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10931 : ℕ)^4527*50000000000000000000^1024 ≤ 2811790978295139^1024*100000^4527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10931 100000 2811790978295139 50000000000000000000 4527 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10931/100000 : ℝ)) (X := (2811790978295139/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15483/100000 : ℝ) ^ (4527/1024 : ℝ) ≤ (13103935379195541/50000000000000000000 : ℝ) := by
    have hpowers : (15483/100000 : ℝ)^4527 ≤ (13103935379195541/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15483 : ℕ)^4527*50000000000000000000^1024 ≤ 13103935379195541^1024*100000^4527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15483 100000 13103935379195541 50000000000000000000 4527 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15483/100000 : ℝ)) (X := (13103935379195541/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002811790978295139/25000000000000000000 : ℝ) ≤ (625015899871203/625000000000000 : ℝ) ^ (4527/1024 : ℝ) := by
    have hpowers : (25002811790978295139/25000000000000000000 : ℝ)^1024 ≤ (625015899871203/625000000000000 : ℝ)^4527 := by
      have hnat : (25002811790978295139 : ℕ)^1024*625000000000000^4527 ≤ 625015899871203^4527*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002811790978295139 25000000000000000000 625015899871203 625000000000000 1024 4527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625015899871203/625000000000000 : ℝ)) (X := (25002811790978295139/25000000000000000000 : ℝ)) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1250397893158937267/1250000000000000000 : ℝ) ≤ (2500179983399661/2500000000000000 : ℝ) ^ (4527/1024 : ℝ) := by
    have hpowers : (1250397893158937267/1250000000000000000 : ℝ)^1024 ≤ (2500179983399661/2500000000000000 : ℝ)^4527 := by
      have hnat : (1250397893158937267 : ℕ)^1024*2500000000000000^4527 ≤ 2500179983399661^4527*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250397893158937267 1250000000000000000 2500179983399661 2500000000000000 1024 4527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500179983399661/2500000000000000 : ℝ)) (X := (1250397893158937267/1250000000000000000 : ℝ)) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013103935379195541/25000000000000000000 : ℝ) ≤ (250029636731451/250000000000000 : ℝ) ^ (4527/1024 : ℝ) := by
    have hpowers : (25013103935379195541/25000000000000000000 : ℝ)^1024 ≤ (250029636731451/250000000000000 : ℝ)^4527 := by
      have hnat : (25013103935379195541 : ℕ)^1024*250000000000000^4527 ≤ 250029636731451^4527*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013103935379195541 25000000000000000000 250029636731451 250000000000000 1024 4527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250029636731451/250000000000000 : ℝ)) (X := (25013103935379195541/25000000000000000000 : ℝ)) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2811790978295139/50000000000000000000 : ℝ) ≤ ((5688872559854217693/5690000000000000000 : ℝ)+2*(116383914849/113800000000000 : ℝ)*(10931/100000 : ℝ))^(4527/1024 : ℝ) := by
    rw [show (5688872559854217693/5690000000000000000 : ℝ)+2*(116383914849/113800000000000 : ℝ)*(10931/100000 : ℝ)=(625015899871203/625000000000000 : ℝ) by norm_num, show 1+2*(2811790978295139/50000000000000000000 : ℝ)=(25002811790978295139/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13103935379195541/50000000000000000000 : ℝ)+(2811790978295139/50000000000000000000 : ℝ) ≤ ((5688872559854217693/5690000000000000000 : ℝ)+(116383914849/113800000000000 : ℝ)*((15483/100000 : ℝ)+(10931/100000 : ℝ)))^(4527/1024 : ℝ) := by
    rw [show (5688872559854217693/5690000000000000000 : ℝ)+(116383914849/113800000000000 : ℝ)*((15483/100000 : ℝ)+(10931/100000 : ℝ))=(2500179983399661/2500000000000000 : ℝ) by norm_num, show 1+(13103935379195541/50000000000000000000 : ℝ)+(2811790978295139/50000000000000000000 : ℝ)=(1250397893158937267/1250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13103935379195541/50000000000000000000 : ℝ) ≤ ((5688872559854217693/5690000000000000000 : ℝ)+2*(116383914849/113800000000000 : ℝ)*(15483/100000 : ℝ))^(4527/1024 : ℝ) := by
    rw [show (5688872559854217693/5690000000000000000 : ℝ)+2*(116383914849/113800000000000 : ℝ)*(15483/100000 : ℝ)=(250029636731451/250000000000000 : ℝ) by norm_num, show 1+2*(13103935379195541/50000000000000000000 : ℝ)=(25013103935379195541/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5688872559854217693/5690000000000000000 : ℝ)*(X 1 0+X 2 0)+(116383914849/113800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4527/1024 : ℝ)) (lo := (10931/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (5688872559854217693/5690000000000000000 : ℝ)) (alpha := (116383914849/113800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5688872559854217693/5690000000000000000 : ℝ)*(X 0 1+X 2 1)+(116383914849/113800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4527/1024 : ℝ)) (lo := (10931/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (5688872559854217693/5690000000000000000 : ℝ)) (alpha := (116383914849/113800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5688872559854217693/5690000000000000000 : ℝ)*(X 0 2+X 1 2)+(116383914849/113800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4527/1024 : ℝ)) (lo := (10931/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (5688872559854217693/5690000000000000000 : ℝ)) (alpha := (116383914849/113800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5351366719/10000000000 : ℝ)*X 2 0+(5217838427/10000000000 : ℝ)*X 2 1+(-394432579/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s6_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2133956609/5000000000 : ℝ)*X 0 0+(503690281/1250000000 : ℝ)*X 0 1+(2259069221/5000000000 : ℝ)*X 0 2+(2133956609/5000000000 : ℝ)*X 1 0+(503690281/1250000000 : ℝ)*X 1 1+(2259069221/5000000000 : ℝ)*X 1 2+(2133956609/5000000000 : ℝ)*X 2 0+(503690281/1250000000 : ℝ)*X 2 1+(2259069221/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s6_1 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-931076189/5000000000 : ℝ)*X 0 0+(2609472927/5000000000 : ℝ)*X 0 1+(2715798033/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s6_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5294925183/10000000000 : ℝ)*X 1 0+(-1758405287/10000000000 : ℝ)*X 1 1+(5431596997/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s6_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((5294925349/10000000000 : ℝ)*X 2 0+(2715798533/5000000000 : ℝ)*X 2 1+(-879202481/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s6_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((133374351/312500000 : ℝ)*X 0 0+(903124103/2000000000 : ℝ)*X 0 1+(806411643/2000000000 : ℝ)*X 0 2+(133374351/312500000 : ℝ)*X 1 0+(903124103/2000000000 : ℝ)*X 1 1+(806411643/2000000000 : ℝ)*X 1 2+(133374351/312500000 : ℝ)*X 2 0+(903124103/2000000000 : ℝ)*X 2 1+(806411643/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_s6_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (201297535783795771453278723/56900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8011309/6250000000000 : ℝ)*(base8) + (186843667/20000000000000 : ℝ)*(base15) + (26953157/50000000000000 : ℝ)*(lower2) + (44504347/12500000000000 : ℝ)*(lower4) + (270607/500000000000 : ℝ)*(upper5) + (677052838127079/20000000000000 : ℝ)*(major0) + (677052838127079/20000000000000 : ℝ)*(major1) + (677052838127079/20000000000000 : ℝ)*(major2) + (2629542357/25000000000000 : ℝ)*(sp0) + (1163650957/100000000000000 : ℝ)*(sp1) + (940509187726939/20000000000000 : ℝ)*(sp2) + (587818141574663/12500000000000 : ℝ)*(sp3) + (4702535548646211/100000000000000 : ℝ)*(sp4) + (1033990516439723/50000000000000 : ℝ)*(sp5) + (2067982196530403/100000000000000 : ℝ)*(f.failure) + (4702546066815639/100000000000000 : ℝ)*(f.sum) + (14098467774527/1138000000000000000000000000 : ℝ)*base65 + (142499525605041253/113800000000000000000000000000000 : ℝ)*base68 + (859191122737441253/113800000000000000000000000000000 : ℝ)*base70 + (894966881206241253/113800000000000000000000000000000 : ℝ)*base72 + (2724722091293/1138000000000000000000000000 : ℝ)*base74 + (454471234345841253/113800000000000000000000000000000 : ℝ)*base76 + (657314100904441253/113800000000000000000000000000000 : ℝ)*base78 + (502542486502641253/113800000000000000000000000000000 : ℝ)*base80 + (152103247/9104000000000000000000000 : ℝ)*base81 + (9222289/1250000000000000000000 : ℝ)*base89 + (9222289/1250000000000000000000 : ℝ)*base91 + (9222289/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1516_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20462363/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10931/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10931/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1516_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1516_box_0 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-103075759/625000000 : ℝ)*x 0 + (5402399341/10000000000 : ℝ)*x 1 + (1350600003/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103075759/625000000 : ℝ)^4529 ≤ (487046786967/5000000000000 : ℝ)^3505 := by
    have hnat : (103075759 : ℕ)^4529*5000000000000^3505 ≤ 487046786967^3505*625000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103075759 625000000 487046786967 5000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402399341/10000000000 : ℝ)^4529 ≤ (45129528502571/100000000000000 : ℝ)^3505 := by
    have hnat : (5402399341 : ℕ)^4529*100000000000000^3505 ≤ 45129528502571^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402399341 10000000000 45129528502571 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350600003/2500000000 : ℝ)^4529 ≤ (9025907149089/20000000000000 : ℝ)^3505 := by
    have hnat : (1350600003 : ℕ)^4529*20000000000000^3505 ≤ 9025907149089^3505*2500000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350600003 2500000000 9025907149089 20000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-103075759/625000000 : ℝ), (5402399341/10000000000 : ℝ), (1350600003/2500000000 : ℝ)] ![(487046786967/5000000000000 : ℝ), (45129528502571/100000000000000 : ℝ), (9025907149089/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-103075759/625000000 : ℝ)|^4529 ≤ (487046786967/5000000000000 : ℝ)^3505
        have hw : |(-103075759/625000000 : ℝ)|=(103075759/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402399341/10000000000 : ℝ)|^4529 ≤ (45129528502571/100000000000000 : ℝ)^3505
        have hw : |(5402399341/10000000000 : ℝ)|=(5402399341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350600003/2500000000 : ℝ)|^4529 ≤ (9025907149089/20000000000000 : ℝ)^3505
        have hw : |(1350600003/2500000000 : ℝ)|=(1350600003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_box_1 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329426681/625000000 : ℝ)*x 0 + (-1831755679/10000000000 : ℝ)*x 1 + (1080479901/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329426681/625000000 : ℝ)^4529 ≤ (43714397844161/100000000000000 : ℝ)^3505 := by
    have hnat : (329426681 : ℕ)^4529*100000000000000^3505 ≤ 43714397844161^3505*625000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329426681 625000000 43714397844161 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1831755679/10000000000 : ℝ)^4529 ≤ (11156071872179/100000000000000 : ℝ)^3505 := by
    have hnat : (1831755679 : ℕ)^4529*100000000000000^3505 ≤ 11156071872179^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1831755679 10000000000 11156071872179 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080479901/2000000000 : ℝ)^4529 ≤ (45129530272811/100000000000000 : ℝ)^3505 := by
    have hnat : (1080479901 : ℕ)^4529*100000000000000^3505 ≤ 45129530272811^3505*2000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080479901 2000000000 45129530272811 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329426681/625000000 : ℝ), (-1831755679/10000000000 : ℝ), (1080479901/2000000000 : ℝ)] ![(43714397844161/100000000000000 : ℝ), (11156071872179/100000000000000 : ℝ), (45129530272811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329426681/625000000 : ℝ)|^4529 ≤ (43714397844161/100000000000000 : ℝ)^3505
        have hw : |(329426681/625000000 : ℝ)|=(329426681/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1831755679/10000000000 : ℝ)|^4529 ≤ (11156071872179/100000000000000 : ℝ)^3505
        have hw : |(-1831755679/10000000000 : ℝ)|=(1831755679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080479901/2000000000 : ℝ)|^4529 ≤ (45129530272811/100000000000000 : ℝ)^3505
        have hw : |(1080479901/2000000000 : ℝ)|=(1080479901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_box_2 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270826347/10000000000 : ℝ)*x 0 + (540239973/1000000000 : ℝ)*x 1 + (-915878059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270826347/10000000000 : ℝ)^4529 ≤ (43714391960707/100000000000000 : ℝ)^3505 := by
    have hnat : (5270826347 : ℕ)^4529*100000000000000^3505 ≤ 43714391960707^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270826347 10000000000 43714391960707 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540239973/1000000000 : ℝ)^4529 ≤ (9025906540299/20000000000000 : ℝ)^3505 := by
    have hnat : (540239973 : ℕ)^4529*20000000000000^3505 ≤ 9025906540299^3505*1000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540239973 1000000000 9025906540299 20000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (915878059/5000000000 : ℝ)^4529 ≤ (11156075326977/100000000000000 : ℝ)^3505 := by
    have hnat : (915878059 : ℕ)^4529*100000000000000^3505 ≤ 11156075326977^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      915878059 5000000000 11156075326977 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270826347/10000000000 : ℝ), (540239973/1000000000 : ℝ), (-915878059/5000000000 : ℝ)] ![(43714391960707/100000000000000 : ℝ), (9025906540299/20000000000000 : ℝ), (11156075326977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270826347/10000000000 : ℝ)|^4529 ≤ (43714391960707/100000000000000 : ℝ)^3505
        have hw : |(5270826347/10000000000 : ℝ)|=(5270826347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540239973/1000000000 : ℝ)|^4529 ≤ (9025906540299/20000000000000 : ℝ)^3505
        have hw : |(540239973/1000000000 : ℝ)|=(540239973/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-915878059/5000000000 : ℝ)|^4529 ≤ (11156075326977/100000000000000 : ℝ)^3505
        have hw : |(-915878059/5000000000 : ℝ)|=(915878059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_box_3 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4470796321/10000000000 : ℝ)*x 0 + (4173428071/10000000000 : ℝ)*x 1 + (4173427321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4470796321/10000000000 : ℝ)^4529 ≤ (35338117267981/100000000000000 : ℝ)^3505 := by
    have hnat : (4470796321 : ℕ)^4529*100000000000000^3505 ≤ 35338117267981^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4470796321 10000000000 35338117267981 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4173428071/10000000000 : ℝ)^4529 ≤ (8082736277223/25000000000000 : ℝ)^3505 := by
    have hnat : (4173428071 : ℕ)^4529*25000000000000^3505 ≤ 8082736277223^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4173428071 10000000000 8082736277223 25000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4173427321/10000000000 : ℝ)^4529 ≤ (16165468800647/50000000000000 : ℝ)^3505 := by
    have hnat : (4173427321 : ℕ)^4529*50000000000000^3505 ≤ 16165468800647^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4173427321 10000000000 16165468800647 50000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4470796321/10000000000 : ℝ), (4173428071/10000000000 : ℝ), (4173427321/10000000000 : ℝ)] ![(35338117267981/100000000000000 : ℝ), (8082736277223/25000000000000 : ℝ), (16165468800647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4470796321/10000000000 : ℝ)|^4529 ≤ (35338117267981/100000000000000 : ℝ)^3505
        have hw : |(4470796321/10000000000 : ℝ)|=(4470796321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4173428071/10000000000 : ℝ)|^4529 ≤ (8082736277223/25000000000000 : ℝ)^3505
        have hw : |(4173428071/10000000000 : ℝ)|=(4173428071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4173427321/10000000000 : ℝ)|^4529 ≤ (16165468800647/50000000000000 : ℝ)^3505
        have hw : |(4173427321/10000000000 : ℝ)|=(4173427321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_box_4 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-208047589/1000000000 : ℝ)*x 0 + (5243753273/10000000000 : ℝ)*x 1 + (1310937737/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208047589/1000000000 : ℝ)^4529 ≤ (13151071660109/100000000000000 : ℝ)^3505 := by
    have hnat : (208047589 : ℕ)^4529*100000000000000^3505 ≤ 13151071660109^3505*1000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208047589 1000000000 13151071660109 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243753273/10000000000 : ℝ)^4529 ≤ (21712238299241/50000000000000 : ℝ)^3505 := by
    have hnat : (5243753273 : ℕ)^4529*50000000000000^3505 ≤ 21712238299241^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243753273 10000000000 21712238299241 50000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310937737/2500000000 : ℝ)^4529 ≤ (21712225859837/50000000000000 : ℝ)^3505 := by
    have hnat : (1310937737 : ℕ)^4529*50000000000000^3505 ≤ 21712225859837^3505*2500000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310937737 2500000000 21712225859837 50000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-208047589/1000000000 : ℝ), (5243753273/10000000000 : ℝ), (1310937737/2500000000 : ℝ)] ![(13151071660109/100000000000000 : ℝ), (21712238299241/50000000000000 : ℝ), (21712225859837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-208047589/1000000000 : ℝ)|^4529 ≤ (13151071660109/100000000000000 : ℝ)^3505
        have hw : |(-208047589/1000000000 : ℝ)|=(208047589/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243753273/10000000000 : ℝ)|^4529 ≤ (21712238299241/50000000000000 : ℝ)^3505
        have hw : |(5243753273/10000000000 : ℝ)|=(5243753273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310937737/2500000000 : ℝ)|^4529 ≤ (21712225859837/50000000000000 : ℝ)^3505
        have hw : |(1310937737/2500000000 : ℝ)|=(1310937737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_box_5 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690622671/5000000000 : ℝ)*x 0 + (-1897255831/10000000000 : ℝ)*x 1 + (5243752821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690622671/5000000000 : ℝ)^4529 ≤ (44901319812807/100000000000000 : ℝ)^3505 := by
    have hnat : (2690622671 : ℕ)^4529*100000000000000^3505 ≤ 44901319812807^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690622671 5000000000 44901319812807 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1897255831/10000000000 : ℝ)^4529 ≤ (1459276050699/12500000000000 : ℝ)^3505 := by
    have hnat : (1897255831 : ℕ)^4529*12500000000000^3505 ≤ 1459276050699^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1897255831 10000000000 1459276050699 12500000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243752821/10000000000 : ℝ)^4529 ≤ (43424471761827/100000000000000 : ℝ)^3505 := by
    have hnat : (5243752821 : ℕ)^4529*100000000000000^3505 ≤ 43424471761827^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243752821 10000000000 43424471761827 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690622671/5000000000 : ℝ), (-1897255831/10000000000 : ℝ), (5243752821/10000000000 : ℝ)] ![(44901319812807/100000000000000 : ℝ), (1459276050699/12500000000000 : ℝ), (43424471761827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690622671/5000000000 : ℝ)|^4529 ≤ (44901319812807/100000000000000 : ℝ)^3505
        have hw : |(2690622671/5000000000 : ℝ)|=(2690622671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1897255831/10000000000 : ℝ)|^4529 ≤ (1459276050699/12500000000000 : ℝ)^3505
        have hw : |(-1897255831/10000000000 : ℝ)|=(1897255831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243752821/10000000000 : ℝ)|^4529 ≤ (43424471761827/100000000000000 : ℝ)^3505
        have hw : |(5243752821/10000000000 : ℝ)|=(5243752821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_box_6 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5381247323/10000000000 : ℝ)*x 0 + (5243750721/10000000000 : ℝ)*x 1 + (-474313993/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381247323/10000000000 : ℝ)^4529 ≤ (44901341171521/100000000000000 : ℝ)^3505 := by
    have hnat : (5381247323 : ℕ)^4529*100000000000000^3505 ≤ 44901341171521^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381247323 10000000000 44901341171521 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243750721/10000000000 : ℝ)^4529 ≤ (21712224645323/50000000000000 : ℝ)^3505 := by
    have hnat : (5243750721 : ℕ)^4529*50000000000000^3505 ≤ 21712224645323^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243750721 10000000000 21712224645323 50000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (474313993/2500000000 : ℝ)^4529 ≤ (11674209526667/100000000000000 : ℝ)^3505 := by
    have hnat : (474313993 : ℕ)^4529*100000000000000^3505 ≤ 11674209526667^3505*2500000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474313993 2500000000 11674209526667 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381247323/10000000000 : ℝ), (5243750721/10000000000 : ℝ), (-474313993/2500000000 : ℝ)] ![(44901341171521/100000000000000 : ℝ), (21712224645323/50000000000000 : ℝ), (11674209526667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381247323/10000000000 : ℝ)|^4529 ≤ (44901341171521/100000000000000 : ℝ)^3505
        have hw : |(5381247323/10000000000 : ℝ)|=(5381247323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243750721/10000000000 : ℝ)|^4529 ≤ (21712224645323/50000000000000 : ℝ)^3505
        have hw : |(5243750721/10000000000 : ℝ)|=(5243750721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-474313993/2500000000 : ℝ)|^4529 ≤ (11674209526667/100000000000000 : ℝ)^3505
        have hw : |(-474313993/2500000000 : ℝ)|=(474313993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_box_7 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4062591729/10000000000 : ℝ)*x 0 + (2188698087/5000000000 : ℝ)*x 1 + (547174533/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4062591729/10000000000 : ℝ)^4529 ≤ (31225790282127/100000000000000 : ℝ)^3505 := by
    have hnat : (4062591729 : ℕ)^4529*100000000000000^3505 ≤ 31225790282127^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4062591729 10000000000 31225790282127 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2188698087/5000000000 : ℝ)^4529 ≤ (6877420878229/20000000000000 : ℝ)^3505 := by
    have hnat : (2188698087 : ℕ)^4529*20000000000000^3505 ≤ 6877420878229^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188698087 5000000000 6877420878229 20000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547174533/1250000000 : ℝ)^4529 ≤ (268649260193/781250000000 : ℝ)^3505 := by
    have hnat : (547174533 : ℕ)^4529*781250000000^3505 ≤ 268649260193^3505*1250000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547174533 1250000000 268649260193 781250000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4062591729/10000000000 : ℝ), (2188698087/5000000000 : ℝ), (547174533/1250000000 : ℝ)] ![(31225790282127/100000000000000 : ℝ), (6877420878229/20000000000000 : ℝ), (268649260193/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4062591729/10000000000 : ℝ)|^4529 ≤ (31225790282127/100000000000000 : ℝ)^3505
        have hw : |(4062591729/10000000000 : ℝ)|=(4062591729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2188698087/5000000000 : ℝ)|^4529 ≤ (6877420878229/20000000000000 : ℝ)^3505
        have hw : |(2188698087/5000000000 : ℝ)|=(2188698087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(547174533/1250000000 : ℝ)|^4529 ≤ (268649260193/781250000000 : ℝ)^3505
        have hw : |(547174533/1250000000 : ℝ)|=(547174533/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_box_8 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1989318699/10000000000 : ℝ)*x 0 + (5132562799/10000000000 : ℝ)*x 1 + (1084568179/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1989318699/10000000000 : ℝ)^4529 ≤ (12411320593063/100000000000000 : ℝ)^3505 := by
    have hnat : (1989318699 : ℕ)^4529*100000000000000^3505 ≤ 12411320593063^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989318699 10000000000 12411320593063 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5132562799/10000000000 : ℝ)^4529 ≤ (2111918993523/5000000000000 : ℝ)^3505 := by
    have hnat : (5132562799 : ℕ)^4529*5000000000000^3505 ≤ 2111918993523^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5132562799 10000000000 2111918993523 5000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084568179/2000000000 : ℝ)^4529 ≤ (22675149766481/50000000000000 : ℝ)^3505 := by
    have hnat : (1084568179 : ℕ)^4529*50000000000000^3505 ≤ 22675149766481^3505*2000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084568179 2000000000 22675149766481 50000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1989318699/10000000000 : ℝ), (5132562799/10000000000 : ℝ), (1084568179/2000000000 : ℝ)] ![(12411320593063/100000000000000 : ℝ), (2111918993523/5000000000000 : ℝ), (22675149766481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1989318699/10000000000 : ℝ)|^4529 ≤ (12411320593063/100000000000000 : ℝ)^3505
        have hw : |(-1989318699/10000000000 : ℝ)|=(1989318699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5132562799/10000000000 : ℝ)|^4529 ≤ (2111918993523/5000000000000 : ℝ)^3505
        have hw : |(5132562799/10000000000 : ℝ)|=(5132562799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084568179/2000000000 : ℝ)|^4529 ≤ (22675149766481/50000000000000 : ℝ)^3505
        have hw : |(1084568179/2000000000 : ℝ)|=(1084568179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_box_9 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (65707421/125000000 : ℝ)*x 0 + (-227883927/1250000000 : ℝ)*x 1 + (1355710187/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65707421/125000000 : ℝ)^4529 ≤ (43561925306181/100000000000000 : ℝ)^3505 := by
    have hnat : (65707421 : ℕ)^4529*100000000000000^3505 ≤ 43561925306181^3505*125000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65707421 125000000 43561925306181 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (227883927/1250000000 : ℝ)^4529 ≤ (11087776730063/100000000000000 : ℝ)^3505 := by
    have hnat : (227883927 : ℕ)^4529*100000000000000^3505 ≤ 11087776730063^3505*1250000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227883927 1250000000 11087776730063 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355710187/2500000000 : ℝ)^4529 ≤ (45350297944471/100000000000000 : ℝ)^3505 := by
    have hnat : (1355710187 : ℕ)^4529*100000000000000^3505 ≤ 45350297944471^3505*2500000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355710187 2500000000 45350297944471 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65707421/125000000 : ℝ), (-227883927/1250000000 : ℝ), (1355710187/2500000000 : ℝ)] ![(43561925306181/100000000000000 : ℝ), (11087776730063/100000000000000 : ℝ), (45350297944471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65707421/125000000 : ℝ)|^4529 ≤ (43561925306181/100000000000000 : ℝ)^3505
        have hw : |(65707421/125000000 : ℝ)|=(65707421/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-227883927/1250000000 : ℝ)|^4529 ≤ (11087776730063/100000000000000 : ℝ)^3505
        have hw : |(-227883927/1250000000 : ℝ)|=(227883927/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355710187/2500000000 : ℝ)|^4529 ≤ (45350297944471/100000000000000 : ℝ)^3505
        have hw : |(1355710187/2500000000 : ℝ)|=(1355710187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_box_10 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256593969/10000000000 : ℝ)*x 0 + (135571007/250000000 : ℝ)*x 1 + (-1823071667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256593969/10000000000 : ℝ)^4529 ≤ (8712385680171/20000000000000 : ℝ)^3505 := by
    have hnat : (5256593969 : ℕ)^4529*20000000000000^3505 ≤ 8712385680171^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256593969 10000000000 8712385680171 20000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135571007/250000000 : ℝ)^4529 ≤ (708598326363/1562500000000 : ℝ)^3505 := by
    have hnat : (135571007 : ℕ)^4529*1562500000000^3505 ≤ 708598326363^3505*250000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135571007 250000000 708598326363 1562500000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1823071667/10000000000 : ℝ)^4529 ≤ (11087778702617/100000000000000 : ℝ)^3505 := by
    have hnat : (1823071667 : ℕ)^4529*100000000000000^3505 ≤ 11087778702617^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1823071667 10000000000 11087778702617 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256593969/10000000000 : ℝ), (135571007/250000000 : ℝ), (-1823071667/10000000000 : ℝ)] ![(8712385680171/20000000000000 : ℝ), (708598326363/1562500000000 : ℝ), (11087778702617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256593969/10000000000 : ℝ)|^4529 ≤ (8712385680171/20000000000000 : ℝ)^3505
        have hw : |(5256593969/10000000000 : ℝ)|=(5256593969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135571007/250000000 : ℝ)|^4529 ≤ (708598326363/1562500000000 : ℝ)^3505
        have hw : |(135571007/250000000 : ℝ)|=(135571007/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1823071667/10000000000 : ℝ)|^4529 ≤ (11087778702617/100000000000000 : ℝ)^3505
        have hw : |(-1823071667/10000000000 : ℝ)|=(1823071667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_box_11 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (565280029/1250000000 : ℝ)*x 0 + (1036778669/2500000000 : ℝ)*x 1 + (4147115341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (565280029/1250000000 : ℝ)^4529 ≤ (35864418279781/100000000000000 : ℝ)^3505 := by
    have hnat : (565280029 : ℕ)^4529*100000000000000^3505 ≤ 35864418279781^3505*1250000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565280029 1250000000 35864418279781 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036778669/2500000000 : ℝ)^4529 ≤ (32067787532261/100000000000000 : ℝ)^3505 := by
    have hnat : (1036778669 : ℕ)^4529*100000000000000^3505 ≤ 32067787532261^3505*2500000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036778669 2500000000 32067787532261 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4147115341/10000000000 : ℝ)^4529 ≤ (32067794176709/100000000000000 : ℝ)^3505 := by
    have hnat : (4147115341 : ℕ)^4529*100000000000000^3505 ≤ 32067794176709^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4147115341 10000000000 32067794176709 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(565280029/1250000000 : ℝ), (1036778669/2500000000 : ℝ), (4147115341/10000000000 : ℝ)] ![(35864418279781/100000000000000 : ℝ), (32067787532261/100000000000000 : ℝ), (32067794176709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(565280029/1250000000 : ℝ)|^4529 ≤ (35864418279781/100000000000000 : ℝ)^3505
        have hw : |(565280029/1250000000 : ℝ)|=(565280029/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036778669/2500000000 : ℝ)|^4529 ≤ (32067787532261/100000000000000 : ℝ)^3505
        have hw : |(1036778669/2500000000 : ℝ)|=(1036778669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4147115341/10000000000 : ℝ)|^4529 ≤ (32067794176709/100000000000000 : ℝ)^3505
        have hw : |(4147115341/10000000000 : ℝ)|=(4147115341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_box_12 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1740297917/10000000000 : ℝ)*x 0 + (5510028231/10000000000 : ℝ)*x 1 + (5228722329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1740297917/10000000000 : ℝ)^4529 ≤ (5220819784459/50000000000000 : ℝ)^3505 := by
    have hnat : (1740297917 : ℕ)^4529*50000000000000^3505 ≤ 5220819784459^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1740297917 10000000000 5220819784459 50000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5510028231/10000000000 : ℝ)^4529 ≤ (46294655995187/100000000000000 : ℝ)^3505 := by
    have hnat : (5510028231 : ℕ)^4529*100000000000000^3505 ≤ 46294655995187^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510028231 10000000000 46294655995187 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228722329/10000000000 : ℝ)^4529 ≤ (21631852211499/50000000000000 : ℝ)^3505 := by
    have hnat : (5228722329 : ℕ)^4529*50000000000000^3505 ≤ 21631852211499^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228722329 10000000000 21631852211499 50000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1740297917/10000000000 : ℝ), (5510028231/10000000000 : ℝ), (5228722329/10000000000 : ℝ)] ![(5220819784459/50000000000000 : ℝ), (46294655995187/100000000000000 : ℝ), (21631852211499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1740297917/10000000000 : ℝ)|^4529 ≤ (5220819784459/50000000000000 : ℝ)^3505
        have hw : |(-1740297917/10000000000 : ℝ)|=(1740297917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5510028231/10000000000 : ℝ)|^4529 ≤ (46294655995187/100000000000000 : ℝ)^3505
        have hw : |(5510028231/10000000000 : ℝ)|=(5510028231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228722329/10000000000 : ℝ)|^4529 ≤ (21631852211499/50000000000000 : ℝ)^3505
        have hw : |(5228722329/10000000000 : ℝ)|=(5228722329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_box_13 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2695853509/5000000000 : ℝ)*x 0 + (-475820589/2500000000 : ℝ)*x 1 + (2614361227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2695853509/5000000000 : ℝ)^4529 ≤ (1406692104931/3125000000000 : ℝ)^3505 := by
    have hnat : (2695853509 : ℕ)^4529*3125000000000^3505 ≤ 1406692104931^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695853509 5000000000 1406692104931 3125000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (475820589/2500000000 : ℝ)^4529 ≤ (11722146870631/100000000000000 : ℝ)^3505 := by
    have hnat : (475820589 : ℕ)^4529*100000000000000^3505 ≤ 11722146870631^3505*2500000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475820589 2500000000 11722146870631 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614361227/5000000000 : ℝ)^4529 ≤ (43263705759447/100000000000000 : ℝ)^3505 := by
    have hnat : (2614361227 : ℕ)^4529*100000000000000^3505 ≤ 43263705759447^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614361227 5000000000 43263705759447 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2695853509/5000000000 : ℝ), (-475820589/2500000000 : ℝ), (2614361227/5000000000 : ℝ)] ![(1406692104931/3125000000000 : ℝ), (11722146870631/100000000000000 : ℝ), (43263705759447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2695853509/5000000000 : ℝ)|^4529 ≤ (1406692104931/3125000000000 : ℝ)^3505
        have hw : |(2695853509/5000000000 : ℝ)|=(2695853509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-475820589/2500000000 : ℝ)|^4529 ≤ (11722146870631/100000000000000 : ℝ)^3505
        have hw : |(-475820589/2500000000 : ℝ)|=(475820589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614361227/5000000000 : ℝ)|^4529 ≤ (43263705759447/100000000000000 : ℝ)^3505
        have hw : |(2614361227/5000000000 : ℝ)|=(2614361227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_box_14 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5391706931/10000000000 : ℝ)*x 0 + (130718063/250000000 : ℝ)*x 1 + (-951641193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5391706931/10000000000 : ℝ)^4529 ≤ (11253536604811/25000000000000 : ℝ)^3505 := by
    have hnat : (5391706931 : ℕ)^4529*25000000000000^3505 ≤ 11253536604811^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391706931 10000000000 11253536604811 25000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130718063/250000000 : ℝ)^4529 ≤ (10815926616273/25000000000000 : ℝ)^3505 := by
    have hnat : (130718063 : ℕ)^4529*25000000000000^3505 ≤ 10815926616273^3505*250000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130718063 250000000 10815926616273 25000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (951641193/5000000000 : ℝ)^4529 ≤ (11722147109379/100000000000000 : ℝ)^3505 := by
    have hnat : (951641193 : ℕ)^4529*100000000000000^3505 ≤ 11722147109379^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      951641193 5000000000 11722147109379 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5391706931/10000000000 : ℝ), (130718063/250000000 : ℝ), (-951641193/5000000000 : ℝ)] ![(11253536604811/25000000000000 : ℝ), (10815926616273/25000000000000 : ℝ), (11722147109379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5391706931/10000000000 : ℝ)|^4529 ≤ (11253536604811/25000000000000 : ℝ)^3505
        have hw : |(5391706931/10000000000 : ℝ)|=(5391706931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130718063/250000000 : ℝ)|^4529 ≤ (10815926616273/25000000000000 : ℝ)^3505
        have hw : |(130718063/250000000 : ℝ)|=(130718063/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-951641193/5000000000 : ℝ)|^4529 ≤ (11722147109379/100000000000000 : ℝ)^3505
        have hw : |(-951641193/5000000000 : ℝ)|=(951641193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1516_box_15 (p : ℝ) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4023058843/10000000000 : ℝ)*x 0 + (2198348233/5000000000 : ℝ)*x 1 + (68698379/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4023058843/10000000000 : ℝ)^4529 ≤ (30833720043927/100000000000000 : ℝ)^3505 := by
    have hnat : (4023058843 : ℕ)^4529*100000000000000^3505 ≤ 30833720043927^3505*10000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023058843 10000000000 30833720043927 100000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2198348233/5000000000 : ℝ)^4529 ≤ (1383325641509/4000000000000 : ℝ)^3505 := by
    have hnat : (2198348233 : ℕ)^4529*4000000000000^3505 ≤ 1383325641509^3505*5000000000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198348233 5000000000 1383325641509 4000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68698379/156250000 : ℝ)^4529 ≤ (17291569451673/50000000000000 : ℝ)^3505 := by
    have hnat : (68698379 : ℕ)^4529*50000000000000^3505 ≤ 17291569451673^3505*156250000^4529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68698379 156250000 17291569451673 50000000000000 4529 3505 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4529/1024 : ℝ)) 4529 3505 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4023058843/10000000000 : ℝ), (2198348233/5000000000 : ℝ), (68698379/156250000 : ℝ)] ![(30833720043927/100000000000000 : ℝ), (1383325641509/4000000000000 : ℝ), (17291569451673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4023058843/10000000000 : ℝ)|^4529 ≤ (30833720043927/100000000000000 : ℝ)^3505
        have hw : |(4023058843/10000000000 : ℝ)|=(4023058843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2198348233/5000000000 : ℝ)|^4529 ≤ (1383325641509/4000000000000 : ℝ)^3505
        have hw : |(2198348233/5000000000 : ℝ)|=(2198348233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68698379/156250000 : ℝ)|^4529 ≤ (17291569451673/50000000000000 : ℝ)^3505
        have hw : |(68698379/156250000 : ℝ)|=(68698379/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1516_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20462363/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10931/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12749/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29323/50000 : ℝ) ∧ (40181/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (21507/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10931/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10931/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10931/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10931/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10931/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10931/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10931/100000 : ℝ) ^ (4527/1024 : ℝ) ≤ (2811790978295139/50000000000000000000 : ℝ) := by
    have hpowers : (10931/100000 : ℝ)^4527 ≤ (2811790978295139/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10931 : ℕ)^4527*50000000000000000000^1024 ≤ 2811790978295139^1024*100000^4527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10931 100000 2811790978295139 50000000000000000000 4527 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10931/100000 : ℝ)) (X := (2811790978295139/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7741/50000 : ℝ) ^ (4527/1024 : ℝ) ≤ (6550097097078151/25000000000000000000 : ℝ) := by
    have hpowers : (7741/50000 : ℝ)^4527 ≤ (6550097097078151/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7741 : ℕ)^4527*25000000000000000000^1024 ≤ 6550097097078151^1024*50000^4527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7741 50000 6550097097078151 25000000000000000000 4527 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7741/50000 : ℝ)) (X := (6550097097078151/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002811790978295139/25000000000000000000 : ℝ) ≤ (625015899871203/625000000000000 : ℝ) ^ (4527/1024 : ℝ) := by
    have hpowers : (25002811790978295139/25000000000000000000 : ℝ)^1024 ≤ (625015899871203/625000000000000 : ℝ)^4527 := by
      have hnat : (25002811790978295139 : ℕ)^1024*625000000000000^4527 ≤ 625015899871203^4527*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002811790978295139 25000000000000000000 625015899871203 625000000000000 1024 4527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625015899871203/625000000000000 : ℝ)) (X := (25002811790978295139/25000000000000000000 : ℝ)) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50015911985172451441/50000000000000000000 : ℝ) ≤ (10000719764390327/10000000000000000 : ℝ) ^ (4527/1024 : ℝ) := by
    have hpowers : (50015911985172451441/50000000000000000000 : ℝ)^1024 ≤ (10000719764390327/10000000000000000 : ℝ)^4527 := by
      have hnat : (50015911985172451441 : ℕ)^1024*10000000000000000^4527 ≤ 10000719764390327^4527*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015911985172451441 50000000000000000000 10000719764390327 10000000000000000 1024 4527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000719764390327/10000000000000000 : ℝ)) (X := (50015911985172451441/50000000000000000000 : ℝ)) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506550097097078151/12500000000000000000 : ℝ) ≤ (5000592565420703/5000000000000000 : ℝ) ^ (4527/1024 : ℝ) := by
    have hpowers : (12506550097097078151/12500000000000000000 : ℝ)^1024 ≤ (5000592565420703/5000000000000000 : ℝ)^4527 := by
      have hnat : (12506550097097078151 : ℕ)^1024*5000000000000000^4527 ≤ 5000592565420703^4527*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506550097097078151 12500000000000000000 5000592565420703 5000000000000000 1024 4527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000592565420703/5000000000000000 : ℝ)) (X := (12506550097097078151/12500000000000000000 : ℝ)) (by norm_num) 4527 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2811790978295139/50000000000000000000 : ℝ) ≤ ((910019678473360571/910200000000000000 : ℝ)+2*(465366451079/455100000000000 : ℝ)*(10931/100000 : ℝ))^(4527/1024 : ℝ) := by
    rw [show (910019678473360571/910200000000000000 : ℝ)+2*(465366451079/455100000000000 : ℝ)*(10931/100000 : ℝ)=(625015899871203/625000000000000 : ℝ) by norm_num, show 1+2*(2811790978295139/50000000000000000000 : ℝ)=(25002811790978295139/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6550097097078151/25000000000000000000 : ℝ)+(2811790978295139/50000000000000000000 : ℝ) ≤ ((910019678473360571/910200000000000000 : ℝ)+(465366451079/455100000000000 : ℝ)*((7741/50000 : ℝ)+(10931/100000 : ℝ)))^(4527/1024 : ℝ) := by
    rw [show (910019678473360571/910200000000000000 : ℝ)+(465366451079/455100000000000 : ℝ)*((7741/50000 : ℝ)+(10931/100000 : ℝ))=(10000719764390327/10000000000000000 : ℝ) by norm_num, show 1+(6550097097078151/25000000000000000000 : ℝ)+(2811790978295139/50000000000000000000 : ℝ)=(50015911985172451441/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6550097097078151/25000000000000000000 : ℝ) ≤ ((910019678473360571/910200000000000000 : ℝ)+2*(465366451079/455100000000000 : ℝ)*(7741/50000 : ℝ))^(4527/1024 : ℝ) := by
    rw [show (910019678473360571/910200000000000000 : ℝ)+2*(465366451079/455100000000000 : ℝ)*(7741/50000 : ℝ)=(5000592565420703/5000000000000000 : ℝ) by norm_num, show 1+2*(6550097097078151/25000000000000000000 : ℝ)=(12506550097097078151/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (910019678473360571/910200000000000000 : ℝ)*(X 1 0+X 2 0)+(465366451079/455100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4527/1024 : ℝ)) (lo := (10931/100000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (910019678473360571/910200000000000000 : ℝ)) (alpha := (465366451079/455100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (910019678473360571/910200000000000000 : ℝ)*(X 0 1+X 2 1)+(465366451079/455100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4527/1024 : ℝ)) (lo := (10931/100000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (910019678473360571/910200000000000000 : ℝ)) (alpha := (465366451079/455100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (910019678473360571/910200000000000000 : ℝ)*(X 0 2+X 1 2)+(465366451079/455100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4527/1024 : ℝ)) (lo := (10931/100000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (910019678473360571/910200000000000000 : ℝ)) (alpha := (465366451079/455100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-103075759/625000000 : ℝ)*X 0 0+(5402399341/10000000000 : ℝ)*X 0 1+(1350600003/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((329426681/625000000 : ℝ)*X 1 0+(-1831755679/10000000000 : ℝ)*X 1 1+(1080479901/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5270826347/10000000000 : ℝ)*X 2 0+(540239973/1000000000 : ℝ)*X 2 1+(-915878059/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4470796321/10000000000 : ℝ)*X 0 0+(4173428071/10000000000 : ℝ)*X 0 1+(4173427321/10000000000 : ℝ)*X 0 2+(4470796321/10000000000 : ℝ)*X 1 0+(4173428071/10000000000 : ℝ)*X 1 1+(4173427321/10000000000 : ℝ)*X 1 2+(4470796321/10000000000 : ℝ)*X 2 0+(4173428071/10000000000 : ℝ)*X 2 1+(4173427321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-208047589/1000000000 : ℝ)*X 0 0+(5243753273/10000000000 : ℝ)*X 0 1+(1310937737/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2690622671/5000000000 : ℝ)*X 1 0+(-1897255831/10000000000 : ℝ)*X 1 1+(5243752821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5381247323/10000000000 : ℝ)*X 2 0+(5243750721/10000000000 : ℝ)*X 2 1+(-474313993/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4062591729/10000000000 : ℝ)*X 0 0+(2188698087/5000000000 : ℝ)*X 0 1+(547174533/1250000000 : ℝ)*X 0 2+(4062591729/10000000000 : ℝ)*X 1 0+(2188698087/5000000000 : ℝ)*X 1 1+(547174533/1250000000 : ℝ)*X 1 2+(4062591729/10000000000 : ℝ)*X 2 0+(2188698087/5000000000 : ℝ)*X 2 1+(547174533/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1989318699/10000000000 : ℝ)*X 0 0+(5132562799/10000000000 : ℝ)*X 0 1+(1084568179/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((65707421/125000000 : ℝ)*X 1 0+(-227883927/1250000000 : ℝ)*X 1 1+(1355710187/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5256593969/10000000000 : ℝ)*X 2 0+(135571007/250000000 : ℝ)*X 2 1+(-1823071667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((565280029/1250000000 : ℝ)*X 0 0+(1036778669/2500000000 : ℝ)*X 0 1+(4147115341/10000000000 : ℝ)*X 0 2+(565280029/1250000000 : ℝ)*X 1 0+(1036778669/2500000000 : ℝ)*X 1 1+(4147115341/10000000000 : ℝ)*X 1 2+(565280029/1250000000 : ℝ)*X 2 0+(1036778669/2500000000 : ℝ)*X 2 1+(4147115341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1740297917/10000000000 : ℝ)*X 0 0+(5510028231/10000000000 : ℝ)*X 0 1+(5228722329/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2695853509/5000000000 : ℝ)*X 1 0+(-475820589/2500000000 : ℝ)*X 1 1+(2614361227/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5391706931/10000000000 : ℝ)*X 2 0+(130718063/250000000 : ℝ)*X 2 1+(-951641193/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4023058843/10000000000 : ℝ)*X 0 0+(2198348233/5000000000 : ℝ)*X 0 1+(68698379/156250000 : ℝ)*X 0 2+(4023058843/10000000000 : ℝ)*X 1 0+(2198348233/5000000000 : ℝ)*X 1 1+(68698379/156250000 : ℝ)*X 1 2+(4023058843/10000000000 : ℝ)*X 2 0+(2198348233/5000000000 : ℝ)*X 2 1+(68698379/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1516_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12749/20000 : ℝ) ≤ (-604354902291305083757308347531/948125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57693419/100000000000000 : ℝ)*(upper1) + (162674403/100000000000000 : ℝ)*(upper4) + (295890573/100000000000000 : ℝ)*(upper5) + (34833278028909/1562500000000 : ℝ)*(major0) + (34833278028909/1562500000000 : ℝ)*(major1) + (34833278028909/1562500000000 : ℝ)*(major2) + (7672817/500000000000 : ℝ)*(sp1) + (8548331307/20000000000000 : ℝ)*(sp2) + (7768938971/100000000000000 : ℝ)*(sp3) + (155901102316531/5000000000000 : ℝ)*(sp4) + (194878606415383/6250000000000 : ℝ)*(sp5) + (97438015486031/3125000000000 : ℝ)*(sp6) + (680919976160081/50000000000000 : ℝ)*(sp7) + (37190878907/100000000000000 : ℝ)*(sp8) + (1361847721259133/100000000000000 : ℝ)*(f.failure) + (389757404651191/12500000000000 : ℝ)*(f.sum) + (4935721502423/1896250000000000000000000000 : ℝ)*base66 + (1018596070203097/118515625000000000000000000000 : ℝ)*base67 + (2589044117270513/474062500000000000000000000000 : ℝ)*base69 + (4244166565569599/948125000000000000000000000000 : ℝ)*base72 + (14366387468783/7585000000000000000000000000 : ℝ)*base73 + (3352111385503349/948125000000000000000000000000 : ℝ)*base76 + (773645752151847/118515625000000000000000000000 : ℝ)*base77 + (5225374141879151/948125000000000000000000000000 : ℝ)*base79 + (25548218286457/7585000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (3488721/1250000000000000000000 : ℝ)*base90 + (3488721/1250000000000000000000 : ℝ)*base92 + (3488721/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29323/50000 : ℝ) ≤ (444852521663407779251063063679/758500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11572023/10000000000000 : ℝ)*(lower0) + (10157319/12500000000000 : ℝ)*(upper1) + (107107133/50000000000000 : ℝ)*(upper2) + (6089059/25000000000000 : ℝ)*(upper3) + (115291409985417/5000000000000 : ℝ)*(major0) + (115291409985417/5000000000000 : ℝ)*(major1) + (115291409985417/5000000000000 : ℝ)*(major2) + (1591760917592233/50000000000000 : ℝ)*(sp0) + (795881963055969/25000000000000 : ℝ)*(sp1) + (3183500141754649/100000000000000 : ℝ)*(sp2) + (352143979368257/25000000000000 : ℝ)*(sp3) + (118774089/4000000000000 : ℝ)*(sp7) + (27710469227/100000000000000 : ℝ)*(sp10) + (601703941/10000000000000 : ℝ)*(sp12) + (1408578886825253/100000000000000 : ℝ)*(f.failure) + (795881963055969/25000000000000 : ℝ)*(f.sum) + (6272937391461/1517000000000000000000000000 : ℝ)*base65 + (7986584238408369/1517000000000000000000000000000 : ℝ)*base67 + (18389399426436369/1517000000000000000000000000000 : ℝ)*base69 + (12349978130273369/1517000000000000000000000000000 : ℝ)*base71 + (1363891062623/758500000000000000000000000 : ℝ)*base73 + (15096019887170369/1517000000000000000000000000000 : ℝ)*base75 + (17609325700683369/1517000000000000000000000000000 : ℝ)*base77 + (17864548376270369/1517000000000000000000000000000 : ℝ)*base79 + (461083376027/60680000000000000000000000 : ℝ)*base81 + (5547161/1250000000000000000000 : ℝ)*base90 + (5547161/1250000000000000000000 : ℝ)*base92 + (5547161/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40181/50000 : ℝ) ≤ (6095659571654610550992229729819/7585000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (125161293/100000000000000 : ℝ)*(upper0) + (3238151/100000000000000 : ℝ)*(lower3) + (52597777/100000000000000 : ℝ)*(lower5) + (1249628350374089/50000000000000 : ℝ)*(major0) + (1249628350374089/50000000000000 : ℝ)*(major1) + (1249628350374089/50000000000000 : ℝ)*(major2) + (34974551993/50000000000000 : ℝ)*(sp1) + (21637144081/100000000000000 : ℝ)*(sp3) + (330767319/25000000000000 : ℝ)*(sp4) + (1722487618946073/50000000000000 : ℝ)*(sp8) + (344491519902951/10000000000000 : ℝ)*(sp9) + (430623143516687/12500000000000 : ℝ)*(sp10) + (305343679146497/20000000000000 : ℝ)*(sp11) + (343486883/4000000000000 : ℝ)*(sp12) + (763370016438283/50000000000000 : ℝ)*(f.failure) + (430623143516687/12500000000000 : ℝ)*(f.sum) + (16358145222901/11377500000000000000000000000 : ℝ)*base65 + (303986839700557727/15170000000000000000000000000000 : ℝ)*base68 + (142513149130527727/15170000000000000000000000000000 : ℝ)*base70 + (42091636731812273/15170000000000000000000000000000 : ℝ)*base71 + (403670541512473/22755000000000000000000000000 : ℝ)*base74 + (10562265466417727/15170000000000000000000000000000 : ℝ)*base76 + (15219781379252273/15170000000000000000000000000000 : ℝ)*base77 + (16614741929567727/15170000000000000000000000000000 : ℝ)*base80 + (9980434609099/2844375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1342729/625000000000000000000 : ℝ)*base89 + (1342729/625000000000000000000 : ℝ)*base91 + (1342729/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-21507/25000 : ℝ) ≤ (-13049993939486941480661451718851/15170000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (716411/20000000000000 : ℝ)*(lower0) + (3568837/6250000000000 : ℝ)*(upper3) + (312773/50000000000000 : ℝ)*(lower4) + (2538420720723319/100000000000000 : ℝ)*(major0) + (2538420720723319/100000000000000 : ℝ)*(major1) + (2538420720723319/100000000000000 : ℝ)*(major2) + (907197231/50000000000000 : ℝ)*(sp0) + (29392312559/100000000000000 : ℝ)*(sp5) + (427950159/100000000000000 : ℝ)*(sp6) + (17118309187/100000000000000 : ℝ)*(sp7) + (888712543319561/25000000000000 : ℝ)*(sp12) + (888705648840037/25000000000000 : ℝ)*(sp13) + (888712889930637/25000000000000 : ℝ)*(sp14) + (6202589354511/400000000000 : ℝ)*(sp15) + (775332228468469/50000000000000 : ℝ)*(f.failure) + (1777425993836353/50000000000000 : ℝ)*(f.sum) + (38756280893983/11377500000000000000000000000 : ℝ)*base65 + (116791362724792383/30340000000000000000000000000000 : ℝ)*base67 + (4646007741832383/30340000000000000000000000000000 : ℝ)*base69 + (147959678485347617/30340000000000000000000000000000 : ℝ)*base72 + (117444111662173/11377500000000000000000000000 : ℝ)*base73 + (62711775013907617/30340000000000000000000000000000 : ℝ)*base76 + (58419836714367617/30340000000000000000000000000000 : ℝ)*base78 + (16909119560827617/30340000000000000000000000000000 : ℝ)*base80 + (46233561656741/22755000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2982247/625000000000000000000 : ℝ)*base89 + (2982247/625000000000000000000 : ℝ)*base91 + (2982247/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1516_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20462363/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10931/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12749/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29323/50000 : ℝ) else (40181/50000 : ℝ) ≤ X j i ∧ X j i ≤ (21507/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1516_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1516_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20462363/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10931/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12749/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29323/50000 : ℝ) else (40181/50000 : ℝ) ≤ X j i ∧ X j i ≤ (21507/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1516_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1516_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4527/1024 : ℝ) ≤ p) (hpb : p ≤ (4529/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20462363/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10931/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12749/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29323/50000 : ℝ) else (40181/50000 : ℝ) ≤ X j i ∧ X j i ≤ (21507/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1516_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
