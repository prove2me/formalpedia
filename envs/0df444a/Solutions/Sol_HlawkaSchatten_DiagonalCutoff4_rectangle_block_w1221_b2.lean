-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1221_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:11:23.802192+00:00
-- url     : https://prove2.me/submissions/2a11969e-67a5-4177-9066-c7be7ee27d03

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
theorem support_rectangle_w1221_s6_0 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1064824223/5000000000 : ℝ)*x 0 + (1347952799/2500000000 : ℝ)*x 1 + (2633359229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064824223/5000000000 : ℝ)^4207 ≤ (1294847063581/10000000000000 : ℝ)^3183 := by
    have hnat : (1064824223 : ℕ)^4207*10000000000000^3183 ≤ 1294847063581^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064824223 5000000000 1294847063581 10000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347952799/2500000000 : ℝ)^4207 ≤ (44200917652901/100000000000000 : ℝ)^3183 := by
    have hnat : (1347952799 : ℕ)^4207*100000000000000^3183 ≤ 44200917652901^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347952799 2500000000 44200917652901 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633359229/5000000000 : ℝ)^4207 ≤ (42850611690123/100000000000000 : ℝ)^3183 := by
    have hnat : (2633359229 : ℕ)^4207*100000000000000^3183 ≤ 42850611690123^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633359229 5000000000 42850611690123 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1064824223/5000000000 : ℝ), (1347952799/2500000000 : ℝ), (2633359229/5000000000 : ℝ)] ![(1294847063581/10000000000000 : ℝ), (44200917652901/100000000000000 : ℝ), (42850611690123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1064824223/5000000000 : ℝ)|^4207 ≤ (1294847063581/10000000000000 : ℝ)^3183
        have hw : |(-1064824223/5000000000 : ℝ)|=(1064824223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347952799/2500000000 : ℝ)|^4207 ≤ (44200917652901/100000000000000 : ℝ)^3183
        have hw : |(1347952799/2500000000 : ℝ)|=(1347952799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633359229/5000000000 : ℝ)|^4207 ≤ (42850611690123/100000000000000 : ℝ)^3183
        have hw : |(2633359229/5000000000 : ℝ)|=(2633359229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s6_1 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068894701/2000000000 : ℝ)*x 0 + (-1096540879/5000000000 : ℝ)*x 1 + (5266718317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068894701/2000000000 : ℝ)^4207 ≤ (43688735345671/100000000000000 : ℝ)^3183 := by
    have hnat : (1068894701 : ℕ)^4207*100000000000000^3183 ≤ 43688735345671^3183*2000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068894701 2000000000 43688735345671 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1096540879/5000000000 : ℝ)^4207 ≤ (13460654462101/100000000000000 : ℝ)^3183 := by
    have hnat : (1096540879 : ℕ)^4207*100000000000000^3183 ≤ 13460654462101^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096540879 5000000000 13460654462101 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266718317/10000000000 : ℝ)^4207 ≤ (42850610173869/100000000000000 : ℝ)^3183 := by
    have hnat : (5266718317 : ℕ)^4207*100000000000000^3183 ≤ 42850610173869^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266718317 10000000000 42850610173869 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068894701/2000000000 : ℝ), (-1096540879/5000000000 : ℝ), (5266718317/10000000000 : ℝ)] ![(43688735345671/100000000000000 : ℝ), (13460654462101/100000000000000 : ℝ), (42850610173869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068894701/2000000000 : ℝ)|^4207 ≤ (43688735345671/100000000000000 : ℝ)^3183
        have hw : |(1068894701/2000000000 : ℝ)|=(1068894701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1096540879/5000000000 : ℝ)|^4207 ≤ (13460654462101/100000000000000 : ℝ)^3183
        have hw : |(-1096540879/5000000000 : ℝ)|=(1096540879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266718317/10000000000 : ℝ)|^4207 ≤ (42850610173869/100000000000000 : ℝ)^3183
        have hw : |(5266718317/10000000000 : ℝ)|=(5266718317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s6_2 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344473431/10000000000 : ℝ)*x 0 + (5266718373/10000000000 : ℝ)*x 1 + (-2193081783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344473431/10000000000 : ℝ)^4207 ≤ (21844367273073/50000000000000 : ℝ)^3183 := by
    have hnat : (5344473431 : ℕ)^4207*50000000000000^3183 ≤ 21844367273073^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344473431 10000000000 21844367273073 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266718373/10000000000 : ℝ)^4207 ≤ (42850610776069/100000000000000 : ℝ)^3183 := by
    have hnat : (5266718373 : ℕ)^4207*100000000000000^3183 ≤ 42850610776069^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266718373 10000000000 42850610776069 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2193081783/10000000000 : ℝ)^4207 ≤ (1346065466491/10000000000000 : ℝ)^3183 := by
    have hnat : (2193081783 : ℕ)^4207*10000000000000^3183 ≤ 1346065466491^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193081783 10000000000 1346065466491 10000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344473431/10000000000 : ℝ), (5266718373/10000000000 : ℝ), (-2193081783/10000000000 : ℝ)] ![(21844367273073/50000000000000 : ℝ), (42850610776069/100000000000000 : ℝ), (1346065466491/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344473431/10000000000 : ℝ)|^4207 ≤ (21844367273073/50000000000000 : ℝ)^3183
        have hw : |(5344473431/10000000000 : ℝ)|=(5344473431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266718373/10000000000 : ℝ)|^4207 ≤ (42850610776069/100000000000000 : ℝ)^3183
        have hw : |(5266718373/10000000000 : ℝ)|=(5266718373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2193081783/10000000000 : ℝ)|^4207 ≤ (1346065466491/10000000000000 : ℝ)^3183
        have hw : |(-2193081783/10000000000 : ℝ)|=(2193081783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s6_3 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (272103139/625000000 : ℝ)*x 0 + (4229076529/10000000000 : ℝ)*x 1 + (4481807657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272103139/625000000 : ℝ)^4207 ≤ (33317272241531/100000000000000 : ℝ)^3183 := by
    have hnat : (272103139 : ℕ)^4207*100000000000000^3183 ≤ 33317272241531^3183*625000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272103139 625000000 33317272241531 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4229076529/10000000000 : ℝ)^4207 ≤ (16031543824569/50000000000000 : ℝ)^3183 := by
    have hnat : (4229076529 : ℕ)^4207*50000000000000^3183 ≤ 16031543824569^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229076529 10000000000 16031543824569 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4481807657/10000000000 : ℝ)^4207 ≤ (34619640094949/100000000000000 : ℝ)^3183 := by
    have hnat : (4481807657 : ℕ)^4207*100000000000000^3183 ≤ 34619640094949^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481807657 10000000000 34619640094949 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272103139/625000000 : ℝ), (4229076529/10000000000 : ℝ), (4481807657/10000000000 : ℝ)] ![(33317272241531/100000000000000 : ℝ), (16031543824569/50000000000000 : ℝ), (34619640094949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272103139/625000000 : ℝ)|^4207 ≤ (33317272241531/100000000000000 : ℝ)^3183
        have hw : |(272103139/625000000 : ℝ)|=(272103139/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4229076529/10000000000 : ℝ)|^4207 ≤ (16031543824569/50000000000000 : ℝ)^3183
        have hw : |(4229076529/10000000000 : ℝ)|=(4229076529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4481807657/10000000000 : ℝ)|^4207 ≤ (34619640094949/100000000000000 : ℝ)^3183
        have hw : |(4481807657/10000000000 : ℝ)|=(4481807657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s6_4 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-532413317/2500000000 : ℝ)*x 0 + (1316758667/2500000000 : ℝ)*x 1 + (5391493783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532413317/2500000000 : ℝ)^4207 ≤ (12948509385997/100000000000000 : ℝ)^3183 := by
    have hnat : (532413317 : ℕ)^4207*100000000000000^3183 ≤ 12948509385997^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532413317 2500000000 12948509385997 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316758667/2500000000 : ℝ)^4207 ≤ (10713503027587/25000000000000 : ℝ)^3183 := by
    have hnat : (1316758667 : ℕ)^4207*25000000000000^3183 ≤ 10713503027587^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316758667 2500000000 10713503027587 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391493783/10000000000 : ℝ)^4207 ≤ (11049369621841/25000000000000 : ℝ)^3183 := by
    have hnat : (5391493783 : ℕ)^4207*25000000000000^3183 ≤ 11049369621841^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391493783 10000000000 11049369621841 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-532413317/2500000000 : ℝ), (1316758667/2500000000 : ℝ), (5391493783/10000000000 : ℝ)] ![(12948509385997/100000000000000 : ℝ), (10713503027587/25000000000000 : ℝ), (11049369621841/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-532413317/2500000000 : ℝ)|^4207 ≤ (12948509385997/100000000000000 : ℝ)^3183
        have hw : |(-532413317/2500000000 : ℝ)|=(532413317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316758667/2500000000 : ℝ)|^4207 ≤ (10713503027587/25000000000000 : ℝ)^3183
        have hw : |(1316758667/2500000000 : ℝ)|=(1316758667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391493783/10000000000 : ℝ)|^4207 ≤ (11049369621841/25000000000000 : ℝ)^3183
        have hw : |(5391493783/10000000000 : ℝ)|=(5391493783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s6_5 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312601119/10000000000 : ℝ)*x 0 + (-103415317/500000000 : ℝ)*x 1 + (539149379/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312601119/10000000000 : ℝ)^4207 ≤ (43344704309487/100000000000000 : ℝ)^3183 := by
    have hnat : (5312601119 : ℕ)^4207*100000000000000^3183 ≤ 43344704309487^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312601119 10000000000 43344704309487 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103415317/500000000 : ℝ)^4207 ≤ (12457817110313/100000000000000 : ℝ)^3183 := by
    have hnat : (103415317 : ℕ)^4207*100000000000000^3183 ≤ 12457817110313^3183*500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103415317 500000000 12457817110313 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539149379/1000000000 : ℝ)^4207 ≤ (5524684820401/12500000000000 : ℝ)^3183 := by
    have hnat : (539149379 : ℕ)^4207*12500000000000^3183 ≤ 5524684820401^3183*1000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539149379 1000000000 5524684820401 12500000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312601119/10000000000 : ℝ), (-103415317/500000000 : ℝ), (539149379/1000000000 : ℝ)] ![(43344704309487/100000000000000 : ℝ), (12457817110313/100000000000000 : ℝ), (5524684820401/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312601119/10000000000 : ℝ)|^4207 ≤ (43344704309487/100000000000000 : ℝ)^3183
        have hw : |(5312601119/10000000000 : ℝ)|=(5312601119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-103415317/500000000 : ℝ)|^4207 ≤ (12457817110313/100000000000000 : ℝ)^3183
        have hw : |(-103415317/500000000 : ℝ)|=(103415317/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539149379/1000000000 : ℝ)|^4207 ≤ (5524684820401/12500000000000 : ℝ)^3183
        have hw : |(539149379/1000000000 : ℝ)|=(539149379/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s6_6 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312601131/10000000000 : ℝ)*x 0 + (5391493779/10000000000 : ℝ)*x 1 + (-2068306339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312601131/10000000000 : ℝ)^4207 ≤ (43344704438891/100000000000000 : ℝ)^3183 := by
    have hnat : (5312601131 : ℕ)^4207*100000000000000^3183 ≤ 43344704438891^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312601131 10000000000 43344704438891 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391493779/10000000000 : ℝ)^4207 ≤ (1767899137761/4000000000000 : ℝ)^3183 := by
    have hnat : (5391493779 : ℕ)^4207*4000000000000^3183 ≤ 1767899137761^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391493779 10000000000 1767899137761 4000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2068306339/10000000000 : ℝ)^4207 ≤ (778613568897/6250000000000 : ℝ)^3183 := by
    have hnat : (2068306339 : ℕ)^4207*6250000000000^3183 ≤ 778613568897^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068306339 10000000000 778613568897 6250000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312601131/10000000000 : ℝ), (5391493779/10000000000 : ℝ), (-2068306339/10000000000 : ℝ)] ![(43344704438891/100000000000000 : ℝ), (1767899137761/4000000000000 : ℝ), (778613568897/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312601131/10000000000 : ℝ)|^4207 ≤ (43344704438891/100000000000000 : ℝ)^3183
        have hw : |(5312601131/10000000000 : ℝ)|=(5312601131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391493779/10000000000 : ℝ)|^4207 ≤ (1767899137761/4000000000000 : ℝ)^3183
        have hw : |(5391493779/10000000000 : ℝ)|=(5391493779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2068306339/10000000000 : ℝ)|^4207 ≤ (778613568897/6250000000000 : ℝ)^3183
        have hw : |(-2068306339/10000000000 : ℝ)|=(2068306339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s6_7 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4353659951/10000000000 : ℝ)*x 0 + (2240584283/5000000000 : ℝ)*x 1 + (4229717817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353659951/10000000000 : ℝ)^4207 ≤ (16658685313487/50000000000000 : ℝ)^3183 := by
    have hnat : (4353659951 : ℕ)^4207*50000000000000^3183 ≤ 16658685313487^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353659951 10000000000 16658685313487 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2240584283/5000000000 : ℝ)^4207 ≤ (17306557717009/50000000000000 : ℝ)^3183 := by
    have hnat : (2240584283 : ℕ)^4207*50000000000000^3183 ≤ 17306557717009^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240584283 5000000000 17306557717009 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4229717817/10000000000 : ℝ)^4207 ≤ (32069513925189/100000000000000 : ℝ)^3183 := by
    have hnat : (4229717817 : ℕ)^4207*100000000000000^3183 ≤ 32069513925189^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229717817 10000000000 32069513925189 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353659951/10000000000 : ℝ), (2240584283/5000000000 : ℝ), (4229717817/10000000000 : ℝ)] ![(16658685313487/50000000000000 : ℝ), (17306557717009/50000000000000 : ℝ), (32069513925189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353659951/10000000000 : ℝ)|^4207 ≤ (16658685313487/50000000000000 : ℝ)^3183
        have hw : |(4353659951/10000000000 : ℝ)|=(4353659951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2240584283/5000000000 : ℝ)|^4207 ≤ (17306557717009/50000000000000 : ℝ)^3183
        have hw : |(2240584283/5000000000 : ℝ)|=(2240584283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4229717817/10000000000 : ℝ)|^4207 ≤ (32069513925189/100000000000000 : ℝ)^3183
        have hw : |(4229717817/10000000000 : ℝ)|=(4229717817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1221_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5713/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1431/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7049/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7061/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5713/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7061/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5713/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7061/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5713/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7061/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5713/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7061/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5713/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7061/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5713/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5713/50000 : ℝ) ^ (8413/2048 : ℝ) ≤ (1348696085341443/10000000000000000000 : ℝ) := by
    have hpowers : (5713/50000 : ℝ)^8413 ≤ (1348696085341443/10000000000000000000 : ℝ)^2048 := by
      have hnat : (5713 : ℕ)^8413*10000000000000000000^2048 ≤ 1348696085341443^2048*50000^8413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5713 50000 1348696085341443 10000000000000000000 8413 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5713/50000 : ℝ)) (X := (1348696085341443/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7061/50000 : ℝ) ^ (8413/2048 : ℝ) ≤ (6439912864858767/20000000000000000000 : ℝ) := by
    have hpowers : (7061/50000 : ℝ)^8413 ≤ (6439912864858767/20000000000000000000 : ℝ)^2048 := by
      have hnat : (7061 : ℕ)^8413*20000000000000000000^2048 ≤ 6439912864858767^2048*50000^8413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7061 50000 6439912864858767 20000000000000000000 8413 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7061/50000 : ℝ)) (X := (6439912864858767/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001348696085341443/5000000000000000000 : ℝ) ≤ (10000656566690911/10000000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (5001348696085341443/5000000000000000000 : ℝ)^2048 ≤ (10000656566690911/10000000000000000 : ℝ)^8413 := by
      have hnat : (5001348696085341443 : ℕ)^2048*10000000000000000^8413 ≤ 10000656566690911^8413*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001348696085341443 5000000000000000000 10000656566690911 10000000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000656566690911/10000000000000000 : ℝ)) (X := (5001348696085341443/5000000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009137305035541653/20000000000000000000 : ℝ) ≤ (2000222393527583/2000000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (20009137305035541653/20000000000000000000 : ℝ)^2048 ≤ (2000222393527583/2000000000000000 : ℝ)^8413 := by
      have hnat : (20009137305035541653 : ℕ)^2048*2000000000000000^8413 ≤ 2000222393527583^8413*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009137305035541653 20000000000000000000 2000222393527583 2000000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000222393527583/2000000000000000 : ℝ)) (X := (20009137305035541653/20000000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006439912864858767/10000000000000000000 : ℝ) ≤ (10001567368584919/10000000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (10006439912864858767/10000000000000000000 : ℝ)^2048 ≤ (10001567368584919/10000000000000000 : ℝ)^8413 := by
      have hnat : (10006439912864858767 : ℕ)^2048*10000000000000000^8413 ≤ 10001567368584919^8413*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006439912864858767 10000000000000000000 10001567368584919 10000000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001567368584919/10000000000000000 : ℝ)) (X := (10006439912864858767/10000000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1348696085341443/10000000000000000000 : ℝ) ≤ ((3368920410169720081/3370000000000000000 : ℝ)+2*(113850236751/67400000000000 : ℝ)*(5713/50000 : ℝ))^(8413/2048 : ℝ) := by
    rw [show (3368920410169720081/3370000000000000000 : ℝ)+2*(113850236751/67400000000000 : ℝ)*(5713/50000 : ℝ)=(10000656566690911/10000000000000000 : ℝ) by norm_num, show 1+2*(1348696085341443/10000000000000000000 : ℝ)=(5001348696085341443/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6439912864858767/20000000000000000000 : ℝ)+(1348696085341443/10000000000000000000 : ℝ) ≤ ((3368920410169720081/3370000000000000000 : ℝ)+(113850236751/67400000000000 : ℝ)*((7061/50000 : ℝ)+(5713/50000 : ℝ)))^(8413/2048 : ℝ) := by
    rw [show (3368920410169720081/3370000000000000000 : ℝ)+(113850236751/67400000000000 : ℝ)*((7061/50000 : ℝ)+(5713/50000 : ℝ))=(2000222393527583/2000000000000000 : ℝ) by norm_num, show 1+(6439912864858767/20000000000000000000 : ℝ)+(1348696085341443/10000000000000000000 : ℝ)=(20009137305035541653/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6439912864858767/20000000000000000000 : ℝ) ≤ ((3368920410169720081/3370000000000000000 : ℝ)+2*(113850236751/67400000000000 : ℝ)*(7061/50000 : ℝ))^(8413/2048 : ℝ) := by
    rw [show (3368920410169720081/3370000000000000000 : ℝ)+2*(113850236751/67400000000000 : ℝ)*(7061/50000 : ℝ)=(10001567368584919/10000000000000000 : ℝ) by norm_num, show 1+2*(6439912864858767/20000000000000000000 : ℝ)=(10006439912864858767/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3368920410169720081/3370000000000000000 : ℝ)*(X 1 0+X 2 0)+(113850236751/67400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (5713/50000 : ℝ)) (hi := (7061/50000 : ℝ)) (c := (3368920410169720081/3370000000000000000 : ℝ)) (alpha := (113850236751/67400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3368920410169720081/3370000000000000000 : ℝ)*(X 0 1+X 2 1)+(113850236751/67400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (5713/50000 : ℝ)) (hi := (7061/50000 : ℝ)) (c := (3368920410169720081/3370000000000000000 : ℝ)) (alpha := (113850236751/67400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3368920410169720081/3370000000000000000 : ℝ)*(X 0 2+X 1 2)+(113850236751/67400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (5713/50000 : ℝ)) (hi := (7061/50000 : ℝ)) (c := (3368920410169720081/3370000000000000000 : ℝ)) (alpha := (113850236751/67400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1064824223/5000000000 : ℝ)*X 0 0+(1347952799/2500000000 : ℝ)*X 0 1+(2633359229/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068894701/2000000000 : ℝ)*X 1 0+(-1096540879/5000000000 : ℝ)*X 1 1+(5266718317/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344473431/10000000000 : ℝ)*X 2 0+(5266718373/10000000000 : ℝ)*X 2 1+(-2193081783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((272103139/625000000 : ℝ)*X 0 0+(4229076529/10000000000 : ℝ)*X 0 1+(4481807657/10000000000 : ℝ)*X 0 2+(272103139/625000000 : ℝ)*X 1 0+(4229076529/10000000000 : ℝ)*X 1 1+(4481807657/10000000000 : ℝ)*X 1 2+(272103139/625000000 : ℝ)*X 2 0+(4229076529/10000000000 : ℝ)*X 2 1+(4481807657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-532413317/2500000000 : ℝ)*X 0 0+(1316758667/2500000000 : ℝ)*X 0 1+(5391493783/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312601119/10000000000 : ℝ)*X 1 0+(-103415317/500000000 : ℝ)*X 1 1+(539149379/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312601131/10000000000 : ℝ)*X 2 0+(5391493779/10000000000 : ℝ)*X 2 1+(-2068306339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4353659951/10000000000 : ℝ)*X 0 0+(2240584283/5000000000 : ℝ)*X 0 1+(4229717817/10000000000 : ℝ)*X 0 2+(4353659951/10000000000 : ℝ)*X 1 0+(2240584283/5000000000 : ℝ)*X 1 1+(4229717817/10000000000 : ℝ)*X 1 2+(4353659951/10000000000 : ℝ)*X 2 0+(2240584283/5000000000 : ℝ)*X 2 1+(4229717817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16257008947151031968233587/1685000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1714842297/100000000000000 : ℝ)*(base19) + (367228887/25000000000000 : ℝ)*(base23) + (3613909/5000000000000 : ℝ)*(lower2) + (109296259/50000000000000 : ℝ)*(upper3) + (29358771/50000000000000 : ℝ)*(upper5) + (119509730200191/2000000000000 : ℝ)*(major0) + (119509730200191/2000000000000 : ℝ)*(major1) + (119509730200191/2000000000000 : ℝ)*(major2) + (7994114525966751/100000000000000 : ℝ)*(sp0) + (3997075655084867/50000000000000 : ℝ)*(sp1) + (7994151556096483/100000000000000 : ℝ)*(sp2) + (3956795160602333/100000000000000 : ℝ)*(sp3) + (240619033/625000000000 : ℝ)*(sp4) + (6128200543/25000000000000 : ℝ)*(sp7) + (1978409836702253/50000000000000 : ℝ)*(f.failure) + (7994153025012031/100000000000000 : ℝ)*(f.sum) + (634655133219/337000000000000000000000000 : ℝ)*base65 + (150030904793485471/6740000000000000000000000000000 : ℝ)*base67 + (108959584104565471/6740000000000000000000000000000 : ℝ)*base69 + (30378035506374529/6740000000000000000000000000000 : ℝ)*base72 + (706207654009/84250000000000000000000000 : ℝ)*base73 + (175717036449365471/6740000000000000000000000000000 : ℝ)*base75 + (110823983803405471/6740000000000000000000000000000 : ℝ)*base77 + (70839470772465471/6740000000000000000000000000000 : ℝ)*base79 + (600044917113/337000000000000000000000000 : ℝ)*base81 + (247191/78125000000000000000 : ℝ)*base89 + (247191/78125000000000000000 : ℝ)*base91 + (247191/78125000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (662167808001246687609768213/168500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (701913629/100000000000000 : ℝ)*(base19) + (77813403/10000000000000 : ℝ)*(base23) + (38773777/50000000000000 : ℝ)*(upper3) + (25686333/100000000000000 : ℝ)*(lower4) + (38471627/50000000000000 : ℝ)*(upper5) + (6005844245762403/100000000000000 : ℝ)*(major0) + (6005844245762403/100000000000000 : ℝ)*(major1) + (6005844245762403/100000000000000 : ℝ)*(major2) + (20160542083/100000000000000 : ℝ)*(sp1) + (2178106497/10000000000000 : ℝ)*(sp2) + (1004345817979387/12500000000000 : ℝ)*(sp4) + (1004343210172423/12500000000000 : ℝ)*(sp5) + (125542874759939/1562500000000 : ℝ)*(sp6) + (1988460908348527/50000000000000 : ℝ)*(sp7) + (1988460908348527/50000000000000 : ℝ)*(f.failure) + (1004345817979387/12500000000000 : ℝ)*(f.sum) + (6610423736967/3370000000000000000000000000 : ℝ)*base66 + (5047855065372564643/337000000000000000000000000000000 : ℝ)*base67 + (2902679343194564643/337000000000000000000000000000000 : ℝ)*base69 + (1625784092371564643/337000000000000000000000000000000 : ℝ)*base71 + (3875660190647/3370000000000000000000000000 : ℝ)*base74 + (13149416586683564643/337000000000000000000000000000000 : ℝ)*base75 + (5214869465576564643/337000000000000000000000000000000 : ℝ)*base77 + (1050552324330564643/337000000000000000000000000000000 : ℝ)*base79 + (12453216633027/3370000000000000000000000000 : ℝ)*base82 + (653781/78125000000000000000 : ℝ)*base90 + (653781/78125000000000000000 : ℝ)*base92 + (653781/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1221_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5713/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1431/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1221_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1221_s7_0 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1064835167/5000000000 : ℝ)*x 0 + (5391589867/10000000000 : ℝ)*x 1 + (2633462553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064835167/5000000000 : ℝ)^4207 ≤ (12948646530703/100000000000000 : ℝ)^3183 := by
    have hnat : (1064835167 : ℕ)^4207*100000000000000^3183 ≤ 12948646530703^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064835167 5000000000 12948646530703 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391589867/10000000000 : ℝ)^4207 ≤ (44198519549323/100000000000000 : ℝ)^3183 := by
    have hnat : (5391589867 : ℕ)^4207*100000000000000^3183 ≤ 44198519549323^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391589867 10000000000 44198519549323 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633462553/5000000000 : ℝ)^4207 ≤ (21426416954273/50000000000000 : ℝ)^3183 := by
    have hnat : (2633462553 : ℕ)^4207*50000000000000^3183 ≤ 21426416954273^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633462553 5000000000 21426416954273 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1064835167/5000000000 : ℝ), (5391589867/10000000000 : ℝ), (2633462553/5000000000 : ℝ)] ![(12948646530703/100000000000000 : ℝ), (44198519549323/100000000000000 : ℝ), (21426416954273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1064835167/5000000000 : ℝ)|^4207 ≤ (12948646530703/100000000000000 : ℝ)^3183
        have hw : |(-1064835167/5000000000 : ℝ)|=(1064835167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391589867/10000000000 : ℝ)|^4207 ≤ (44198519549323/100000000000000 : ℝ)^3183
        have hw : |(5391589867/10000000000 : ℝ)|=(5391589867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633462553/5000000000 : ℝ)|^4207 ≤ (21426416954273/50000000000000 : ℝ)^3183
        have hw : |(2633462553/5000000000 : ℝ)|=(2633462553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s7_1 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534441649/1000000000 : ℝ)*x 0 + (-548220857/2500000000 : ℝ)*x 1 + (5266925217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534441649/1000000000 : ℝ)^4207 ≤ (10922029833549/25000000000000 : ℝ)^3183 := by
    have hnat : (534441649 : ℕ)^4207*25000000000000^3183 ≤ 10922029833549^3183*1000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534441649 1000000000 10922029833549 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548220857/2500000000 : ℝ)^4207 ≤ (841190347569/6250000000000 : ℝ)^3183 := by
    have hnat : (548220857 : ℕ)^4207*6250000000000^3183 ≤ 841190347569^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548220857 2500000000 841190347569 6250000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266925217/10000000000 : ℝ)^4207 ≤ (42852835102207/100000000000000 : ℝ)^3183 := by
    have hnat : (5266925217 : ℕ)^4207*100000000000000^3183 ≤ 42852835102207^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266925217 10000000000 42852835102207 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534441649/1000000000 : ℝ), (-548220857/2500000000 : ℝ), (5266925217/10000000000 : ℝ)] ![(10922029833549/25000000000000 : ℝ), (841190347569/6250000000000 : ℝ), (42852835102207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534441649/1000000000 : ℝ)|^4207 ≤ (10922029833549/25000000000000 : ℝ)^3183
        have hw : |(534441649/1000000000 : ℝ)|=(534441649/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-548220857/2500000000 : ℝ)|^4207 ≤ (841190347569/6250000000000 : ℝ)^3183
        have hw : |(-548220857/2500000000 : ℝ)|=(548220857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266925217/10000000000 : ℝ)|^4207 ≤ (42852835102207/100000000000000 : ℝ)^3183
        have hw : |(5266925217/10000000000 : ℝ)|=(5266925217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s7_2 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213776653/400000000 : ℝ)*x 0 + (2633462737/5000000000 : ℝ)*x 1 + (-438576661/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213776653/400000000 : ℝ)^4207 ≤ (43688117551477/100000000000000 : ℝ)^3183 := by
    have hnat : (213776653 : ℕ)^4207*100000000000000^3183 ≤ 43688117551477^3183*400000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213776653 400000000 43688117551477 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633462737/5000000000 : ℝ)^4207 ≤ (42852837865911/100000000000000 : ℝ)^3183 := by
    have hnat : (2633462737 : ℕ)^4207*100000000000000^3183 ≤ 42852837865911^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633462737 5000000000 42852837865911 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (438576661/2000000000 : ℝ)^4207 ≤ (841190285207/6250000000000 : ℝ)^3183 := by
    have hnat : (438576661 : ℕ)^4207*6250000000000^3183 ≤ 841190285207^3183*2000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438576661 2000000000 841190285207 6250000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213776653/400000000 : ℝ), (2633462737/5000000000 : ℝ), (-438576661/2000000000 : ℝ)] ![(43688117551477/100000000000000 : ℝ), (42852837865911/100000000000000 : ℝ), (841190285207/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213776653/400000000 : ℝ)|^4207 ≤ (43688117551477/100000000000000 : ℝ)^3183
        have hw : |(213776653/400000000 : ℝ)|=(213776653/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633462737/5000000000 : ℝ)|^4207 ≤ (42852837865911/100000000000000 : ℝ)^3183
        have hw : |(2633462737/5000000000 : ℝ)|=(2633462737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-438576661/2000000000 : ℝ)|^4207 ≤ (841190285207/6250000000000 : ℝ)^3183
        have hw : |(-438576661/2000000000 : ℝ)|=(438576661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s7_3 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4353661017/10000000000 : ℝ)*x 0 + (4229508053/10000000000 : ℝ)*x 1 + (4481373409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353661017/10000000000 : ℝ)^4207 ≤ (16658690704611/50000000000000 : ℝ)^3183 := by
    have hnat : (4353661017 : ℕ)^4207*50000000000000^3183 ≤ 16658690704611^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353661017 10000000000 16658690704611 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4229508053/10000000000 : ℝ)^4207 ≤ (3206741186887/10000000000000 : ℝ)^3183 := by
    have hnat : (4229508053 : ℕ)^4207*10000000000000^3183 ≤ 3206741186887^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229508053 10000000000 3206741186887 10000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4481373409/10000000000 : ℝ)^4207 ≤ (6923041340319/20000000000000 : ℝ)^3183 := by
    have hnat : (4481373409 : ℕ)^4207*20000000000000^3183 ≤ 6923041340319^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481373409 10000000000 6923041340319 20000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353661017/10000000000 : ℝ), (4229508053/10000000000 : ℝ), (4481373409/10000000000 : ℝ)] ![(16658690704611/50000000000000 : ℝ), (3206741186887/10000000000000 : ℝ), (6923041340319/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353661017/10000000000 : ℝ)|^4207 ≤ (16658690704611/50000000000000 : ℝ)^3183
        have hw : |(4353661017/10000000000 : ℝ)|=(4353661017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4229508053/10000000000 : ℝ)|^4207 ≤ (3206741186887/10000000000000 : ℝ)^3183
        have hw : |(4229508053/10000000000 : ℝ)|=(4229508053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4481373409/10000000000 : ℝ)|^4207 ≤ (6923041340319/20000000000000 : ℝ)^3183
        have hw : |(4481373409/10000000000 : ℝ)|=(4481373409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s7_4 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2129674839/10000000000 : ℝ)*x 0 + (105344807/200000000 : ℝ)*x 1 + (5391273639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129674839/10000000000 : ℝ)^4207 ≤ (12948682733557/100000000000000 : ℝ)^3183 := by
    have hnat : (2129674839 : ℕ)^4207*100000000000000^3183 ≤ 12948682733557^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129674839 10000000000 12948682733557 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105344807/200000000 : ℝ)^4207 ≤ (2678513998963/6250000000000 : ℝ)^3183 := by
    have hnat : (105344807 : ℕ)^4207*6250000000000^3183 ≤ 2678513998963^3183*200000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105344807 200000000 2678513998963 6250000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391273639/10000000000 : ℝ)^4207 ≤ (44195093268373/100000000000000 : ℝ)^3183 := by
    have hnat : (5391273639 : ℕ)^4207*100000000000000^3183 ≤ 44195093268373^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391273639 10000000000 44195093268373 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2129674839/10000000000 : ℝ), (105344807/200000000 : ℝ), (5391273639/10000000000 : ℝ)] ![(12948682733557/100000000000000 : ℝ), (2678513998963/6250000000000 : ℝ), (44195093268373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2129674839/10000000000 : ℝ)|^4207 ≤ (12948682733557/100000000000000 : ℝ)^3183
        have hw : |(-2129674839/10000000000 : ℝ)|=(2129674839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105344807/200000000 : ℝ)|^4207 ≤ (2678513998963/6250000000000 : ℝ)^3183
        have hw : |(105344807/200000000 : ℝ)|=(105344807/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391273639/10000000000 : ℝ)|^4207 ≤ (44195093268373/100000000000000 : ℝ)^3183
        have hw : |(5391273639/10000000000 : ℝ)|=(5391273639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s7_5 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312653117/10000000000 : ℝ)*x 0 + (-41370673/200000000 : ℝ)*x 1 + (2695637509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312653117/10000000000 : ℝ)^4207 ≤ (8669053007443/20000000000000 : ℝ)^3183 := by
    have hnat : (5312653117 : ℕ)^4207*20000000000000^3183 ≤ 8669053007443^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312653117 10000000000 8669053007443 20000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41370673/200000000 : ℝ)^4207 ≤ (12459626737783/100000000000000 : ℝ)^3183 := by
    have hnat : (41370673 : ℕ)^4207*100000000000000^3183 ≤ 12459626737783^3183*200000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41370673 200000000 12459626737783 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695637509/5000000000 : ℝ)^4207 ≤ (22097554104741/50000000000000 : ℝ)^3183 := by
    have hnat : (2695637509 : ℕ)^4207*50000000000000^3183 ≤ 22097554104741^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695637509 5000000000 22097554104741 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312653117/10000000000 : ℝ), (-41370673/200000000 : ℝ), (2695637509/5000000000 : ℝ)] ![(8669053007443/20000000000000 : ℝ), (12459626737783/100000000000000 : ℝ), (22097554104741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312653117/10000000000 : ℝ)|^4207 ≤ (8669053007443/20000000000000 : ℝ)^3183
        have hw : |(5312653117/10000000000 : ℝ)|=(5312653117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41370673/200000000 : ℝ)|^4207 ≤ (12459626737783/100000000000000 : ℝ)^3183
        have hw : |(-41370673/200000000 : ℝ)|=(41370673/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695637509/5000000000 : ℝ)|^4207 ≤ (22097554104741/50000000000000 : ℝ)^3183
        have hw : |(2695637509/5000000000 : ℝ)|=(2695637509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s7_6 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062530831/2000000000 : ℝ)*x 0 + (1347818367/2500000000 : ℝ)*x 1 + (-2068534353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062530831/2000000000 : ℝ)^4207 ≤ (43345276230651/100000000000000 : ℝ)^3183 := by
    have hnat : (1062530831 : ℕ)^4207*100000000000000^3183 ≤ 43345276230651^3183*2000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062530831 2000000000 43345276230651 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347818367/2500000000 : ℝ)^4207 ≤ (2762193213477/6250000000000 : ℝ)^3183 := by
    have hnat : (1347818367 : ℕ)^4207*6250000000000^3183 ≤ 2762193213477^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347818367 2500000000 2762193213477 6250000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2068534353/10000000000 : ℝ)^4207 ≤ (1557454041813/12500000000000 : ℝ)^3183 := by
    have hnat : (2068534353 : ℕ)^4207*12500000000000^3183 ≤ 1557454041813^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068534353 10000000000 1557454041813 12500000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062530831/2000000000 : ℝ), (1347818367/2500000000 : ℝ), (-2068534353/10000000000 : ℝ)] ![(43345276230651/100000000000000 : ℝ), (2762193213477/6250000000000 : ℝ), (1557454041813/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062530831/2000000000 : ℝ)|^4207 ≤ (43345276230651/100000000000000 : ℝ)^3183
        have hw : |(1062530831/2000000000 : ℝ)|=(1062530831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347818367/2500000000 : ℝ)|^4207 ≤ (2762193213477/6250000000000 : ℝ)^3183
        have hw : |(1347818367/2500000000 : ℝ)|=(1347818367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2068534353/10000000000 : ℝ)|^4207 ≤ (1557454041813/12500000000000 : ℝ)^3183
        have hw : |(-2068534353/10000000000 : ℝ)|=(2068534353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s7_7 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4353670667/10000000000 : ℝ)*x 0 + (4480739571/10000000000 : ℝ)*x 1 + (4230144027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353670667/10000000000 : ℝ)^4207 ≤ (33317479015913/100000000000000 : ℝ)^3183 := by
    have hnat : (4353670667 : ℕ)^4207*100000000000000^3183 ≤ 33317479015913^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353670667 10000000000 33317479015913 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4480739571/10000000000 : ℝ)^4207 ≤ (34608735870537/100000000000000 : ℝ)^3183 := by
    have hnat : (4480739571 : ℕ)^4207*100000000000000^3183 ≤ 34608735870537^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480739571 10000000000 34608735870537 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230144027/10000000000 : ℝ)^4207 ≤ (2004611568863/6250000000000 : ℝ)^3183 := by
    have hnat : (4230144027 : ℕ)^4207*6250000000000^3183 ≤ 2004611568863^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230144027 10000000000 2004611568863 6250000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353670667/10000000000 : ℝ), (4480739571/10000000000 : ℝ), (4230144027/10000000000 : ℝ)] ![(33317479015913/100000000000000 : ℝ), (34608735870537/100000000000000 : ℝ), (2004611568863/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353670667/10000000000 : ℝ)|^4207 ≤ (33317479015913/100000000000000 : ℝ)^3183
        have hw : |(4353670667/10000000000 : ℝ)|=(4353670667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4480739571/10000000000 : ℝ)|^4207 ≤ (34608735870537/100000000000000 : ℝ)^3183
        have hw : |(4480739571/10000000000 : ℝ)|=(4480739571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230144027/10000000000 : ℝ)|^4207 ≤ (2004611568863/6250000000000 : ℝ)^3183
        have hw : |(4230144027/10000000000 : ℝ)|=(4230144027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1221_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1431/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11453/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7047/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7049/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1431/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7049/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1431/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7049/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1431/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7049/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1431/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7049/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1431/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7049/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1431/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1431/12500 : ℝ) ^ (8413/2048 : ℝ) ≤ (13593955668684931/100000000000000000000 : ℝ) := by
    have hpowers : (1431/12500 : ℝ)^8413 ≤ (13593955668684931/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1431 : ℕ)^8413*100000000000000000000^2048 ≤ 13593955668684931^2048*12500^8413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1431 12500 13593955668684931 100000000000000000000 8413 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1431/12500 : ℝ)) (X := (13593955668684931/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7049/50000 : ℝ) ^ (8413/2048 : ℝ) ≤ (31975362630262799/100000000000000000000 : ℝ) := by
    have hpowers : (7049/50000 : ℝ)^8413 ≤ (31975362630262799/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7049 : ℕ)^8413*100000000000000000000^2048 ≤ 31975362630262799^2048*50000^8413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7049 50000 31975362630262799 100000000000000000000 8413 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7049/50000 : ℝ)) (X := (31975362630262799/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013593955668684931/50000000000000000000 : ℝ) ≤ (2000132354966599/2000000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (50013593955668684931/50000000000000000000 : ℝ)^2048 ≤ (2000132354966599/2000000000000000 : ℝ)^8413 := by
      have hnat : (50013593955668684931 : ℕ)^2048*2000000000000000^8413 ≤ 2000132354966599^8413*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013593955668684931 50000000000000000000 2000132354966599 2000000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000132354966599/2000000000000000 : ℝ)) (X := (50013593955668684931/50000000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004556931829894773/10000000000000000000 : ℝ) ≤ (5000554557711399/5000000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (10004556931829894773/10000000000000000000 : ℝ)^2048 ≤ (5000554557711399/5000000000000000 : ℝ)^8413 := by
      have hnat : (10004556931829894773 : ℕ)^2048*5000000000000000^8413 ≤ 5000554557711399^8413*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004556931829894773 10000000000000000000 5000554557711399 5000000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000554557711399/5000000000000000 : ℝ)) (X := (10004556931829894773/10000000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031975362630262799/50000000000000000000 : ℝ) ≤ (10001556456012601/10000000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (50031975362630262799/50000000000000000000 : ℝ)^2048 ≤ (10001556456012601/10000000000000000 : ℝ)^8413 := by
      have hnat : (50031975362630262799 : ℕ)^2048*10000000000000000^8413 ≤ 10001556456012601^8413*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031975362630262799 50000000000000000000 10001556456012601 10000000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001556456012601/10000000000000000 : ℝ)) (X := (50031975362630262799/50000000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13593955668684931/100000000000000000000 : ℝ) ≤ ((249919918803427427/250000000000000000 : ℝ)+2*(447340589803/265000000000000 : ℝ)*(1431/12500 : ℝ))^(8413/2048 : ℝ) := by
    rw [show (249919918803427427/250000000000000000 : ℝ)+2*(447340589803/265000000000000 : ℝ)*(1431/12500 : ℝ)=(2000132354966599/2000000000000000 : ℝ) by norm_num, show 1+2*(13593955668684931/100000000000000000000 : ℝ)=(50013593955668684931/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31975362630262799/100000000000000000000 : ℝ)+(13593955668684931/100000000000000000000 : ℝ) ≤ ((249919918803427427/250000000000000000 : ℝ)+(447340589803/265000000000000 : ℝ)*((7049/50000 : ℝ)+(1431/12500 : ℝ)))^(8413/2048 : ℝ) := by
    rw [show (249919918803427427/250000000000000000 : ℝ)+(447340589803/265000000000000 : ℝ)*((7049/50000 : ℝ)+(1431/12500 : ℝ))=(5000554557711399/5000000000000000 : ℝ) by norm_num, show 1+(31975362630262799/100000000000000000000 : ℝ)+(13593955668684931/100000000000000000000 : ℝ)=(10004556931829894773/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31975362630262799/100000000000000000000 : ℝ) ≤ ((249919918803427427/250000000000000000 : ℝ)+2*(447340589803/265000000000000 : ℝ)*(7049/50000 : ℝ))^(8413/2048 : ℝ) := by
    rw [show (249919918803427427/250000000000000000 : ℝ)+2*(447340589803/265000000000000 : ℝ)*(7049/50000 : ℝ)=(10001556456012601/10000000000000000 : ℝ) by norm_num, show 1+2*(31975362630262799/100000000000000000000 : ℝ)=(50031975362630262799/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (249919918803427427/250000000000000000 : ℝ)*(X 1 0+X 2 0)+(447340589803/265000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (1431/12500 : ℝ)) (hi := (7049/50000 : ℝ)) (c := (249919918803427427/250000000000000000 : ℝ)) (alpha := (447340589803/265000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (249919918803427427/250000000000000000 : ℝ)*(X 0 1+X 2 1)+(447340589803/265000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (1431/12500 : ℝ)) (hi := (7049/50000 : ℝ)) (c := (249919918803427427/250000000000000000 : ℝ)) (alpha := (447340589803/265000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (249919918803427427/250000000000000000 : ℝ)*(X 0 2+X 1 2)+(447340589803/265000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (1431/12500 : ℝ)) (hi := (7049/50000 : ℝ)) (c := (249919918803427427/250000000000000000 : ℝ)) (alpha := (447340589803/265000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1064835167/5000000000 : ℝ)*X 0 0+(5391589867/10000000000 : ℝ)*X 0 1+(2633462553/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534441649/1000000000 : ℝ)*X 1 0+(-548220857/2500000000 : ℝ)*X 1 1+(5266925217/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213776653/400000000 : ℝ)*X 2 0+(2633462737/5000000000 : ℝ)*X 2 1+(-438576661/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4353661017/10000000000 : ℝ)*X 0 0+(4229508053/10000000000 : ℝ)*X 0 1+(4481373409/10000000000 : ℝ)*X 0 2+(4353661017/10000000000 : ℝ)*X 1 0+(4229508053/10000000000 : ℝ)*X 1 1+(4481373409/10000000000 : ℝ)*X 1 2+(4353661017/10000000000 : ℝ)*X 2 0+(4229508053/10000000000 : ℝ)*X 2 1+(4481373409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2129674839/10000000000 : ℝ)*X 0 0+(105344807/200000000 : ℝ)*X 0 1+(5391273639/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312653117/10000000000 : ℝ)*X 1 0+(-41370673/200000000 : ℝ)*X 1 1+(2695637509/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062530831/2000000000 : ℝ)*X 2 0+(1347818367/2500000000 : ℝ)*X 2 1+(-2068534353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4353670667/10000000000 : ℝ)*X 0 0+(4480739571/10000000000 : ℝ)*X 0 1+(4230144027/10000000000 : ℝ)*X 0 2+(4353670667/10000000000 : ℝ)*X 1 0+(4480739571/10000000000 : ℝ)*X 1 1+(4230144027/10000000000 : ℝ)*X 1 2+(4353670667/10000000000 : ℝ)*X 2 0+(4480739571/10000000000 : ℝ)*X 2 1+(4230144027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (61160578374871071886380261/12500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34318811/6250000000000 : ℝ)*(base19) + (108361159/100000000000000 : ℝ)*(base23) + (83838251/100000000000000 : ℝ)*(upper3) + (12899259/12500000000000 : ℝ)*(upper4) + (50133601/50000000000000 : ℝ)*(upper5) + (5995968134875581/100000000000000 : ℝ)*(major0) + (5995968134875581/100000000000000 : ℝ)*(major1) + (5995968134875581/100000000000000 : ℝ)*(major2) + (4010766344070283/50000000000000 : ℝ)*(sp0) + (4010776728857237/50000000000000 : ℝ)*(sp1) + (802155389845429/10000000000000 : ℝ)*(sp2) + (3970379001285251/100000000000000 : ℝ)*(sp3) + (21318674883/100000000000000 : ℝ)*(sp4) + (309855557/10000000000000 : ℝ)*(sp7) + (3970382099840821/100000000000000 : ℝ)*(f.failure) + (160431080136309/2000000000000 : ℝ)*(f.sum) + (19680701918543/13250000000000000000000000000 : ℝ)*base65 + (4643027051675965389/1325000000000000000000000000000000 : ℝ)*base68 + (3798034453200965389/1325000000000000000000000000000000 : ℝ)*base70 + (17499258395424034611/1325000000000000000000000000000000 : ℝ)*base71 + (32392623887707/13250000000000000000000000000 : ℝ)*base74 + (37777303856325965389/1325000000000000000000000000000000 : ℝ)*base76 + (18520877191325965389/1325000000000000000000000000000000 : ℝ)*base78 + (21540020111724034611/1325000000000000000000000000000000 : ℝ)*base79 + (14432972863793/13250000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (1562313/156250000000000000000 : ℝ)*base90 + (1562313/156250000000000000000 : ℝ)*base92 + (1562313/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (107796364293538166888019489/12500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (170323869/12500000000000 : ℝ)*(base19) + (482611/15625000000 : ℝ)*(base23) + (233718977/100000000000000 : ℝ)*(upper3) + (141378203/100000000000000 : ℝ)*(lower4) + (6026462623994169/100000000000000 : ℝ)*(major0) + (6026462623994169/100000000000000 : ℝ)*(major1) + (6026462623994169/100000000000000 : ℝ)*(major2) + (60557387093/50000000000000 : ℝ)*(sp1) + (50922045407/50000000000000 : ℝ)*(sp2) + (35079448573/100000000000000 : ℝ)*(sp3) + (1612470032538939/20000000000000 : ℝ)*(sp4) + (8062227685329557/100000000000000 : ℝ)*(sp5) + (201556130747337/2500000000000 : ℝ)*(sp6) + (399053971838809/10000000000000 : ℝ)*(sp7) + (498821849729583/12500000000000 : ℝ)*(f.failure) + (1612470032538939/20000000000000 : ℝ)*(f.sum) + (85538455284207/13250000000000000000000000000 : ℝ)*base65 + (5999863823867972361/1325000000000000000000000000000000 : ℝ)*base68 + (5132298731157027639/1325000000000000000000000000000000 : ℝ)*base69 + (9409393667942972361/1325000000000000000000000000000000 : ℝ)*base72 + (12034934729543/13250000000000000000000000000 : ℝ)*base74 + (9244422606182027639/1325000000000000000000000000000000 : ℝ)*base75 + (8615111342267972361/1325000000000000000000000000000000 : ℝ)*base78 + (8095008448317972361/1325000000000000000000000000000000 : ℝ)*base80 + (34258313088457/13250000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (408777/39062500000000000000 : ℝ)*base89 + (408777/39062500000000000000 : ℝ)*base91 + (408777/39062500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1221_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1431/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11453/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1221_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1221_s8_0 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2129670229/10000000000 : ℝ)*x 0 + (1078309761/2000000000 : ℝ)*x 1 + (1316741639/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129670229/10000000000 : ℝ)^4207 ≤ (3237161421727/25000000000000 : ℝ)^3183 := by
    have hnat : (2129670229 : ℕ)^4207*25000000000000^3183 ≤ 3237161421727^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129670229 10000000000 3237161421727 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078309761/2000000000 : ℝ)^4207 ≤ (44198074645319/100000000000000 : ℝ)^3183 := by
    have hnat : (1078309761 : ℕ)^4207*100000000000000^3183 ≤ 44198074645319^3183*2000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078309761 2000000000 44198074645319 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316741639/2500000000 : ℝ)^4207 ≤ (21426639825173/50000000000000 : ℝ)^3183 := by
    have hnat : (1316741639 : ℕ)^4207*50000000000000^3183 ≤ 21426639825173^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316741639 2500000000 21426639825173 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2129670229/10000000000 : ℝ), (1078309761/2000000000 : ℝ), (1316741639/2500000000 : ℝ)] ![(3237161421727/25000000000000 : ℝ), (44198074645319/100000000000000 : ℝ), (21426639825173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2129670229/10000000000 : ℝ)|^4207 ≤ (3237161421727/25000000000000 : ℝ)^3183
        have hw : |(-2129670229/10000000000 : ℝ)|=(2129670229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078309761/2000000000 : ℝ)|^4207 ≤ (44198074645319/100000000000000 : ℝ)^3183
        have hw : |(1078309761/2000000000 : ℝ)|=(1078309761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316741639/2500000000 : ℝ)|^4207 ≤ (21426639825173/50000000000000 : ℝ)^3183
        have hw : |(1316741639/2500000000 : ℝ)|=(1316741639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s8_1 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344407241/10000000000 : ℝ)*x 0 + (-438568189/2000000000 : ℝ)*x 1 + (1316741639/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344407241/10000000000 : ℝ)^4207 ≤ (21844009702363/50000000000000 : ℝ)^3183 := by
    have hnat : (5344407241 : ℕ)^4207*50000000000000^3183 ≤ 21844009702363^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344407241 10000000000 21844009702363 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438568189/2000000000 : ℝ)^4207 ≤ (2691740186961/20000000000000 : ℝ)^3183 := by
    have hnat : (438568189 : ℕ)^4207*20000000000000^3183 ≤ 2691740186961^3183*2000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438568189 2000000000 2691740186961 20000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316741639/2500000000 : ℝ)^4207 ≤ (21426639825173/50000000000000 : ℝ)^3183 := by
    have hnat : (1316741639 : ℕ)^4207*50000000000000^3183 ≤ 21426639825173^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316741639 2500000000 21426639825173 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344407241/10000000000 : ℝ), (-438568189/2000000000 : ℝ), (1316741639/2500000000 : ℝ)] ![(21844009702363/50000000000000 : ℝ), (2691740186961/20000000000000 : ℝ), (21426639825173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344407241/10000000000 : ℝ)|^4207 ≤ (21844009702363/50000000000000 : ℝ)^3183
        have hw : |(5344407241/10000000000 : ℝ)|=(5344407241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-438568189/2000000000 : ℝ)|^4207 ≤ (2691740186961/20000000000000 : ℝ)^3183
        have hw : |(-438568189/2000000000 : ℝ)|=(438568189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316741639/2500000000 : ℝ)|^4207 ≤ (21426639825173/50000000000000 : ℝ)^3183
        have hw : |(1316741639/2500000000 : ℝ)|=(1316741639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s8_2 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344407241/10000000000 : ℝ)*x 0 + (1316741639/2500000000 : ℝ)*x 1 + (-438568189/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344407241/10000000000 : ℝ)^4207 ≤ (21844009702363/50000000000000 : ℝ)^3183 := by
    have hnat : (5344407241 : ℕ)^4207*50000000000000^3183 ≤ 21844009702363^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344407241 10000000000 21844009702363 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316741639/2500000000 : ℝ)^4207 ≤ (21426639825173/50000000000000 : ℝ)^3183 := by
    have hnat : (1316741639 : ℕ)^4207*50000000000000^3183 ≤ 21426639825173^3183*2500000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316741639 2500000000 21426639825173 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (438568189/2000000000 : ℝ)^4207 ≤ (2691740186961/20000000000000 : ℝ)^3183 := by
    have hnat : (438568189 : ℕ)^4207*20000000000000^3183 ≤ 2691740186961^3183*2000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438568189 2000000000 2691740186961 20000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344407241/10000000000 : ℝ), (1316741639/2500000000 : ℝ), (-438568189/2000000000 : ℝ)] ![(21844009702363/50000000000000 : ℝ), (21426639825173/50000000000000 : ℝ), (2691740186961/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344407241/10000000000 : ℝ)|^4207 ≤ (21844009702363/50000000000000 : ℝ)^3183
        have hw : |(5344407241/10000000000 : ℝ)|=(5344407241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316741639/2500000000 : ℝ)|^4207 ≤ (21426639825173/50000000000000 : ℝ)^3183
        have hw : |(1316741639/2500000000 : ℝ)|=(1316741639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-438568189/2000000000 : ℝ)|^4207 ≤ (2691740186961/20000000000000 : ℝ)^3183
        have hw : |(-438568189/2000000000 : ℝ)|=(438568189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s8_3 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (544207911/1250000000 : ℝ)*x 0 + (264349413/625000000 : ℝ)*x 1 + (4481290127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544207911/1250000000 : ℝ)^4207 ≤ (33317404379661/100000000000000 : ℝ)^3183 := by
    have hnat : (544207911 : ℕ)^4207*100000000000000^3183 ≤ 33317404379661^3183*1250000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544207911 1250000000 33317404379661 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264349413/625000000 : ℝ)^4207 ≤ (100213247353/312500000000 : ℝ)^3183 := by
    have hnat : (264349413 : ℕ)^4207*312500000000^3183 ≤ 100213247353^3183*625000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264349413 625000000 100213247353 312500000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4481290127/10000000000 : ℝ)^4207 ≤ (276914851693/800000000000 : ℝ)^3183 := by
    have hnat : (4481290127 : ℕ)^4207*800000000000^3183 ≤ 276914851693^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481290127 10000000000 276914851693 800000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544207911/1250000000 : ℝ), (264349413/625000000 : ℝ), (4481290127/10000000000 : ℝ)] ![(33317404379661/100000000000000 : ℝ), (100213247353/312500000000 : ℝ), (276914851693/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544207911/1250000000 : ℝ)|^4207 ≤ (33317404379661/100000000000000 : ℝ)^3183
        have hw : |(544207911/1250000000 : ℝ)|=(544207911/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264349413/625000000 : ℝ)|^4207 ≤ (100213247353/312500000000 : ℝ)^3183
        have hw : |(264349413/625000000 : ℝ)|=(264349413/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4481290127/10000000000 : ℝ)|^4207 ≤ (276914851693/800000000000 : ℝ)^3183
        have hw : |(4481290127/10000000000 : ℝ)|=(4481290127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s8_4 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-133104683/625000000 : ℝ)*x 0 + (210691213/400000000 : ℝ)*x 1 + (673904237/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133104683/625000000 : ℝ)^4207 ≤ (517947337951/4000000000000 : ℝ)^3183 := by
    have hnat : (133104683 : ℕ)^4207*4000000000000^3183 ≤ 517947337951^3183*625000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133104683 625000000 517947337951 4000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210691213/400000000 : ℝ)^4207 ≤ (21428326935863/50000000000000 : ℝ)^3183 := by
    have hnat : (210691213 : ℕ)^4207*50000000000000^3183 ≤ 21428326935863^3183*400000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210691213 400000000 21428326935863 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673904237/1250000000 : ℝ)^4207 ≤ (44194662663753/100000000000000 : ℝ)^3183 := by
    have hnat : (673904237 : ℕ)^4207*100000000000000^3183 ≤ 44194662663753^3183*1250000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673904237 1250000000 44194662663753 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-133104683/625000000 : ℝ), (210691213/400000000 : ℝ), (673904237/1250000000 : ℝ)] ![(517947337951/4000000000000 : ℝ), (21428326935863/50000000000000 : ℝ), (44194662663753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-133104683/625000000 : ℝ)|^4207 ≤ (517947337951/4000000000000 : ℝ)^3183
        have hw : |(-133104683/625000000 : ℝ)|=(133104683/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210691213/400000000 : ℝ)|^4207 ≤ (21428326935863/50000000000000 : ℝ)^3183
        have hw : |(210691213/400000000 : ℝ)|=(210691213/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673904237/1250000000 : ℝ)|^4207 ≤ (44194662663753/100000000000000 : ℝ)^3183
        have hw : |(673904237/1250000000 : ℝ)|=(673904237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s8_5 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656332571/5000000000 : ℝ)*x 0 + (-2068573393/10000000000 : ℝ)*x 1 + (5391233847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656332571/5000000000 : ℝ)^4207 ≤ (43345394710741/100000000000000 : ℝ)^3183 := by
    have hnat : (2656332571 : ℕ)^4207*100000000000000^3183 ≤ 43345394710741^3183*5000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656332571 5000000000 43345394710741 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2068573393/10000000000 : ℝ)^4207 ≤ (12459943140573/100000000000000 : ℝ)^3183 := by
    have hnat : (2068573393 : ℕ)^4207*100000000000000^3183 ≤ 12459943140573^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068573393 10000000000 12459943140573 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391233847/10000000000 : ℝ)^4207 ≤ (11048665533213/25000000000000 : ℝ)^3183 := by
    have hnat : (5391233847 : ℕ)^4207*25000000000000^3183 ≤ 11048665533213^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391233847 10000000000 11048665533213 25000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656332571/5000000000 : ℝ), (-2068573393/10000000000 : ℝ), (5391233847/10000000000 : ℝ)] ![(43345394710741/100000000000000 : ℝ), (12459943140573/100000000000000 : ℝ), (11048665533213/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656332571/5000000000 : ℝ)|^4207 ≤ (43345394710741/100000000000000 : ℝ)^3183
        have hw : |(2656332571/5000000000 : ℝ)|=(2656332571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2068573393/10000000000 : ℝ)|^4207 ≤ (12459943140573/100000000000000 : ℝ)^3183
        have hw : |(-2068573393/10000000000 : ℝ)|=(2068573393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391233847/10000000000 : ℝ)|^4207 ≤ (11048665533213/25000000000000 : ℝ)^3183
        have hw : |(5391233847/10000000000 : ℝ)|=(5391233847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s8_6 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062532963/2000000000 : ℝ)*x 0 + (5391234079/10000000000 : ℝ)*x 1 + (-25857169/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062532963/2000000000 : ℝ)^4207 ≤ (21672695592241/50000000000000 : ℝ)^3183 := by
    have hnat : (1062532963 : ℕ)^4207*50000000000000^3183 ≤ 21672695592241^3183*2000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062532963 2000000000 21672695592241 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391234079/10000000000 : ℝ)^4207 ≤ (22097332323253/50000000000000 : ℝ)^3183 := by
    have hnat : (5391234079 : ℕ)^4207*50000000000000^3183 ≤ 22097332323253^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391234079 10000000000 22097332323253 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25857169/125000000 : ℝ)^4207 ≤ (12459944151651/100000000000000 : ℝ)^3183 := by
    have hnat : (25857169 : ℕ)^4207*100000000000000^3183 ≤ 12459944151651^3183*125000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25857169 125000000 12459944151651 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062532963/2000000000 : ℝ), (5391234079/10000000000 : ℝ), (-25857169/125000000 : ℝ)] ![(21672695592241/50000000000000 : ℝ), (22097332323253/50000000000000 : ℝ), (12459944151651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062532963/2000000000 : ℝ)|^4207 ≤ (21672695592241/50000000000000 : ℝ)^3183
        have hw : |(1062532963/2000000000 : ℝ)|=(1062532963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391234079/10000000000 : ℝ)|^4207 ≤ (22097332323253/50000000000000 : ℝ)^3183
        have hw : |(5391234079/10000000000 : ℝ)|=(5391234079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-25857169/125000000 : ℝ)|^4207 ≤ (12459944151651/100000000000000 : ℝ)^3183
        have hw : |(-25857169/125000000 : ℝ)|=(25857169/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1221_s8_7 (p : ℝ) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (87073459/200000000 : ℝ)*x 0 + (4480656137/10000000000 : ℝ)*x 1 + (846045343/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87073459/200000000 : ℝ)^4207 ≤ (6663500421549/20000000000000 : ℝ)^3183 := by
    have hnat : (87073459 : ℕ)^4207*20000000000000^3183 ≤ 6663500421549^3183*200000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87073459 200000000 6663500421549 20000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4480656137/10000000000 : ℝ)^4207 ≤ (17303942058769/50000000000000 : ℝ)^3183 := by
    have hnat : (4480656137 : ℕ)^4207*50000000000000^3183 ≤ 17303942058769^3183*10000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480656137 10000000000 17303942058769 50000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (846045343/2000000000 : ℝ)^4207 ≤ (32074613758777/100000000000000 : ℝ)^3183 := by
    have hnat : (846045343 : ℕ)^4207*100000000000000^3183 ≤ 32074613758777^3183*2000000000^4207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846045343 2000000000 32074613758777 100000000000000 4207 3183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4207/1024 : ℝ)) 4207 3183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(87073459/200000000 : ℝ), (4480656137/10000000000 : ℝ), (846045343/2000000000 : ℝ)] ![(6663500421549/20000000000000 : ℝ), (17303942058769/50000000000000 : ℝ), (32074613758777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(87073459/200000000 : ℝ)|^4207 ≤ (6663500421549/20000000000000 : ℝ)^3183
        have hw : |(87073459/200000000 : ℝ)|=(87073459/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4480656137/10000000000 : ℝ)|^4207 ≤ (17303942058769/50000000000000 : ℝ)^3183
        have hw : |(4480656137/10000000000 : ℝ)|=(4480656137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(846045343/2000000000 : ℝ)|^4207 ≤ (32074613758777/100000000000000 : ℝ)^3183
        have hw : |(846045343/2000000000 : ℝ)|=(846045343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1221_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11453/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5727/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14093/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7047/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11453/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7047/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11453/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7047/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11453/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7047/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11453/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7047/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11453/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7047/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11453/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11453/100000 : ℝ) ^ (8413/2048 : ℝ) ≤ (13618361967054791/100000000000000000000 : ℝ) := by
    have hpowers : (11453/100000 : ℝ)^8413 ≤ (13618361967054791/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11453 : ℕ)^8413*100000000000000000000^2048 ≤ 13618361967054791^2048*100000^8413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11453 100000 13618361967054791 100000000000000000000 8413 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11453/100000 : ℝ)) (X := (13618361967054791/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7047/50000 : ℝ) ^ (8413/2048 : ℝ) ≤ (1996131926072689/6250000000000000000 : ℝ) := by
    have hpowers : (7047/50000 : ℝ)^8413 ≤ (1996131926072689/6250000000000000000 : ℝ)^2048 := by
      have hnat : (7047 : ℕ)^8413*6250000000000000000^2048 ≤ 1996131926072689^2048*50000^8413 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7047 50000 1996131926072689 6250000000000000000 8413 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7047/50000 : ℝ)) (X := (1996131926072689/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013618361967054791/50000000000000000000 : ℝ) ≤ (10000662962847041/10000000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (50013618361967054791/50000000000000000000 : ℝ)^2048 ≤ (10000662962847041/10000000000000000 : ℝ)^8413 := by
      have hnat : (50013618361967054791 : ℕ)^2048*10000000000000000^8413 ≤ 10000662962847041^8413*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013618361967054791 50000000000000000000 10000662962847041 10000000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000662962847041/10000000000000000 : ℝ)) (X := (50013618361967054791/50000000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009111294556843563/20000000000000000000 : ℝ) ≤ (156267325044197/156250000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (20009111294556843563/20000000000000000000 : ℝ)^2048 ≤ (156267325044197/156250000000000 : ℝ)^8413 := by
      have hnat : (20009111294556843563 : ℕ)^2048*156250000000000^8413 ≤ 156267325044197^8413*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009111294556843563 20000000000000000000 156267325044197 156250000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156267325044197/156250000000000 : ℝ)) (X := (20009111294556843563/20000000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126996131926072689/3125000000000000000 : ℝ) ≤ (400062185712407/400000000000000 : ℝ) ^ (8413/2048 : ℝ) := by
    have hpowers : (3126996131926072689/3125000000000000000 : ℝ)^2048 ≤ (400062185712407/400000000000000 : ℝ)^8413 := by
      have hnat : (3126996131926072689 : ℕ)^2048*400000000000000^8413 ≤ 400062185712407^8413*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126996131926072689 3125000000000000000 400062185712407 400000000000000 2048 8413 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400062185712407/400000000000000 : ℝ)) (X := (3126996131926072689/3125000000000000000 : ℝ)) (by norm_num) 8413 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13618361967054791/100000000000000000000 : ℝ) ≤ ((26401538474261261579/26410000000000000000 : ℝ)+2*(445839981567/264100000000000 : ℝ)*(11453/100000 : ℝ))^(8413/2048 : ℝ) := by
    rw [show (26401538474261261579/26410000000000000000 : ℝ)+2*(445839981567/264100000000000 : ℝ)*(11453/100000 : ℝ)=(10000662962847041/10000000000000000 : ℝ) by norm_num, show 1+2*(13618361967054791/100000000000000000000 : ℝ)=(50013618361967054791/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1996131926072689/6250000000000000000 : ℝ)+(13618361967054791/100000000000000000000 : ℝ) ≤ ((26401538474261261579/26410000000000000000 : ℝ)+(445839981567/264100000000000 : ℝ)*((7047/50000 : ℝ)+(11453/100000 : ℝ)))^(8413/2048 : ℝ) := by
    rw [show (26401538474261261579/26410000000000000000 : ℝ)+(445839981567/264100000000000 : ℝ)*((7047/50000 : ℝ)+(11453/100000 : ℝ))=(156267325044197/156250000000000 : ℝ) by norm_num, show 1+(1996131926072689/6250000000000000000 : ℝ)+(13618361967054791/100000000000000000000 : ℝ)=(20009111294556843563/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1996131926072689/6250000000000000000 : ℝ) ≤ ((26401538474261261579/26410000000000000000 : ℝ)+2*(445839981567/264100000000000 : ℝ)*(7047/50000 : ℝ))^(8413/2048 : ℝ) := by
    rw [show (26401538474261261579/26410000000000000000 : ℝ)+2*(445839981567/264100000000000 : ℝ)*(7047/50000 : ℝ)=(400062185712407/400000000000000 : ℝ) by norm_num, show 1+2*(1996131926072689/6250000000000000000 : ℝ)=(3126996131926072689/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26401538474261261579/26410000000000000000 : ℝ)*(X 1 0+X 2 0)+(445839981567/264100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (11453/100000 : ℝ)) (hi := (7047/50000 : ℝ)) (c := (26401538474261261579/26410000000000000000 : ℝ)) (alpha := (445839981567/264100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26401538474261261579/26410000000000000000 : ℝ)*(X 0 1+X 2 1)+(445839981567/264100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (11453/100000 : ℝ)) (hi := (7047/50000 : ℝ)) (c := (26401538474261261579/26410000000000000000 : ℝ)) (alpha := (445839981567/264100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26401538474261261579/26410000000000000000 : ℝ)*(X 0 2+X 1 2)+(445839981567/264100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8413/2048 : ℝ)) (lo := (11453/100000 : ℝ)) (hi := (7047/50000 : ℝ)) (c := (26401538474261261579/26410000000000000000 : ℝ)) (alpha := (445839981567/264100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2129670229/10000000000 : ℝ)*X 0 0+(1078309761/2000000000 : ℝ)*X 0 1+(1316741639/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344407241/10000000000 : ℝ)*X 1 0+(-438568189/2000000000 : ℝ)*X 1 1+(1316741639/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344407241/10000000000 : ℝ)*X 2 0+(1316741639/2500000000 : ℝ)*X 2 1+(-438568189/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((544207911/1250000000 : ℝ)*X 0 0+(264349413/625000000 : ℝ)*X 0 1+(4481290127/10000000000 : ℝ)*X 0 2+(544207911/1250000000 : ℝ)*X 1 0+(264349413/625000000 : ℝ)*X 1 1+(4481290127/10000000000 : ℝ)*X 1 2+(544207911/1250000000 : ℝ)*X 2 0+(264349413/625000000 : ℝ)*X 2 1+(4481290127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-133104683/625000000 : ℝ)*X 0 0+(210691213/400000000 : ℝ)*X 0 1+(673904237/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656332571/5000000000 : ℝ)*X 1 0+(-2068573393/10000000000 : ℝ)*X 1 1+(5391233847/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062532963/2000000000 : ℝ)*X 2 0+(5391234079/10000000000 : ℝ)*X 2 1+(-25857169/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((87073459/200000000 : ℝ)*X 0 0+(4480656137/10000000000 : ℝ)*X 0 1+(846045343/2000000000 : ℝ)*X 0 2+(87073459/200000000 : ℝ)*X 1 0+(4480656137/10000000000 : ℝ)*X 1 1+(846045343/2000000000 : ℝ)*X 1 2+(87073459/200000000 : ℝ)*X 2 0+(4480656137/10000000000 : ℝ)*X 2 1+(846045343/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1221_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (317414593269409419749956179/132050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (234658907/50000000000000 : ℝ)*(base19) + (436243869/100000000000000 : ℝ)*(base23) + (17676063/100000000000000 : ℝ)*(lower2) + (61131959/100000000000000 : ℝ)*(upper3) + (9205953/25000000000000 : ℝ)*(upper5) + (599992841967533/10000000000000 : ℝ)*(major0) + (599992841967533/10000000000000 : ℝ)*(major1) + (599992841967533/10000000000000 : ℝ)*(major2) + (802683930078681/10000000000000 : ℝ)*(sp0) + (2006712946806217/25000000000000 : ℝ)*(sp1) + (8026851820298813/100000000000000 : ℝ)*(sp2) + (12415617333031/312500000000 : ℝ)*(sp3) + (404867371/3125000000000 : ℝ)*(sp4) + (3478056597/50000000000000 : ℝ)*(sp7) + (1986502251341557/50000000000000 : ℝ)*(f.failure) + (4013426128271341/50000000000000 : ℝ)*(f.sum) + (3401362089173/660250000000000000000000000 : ℝ)*base66 + (3750639342788614607/264100000000000000000000000000000 : ℝ)*base67 + (4561146968829214607/264100000000000000000000000000000 : ℝ)*base69 + (228292593557385393/264100000000000000000000000000000 : ℝ)*base72 + (631223375261/165062500000000000000000000 : ℝ)*base74 + (4660408706631614607/264100000000000000000000000000000 : ℝ)*base75 + (531066273811885393/264100000000000000000000000000000 : ℝ)*base78 + (9324887760438814607/264100000000000000000000000000000 : ℝ)*base79 + (12044691809557/2641000000000000000000000000 : ℝ)*base81 + (612121/78125000000000000000 : ℝ)*base90 + (612121/78125000000000000000 : ℝ)*base92 + (612121/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10410836799542765626266773973/1320500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (510376421/25000000000000 : ℝ)*(base19) + (87501081/5000000000000 : ℝ)*(base23) + (640164973/100000000000000 : ℝ)*(lower1) + (202974151/100000000000000 : ℝ)*(upper3) + (3095503/2500000000000 : ℝ)*(lower4) + (48508137/25000000000000 : ℝ)*(upper5) + (6030293711628171/100000000000000 : ℝ)*(major0) + (6030293711628171/100000000000000 : ℝ)*(major1) + (6030293711628171/100000000000000 : ℝ)*(major2) + (4684456931/100000000000000 : ℝ)*(sp1) + (2016868877737793/25000000000000 : ℝ)*(sp4) + (8067468784988557/100000000000000 : ℝ)*(sp5) + (504217110058097/6250000000000 : ℝ)*(sp6) + (249569478094049/6250000000000 : ℝ)*(sp7) + (249569478094049/6250000000000 : ℝ)*(f.failure) + (2016868877737793/25000000000000 : ℝ)*(f.sum) + (7956839790763/13205000000000000000000000000 : ℝ)*base66 + (10250167429584042009/2641000000000000000000000000000000 : ℝ)*base67 + (6749633611739957991/2641000000000000000000000000000000 : ℝ)*base70 + (12699008383147042009/2641000000000000000000000000000000 : ℝ)*base71 + (62304607746997/13205000000000000000000000000 : ℝ)*base73 + (33081499746037042009/2641000000000000000000000000000000 : ℝ)*base75 + (15750623807867957991/2641000000000000000000000000000000 : ℝ)*base78 + (38906835208756042009/2641000000000000000000000000000000 : ℝ)*base79 + (79345847652357/13205000000000000000000000000 : ℝ)*base81 + (534063/39062500000000000000 : ℝ)*base90 + (534063/39062500000000000000 : ℝ)*base92 + (534063/39062500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1221_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11453/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5727/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1221_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1221_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5713/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5727/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1221_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1221_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1221_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8413/2048 : ℝ) ≤ p) (hpb : p ≤ (4207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2359647/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7061/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5713/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5727/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1221_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
