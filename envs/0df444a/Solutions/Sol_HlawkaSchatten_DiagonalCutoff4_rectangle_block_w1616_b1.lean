-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1616_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:52:32.900754+00:00
-- url     : https://prove2.me/submissions/68f41416-607b-4c69-8235-ecd427a2543b

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
theorem support_rectangle_w1616_s3_0 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-844599109/5000000000 : ℝ)*x 0 + (5458090983/10000000000 : ℝ)*x 1 + (2590479023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (844599109/5000000000 : ℝ)^4783 ≤ (2081233776491/20000000000000 : ℝ)^3759 := by
    have hnat : (844599109 : ℕ)^4783*20000000000000^3759 ≤ 2081233776491^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844599109 5000000000 2081233776491 20000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5458090983/10000000000 : ℝ)^4783 ≤ (4628148559593/10000000000000 : ℝ)^3759 := by
    have hnat : (5458090983 : ℕ)^4783*10000000000000^3759 ≤ 4628148559593^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458090983 10000000000 4628148559593 10000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590479023/5000000000 : ℝ)^4783 ≤ (43312345509813/100000000000000 : ℝ)^3759 := by
    have hnat : (2590479023 : ℕ)^4783*100000000000000^3759 ≤ 43312345509813^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590479023 5000000000 43312345509813 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-844599109/5000000000 : ℝ), (5458090983/10000000000 : ℝ), (2590479023/5000000000 : ℝ)] ![(2081233776491/20000000000000 : ℝ), (4628148559593/10000000000000 : ℝ), (43312345509813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-844599109/5000000000 : ℝ)|^4783 ≤ (2081233776491/20000000000000 : ℝ)^3759
        have hw : |(-844599109/5000000000 : ℝ)|=(844599109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5458090983/10000000000 : ℝ)|^4783 ≤ (4628148559593/10000000000000 : ℝ)^3759
        have hw : |(5458090983/10000000000 : ℝ)|=(5458090983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590479023/5000000000 : ℝ)|^4783 ≤ (43312345509813/100000000000000 : ℝ)^3759
        have hw : |(2590479023/5000000000 : ℝ)|=(2590479023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s3_1 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338209467/2500000000 : ℝ)*x 0 + (-366415333/2000000000 : ℝ)*x 1 + (2590479023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338209467/2500000000 : ℝ)^4783 ≤ (11287217898709/25000000000000 : ℝ)^3759 := by
    have hnat : (1338209467 : ℕ)^4783*25000000000000^3759 ≤ 11287217898709^3759*2500000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338209467 2500000000 11287217898709 25000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (366415333/2000000000 : ℝ)^4783 ≤ (5769391438803/50000000000000 : ℝ)^3759 := by
    have hnat : (366415333 : ℕ)^4783*50000000000000^3759 ≤ 5769391438803^3759*2000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366415333 2000000000 5769391438803 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590479023/5000000000 : ℝ)^4783 ≤ (43312345509813/100000000000000 : ℝ)^3759 := by
    have hnat : (2590479023 : ℕ)^4783*100000000000000^3759 ≤ 43312345509813^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590479023 5000000000 43312345509813 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338209467/2500000000 : ℝ), (-366415333/2000000000 : ℝ), (2590479023/5000000000 : ℝ)] ![(11287217898709/25000000000000 : ℝ), (5769391438803/50000000000000 : ℝ), (43312345509813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338209467/2500000000 : ℝ)|^4783 ≤ (11287217898709/25000000000000 : ℝ)^3759
        have hw : |(1338209467/2500000000 : ℝ)|=(1338209467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-366415333/2000000000 : ℝ)|^4783 ≤ (5769391438803/50000000000000 : ℝ)^3759
        have hw : |(-366415333/2000000000 : ℝ)|=(366415333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590479023/5000000000 : ℝ)|^4783 ≤ (43312345509813/100000000000000 : ℝ)^3759
        have hw : |(2590479023/5000000000 : ℝ)|=(2590479023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s3_2 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338209467/2500000000 : ℝ)*x 0 + (2590479023/5000000000 : ℝ)*x 1 + (-366415333/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338209467/2500000000 : ℝ)^4783 ≤ (11287217898709/25000000000000 : ℝ)^3759 := by
    have hnat : (1338209467 : ℕ)^4783*25000000000000^3759 ≤ 11287217898709^3759*2500000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338209467 2500000000 11287217898709 25000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590479023/5000000000 : ℝ)^4783 ≤ (43312345509813/100000000000000 : ℝ)^3759 := by
    have hnat : (2590479023 : ℕ)^4783*100000000000000^3759 ≤ 43312345509813^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590479023 5000000000 43312345509813 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (366415333/2000000000 : ℝ)^4783 ≤ (5769391438803/50000000000000 : ℝ)^3759 := by
    have hnat : (366415333 : ℕ)^4783*50000000000000^3759 ≤ 5769391438803^3759*2000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366415333 2000000000 5769391438803 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338209467/2500000000 : ℝ), (2590479023/5000000000 : ℝ), (-366415333/2000000000 : ℝ)] ![(11287217898709/25000000000000 : ℝ), (43312345509813/100000000000000 : ℝ), (5769391438803/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338209467/2500000000 : ℝ)|^4783 ≤ (11287217898709/25000000000000 : ℝ)^3759
        have hw : |(1338209467/2500000000 : ℝ)|=(1338209467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590479023/5000000000 : ℝ)|^4783 ≤ (43312345509813/100000000000000 : ℝ)^3759
        have hw : |(2590479023/5000000000 : ℝ)|=(2590479023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-366415333/2000000000 : ℝ)|^4783 ≤ (5769391438803/50000000000000 : ℝ)^3759
        have hw : |(-366415333/2000000000 : ℝ)|=(366415333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s3_3 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52594537/125000000 : ℝ)*x 0 + (3875045941/10000000000 : ℝ)*x 1 + (1140359877/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52594537/125000000 : ℝ)^4783 ≤ (33236227586911/100000000000000 : ℝ)^3759 := by
    have hnat : (52594537 : ℕ)^4783*100000000000000^3759 ≤ 33236227586911^3759*125000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52594537 125000000 33236227586911 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3875045941/10000000000 : ℝ)^4783 ≤ (29930789316223/100000000000000 : ℝ)^3759 := by
    have hnat : (3875045941 : ℕ)^4783*100000000000000^3759 ≤ 29930789316223^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3875045941 10000000000 29930789316223 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1140359877/2500000000 : ℝ)^4783 ≤ (18416491536247/50000000000000 : ℝ)^3759 := by
    have hnat : (1140359877 : ℕ)^4783*50000000000000^3759 ≤ 18416491536247^3759*2500000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140359877 2500000000 18416491536247 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52594537/125000000 : ℝ), (3875045941/10000000000 : ℝ), (1140359877/2500000000 : ℝ)] ![(33236227586911/100000000000000 : ℝ), (29930789316223/100000000000000 : ℝ), (18416491536247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52594537/125000000 : ℝ)|^4783 ≤ (33236227586911/100000000000000 : ℝ)^3759
        have hw : |(52594537/125000000 : ℝ)|=(52594537/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3875045941/10000000000 : ℝ)|^4783 ≤ (29930789316223/100000000000000 : ℝ)^3759
        have hw : |(3875045941/10000000000 : ℝ)|=(3875045941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1140359877/2500000000 : ℝ)|^4783 ≤ (18416491536247/50000000000000 : ℝ)^3759
        have hw : |(1140359877/2500000000 : ℝ)|=(1140359877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s3_4 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-105579261/625000000 : ℝ)*x 0 + (5183029639/10000000000 : ℝ)*x 1 + (2727998771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105579261/625000000 : ℝ)^4783 ≤ (2601679314521/25000000000000 : ℝ)^3759 := by
    have hnat : (105579261 : ℕ)^4783*25000000000000^3759 ≤ 2601679314521^3759*625000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105579261 625000000 2601679314521 25000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183029639/10000000000 : ℝ)^4783 ≤ (43334382778507/100000000000000 : ℝ)^3759 := by
    have hnat : (5183029639 : ℕ)^4783*100000000000000^3759 ≤ 43334382778507^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183029639 10000000000 43334382778507 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2727998771/5000000000 : ℝ)^4783 ≤ (11564724986273/25000000000000 : ℝ)^3759 := by
    have hnat : (2727998771 : ℕ)^4783*25000000000000^3759 ≤ 11564724986273^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727998771 5000000000 11564724986273 25000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-105579261/625000000 : ℝ), (5183029639/10000000000 : ℝ), (2727998771/5000000000 : ℝ)] ![(2601679314521/25000000000000 : ℝ), (43334382778507/100000000000000 : ℝ), (11564724986273/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-105579261/625000000 : ℝ)|^4783 ≤ (2601679314521/25000000000000 : ℝ)^3759
        have hw : |(-105579261/625000000 : ℝ)|=(105579261/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183029639/10000000000 : ℝ)|^4783 ≤ (43334382778507/100000000000000 : ℝ)^3759
        have hw : |(5183029639/10000000000 : ℝ)|=(5183029639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2727998771/5000000000 : ℝ)|^4783 ≤ (11564724986273/25000000000000 : ℝ)^3759
        have hw : |(2727998771/5000000000 : ℝ)|=(2727998771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s3_5 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639580101/5000000000 : ℝ)*x 0 + (-1557037161/10000000000 : ℝ)*x 1 + (1091199507/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639580101/5000000000 : ℝ)^4783 ≤ (44359631722851/100000000000000 : ℝ)^3759 := by
    have hnat : (2639580101 : ℕ)^4783*100000000000000^3759 ≤ 44359631722851^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639580101 5000000000 44359631722851 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1557037161/10000000000 : ℝ)^4783 ≤ (4690734194567/50000000000000 : ℝ)^3759 := by
    have hnat : (1557037161 : ℕ)^4783*50000000000000^3759 ≤ 4690734194567^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557037161 10000000000 4690734194567 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091199507/2000000000 : ℝ)^4783 ≤ (23129449934787/50000000000000 : ℝ)^3759 := by
    have hnat : (1091199507 : ℕ)^4783*50000000000000^3759 ≤ 23129449934787^3759*2000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091199507 2000000000 23129449934787 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639580101/5000000000 : ℝ), (-1557037161/10000000000 : ℝ), (1091199507/2000000000 : ℝ)] ![(44359631722851/100000000000000 : ℝ), (4690734194567/50000000000000 : ℝ), (23129449934787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639580101/5000000000 : ℝ)|^4783 ≤ (44359631722851/100000000000000 : ℝ)^3759
        have hw : |(2639580101/5000000000 : ℝ)|=(2639580101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1557037161/10000000000 : ℝ)|^4783 ≤ (4690734194567/50000000000000 : ℝ)^3759
        have hw : |(-1557037161/10000000000 : ℝ)|=(1557037161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1091199507/2000000000 : ℝ)|^4783 ≤ (23129449934787/50000000000000 : ℝ)^3759
        have hw : |(1091199507/2000000000 : ℝ)|=(1091199507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s3_6 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41243439/78125000 : ℝ)*x 0 + (1363999387/2500000000 : ℝ)*x 1 + (-1557037157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41243439/78125000 : ℝ)^4783 ≤ (44359631615933/100000000000000 : ℝ)^3759 := by
    have hnat : (41243439 : ℕ)^4783*100000000000000^3759 ≤ 44359631615933^3759*78125000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41243439 78125000 44359631615933 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363999387/2500000000 : ℝ)^4783 ≤ (46258900009821/100000000000000 : ℝ)^3759 := by
    have hnat : (1363999387 : ℕ)^4783*100000000000000^3759 ≤ 46258900009821^3759*2500000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363999387 2500000000 46258900009821 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1557037157/10000000000 : ℝ)^4783 ≤ (2345367089617/25000000000000 : ℝ)^3759 := by
    have hnat : (1557037157 : ℕ)^4783*25000000000000^3759 ≤ 2345367089617^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557037157 10000000000 2345367089617 25000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41243439/78125000 : ℝ), (1363999387/2500000000 : ℝ), (-1557037157/10000000000 : ℝ)] ![(44359631615933/100000000000000 : ℝ), (46258900009821/100000000000000 : ℝ), (2345367089617/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41243439/78125000 : ℝ)|^4783 ≤ (44359631615933/100000000000000 : ℝ)^3759
        have hw : |(41243439/78125000 : ℝ)|=(41243439/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1363999387/2500000000 : ℝ)|^4783 ≤ (46258900009821/100000000000000 : ℝ)^3759
        have hw : |(1363999387/2500000000 : ℝ)|=(1363999387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1557037157/10000000000 : ℝ)|^4783 ≤ (2345367089617/25000000000000 : ℝ)^3759
        have hw : |(-1557037157/10000000000 : ℝ)|=(1557037157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s3_7 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4207736221/10000000000 : ℝ)*x 0 + (2278154341/5000000000 : ℝ)*x 1 + (3880230887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4207736221/10000000000 : ℝ)^4783 ≤ (33237969042521/100000000000000 : ℝ)^3759 := by
    have hnat : (4207736221 : ℕ)^4783*100000000000000^3759 ≤ 33237969042521^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4207736221 10000000000 33237969042521 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2278154341/5000000000 : ℝ)^4783 ≤ (36780274196543/100000000000000 : ℝ)^3759 := by
    have hnat : (2278154341 : ℕ)^4783*100000000000000^3759 ≤ 36780274196543^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278154341 5000000000 36780274196543 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3880230887/10000000000 : ℝ)^4783 ≤ (29981756744907/100000000000000 : ℝ)^3759 := by
    have hnat : (3880230887 : ℕ)^4783*100000000000000^3759 ≤ 29981756744907^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3880230887 10000000000 29981756744907 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4207736221/10000000000 : ℝ), (2278154341/5000000000 : ℝ), (3880230887/10000000000 : ℝ)] ![(33237969042521/100000000000000 : ℝ), (36780274196543/100000000000000 : ℝ), (29981756744907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4207736221/10000000000 : ℝ)|^4783 ≤ (33237969042521/100000000000000 : ℝ)^3759
        have hw : |(4207736221/10000000000 : ℝ)|=(4207736221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2278154341/5000000000 : ℝ)|^4783 ≤ (36780274196543/100000000000000 : ℝ)^3759
        have hw : |(2278154341/5000000000 : ℝ)|=(2278154341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3880230887/10000000000 : ℝ)|^4783 ≤ (29981756744907/100000000000000 : ℝ)^3759
        have hw : |(3880230887/10000000000 : ℝ)|=(3880230887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1616_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43459581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16469/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (207/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (327/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8171/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16469/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (207/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16469/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (207/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16469/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (207/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16469/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (207/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16469/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (207/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16469/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (207/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (207/2000 : ℝ) ^ (4779/1024 : ℝ) ≤ (505550220244083/20000000000000000000 : ℝ) := by
    have hpowers : (207/2000 : ℝ)^4779 ≤ (505550220244083/20000000000000000000 : ℝ)^1024 := by
      have hnat : (207 : ℕ)^4779*20000000000000000000^1024 ≤ 505550220244083^1024*2000^4779 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        207 2000 505550220244083 20000000000000000000 4779 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (207/2000 : ℝ)) (X := (505550220244083/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16469/100000 : ℝ) ^ (4779/1024 : ℝ) ≤ (22089815069943523/100000000000000000000 : ℝ) := by
    have hpowers : (16469/100000 : ℝ)^4779 ≤ (22089815069943523/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16469 : ℕ)^4779*100000000000000000000^1024 ≤ 22089815069943523^1024*100000^4779 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16469 100000 22089815069943523 100000000000000000000 4779 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16469/100000 : ℝ)) (X := (22089815069943523/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000505550220244083/10000000000000000000 : ℝ) ≤ (400004332899301/400000000000000 : ℝ) ^ (4779/1024 : ℝ) := by
    have hpowers : (10000505550220244083/10000000000000000000 : ℝ)^1024 ≤ (400004332899301/400000000000000 : ℝ)^4779 := by
      have hnat : (10000505550220244083 : ℕ)^1024*400000000000000^4779 ≤ 400004332899301^4779*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000505550220244083 10000000000000000000 400004332899301 400000000000000 1024 4779 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400004332899301/400000000000000 : ℝ)) (X := (10000505550220244083/10000000000000000000 : ℝ)) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50012308783085581969/50000000000000000000 : ℝ) ≤ (10000527431473527/10000000000000000 : ℝ) ^ (4779/1024 : ℝ) := by
    have hpowers : (50012308783085581969/50000000000000000000 : ℝ)^1024 ≤ (10000527431473527/10000000000000000 : ℝ)^4779 := by
      have hnat : (50012308783085581969 : ℕ)^1024*10000000000000000^4779 ≤ 10000527431473527^4779*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012308783085581969 50000000000000000000 10000527431473527 10000000000000000 1024 4779 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000527431473527/10000000000000000 : ℝ)) (X := (50012308783085581969/50000000000000000000 : ℝ)) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022089815069943523/50000000000000000000 : ℝ) ≤ (10000946540464529/10000000000000000 : ℝ) ^ (4779/1024 : ℝ) := by
    have hpowers : (50022089815069943523/50000000000000000000 : ℝ)^1024 ≤ (10000946540464529/10000000000000000 : ℝ)^4779 := by
      have hnat : (50022089815069943523 : ℕ)^1024*10000000000000000^4779 ≤ 10000946540464529^4779*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022089815069943523 50000000000000000000 10000946540464529 10000000000000000 1024 4779 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000946540464529/10000000000000000 : ℝ)) (X := (50022089815069943523/50000000000000000000 : ℝ)) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(505550220244083/20000000000000000000 : ℝ) ≤ ((2447279490766273163/2447600000000000000 : ℝ)+2*(209554495501/305950000000000 : ℝ)*(207/2000 : ℝ))^(4779/1024 : ℝ) := by
    rw [show (2447279490766273163/2447600000000000000 : ℝ)+2*(209554495501/305950000000000 : ℝ)*(207/2000 : ℝ)=(400004332899301/400000000000000 : ℝ) by norm_num, show 1+2*(505550220244083/20000000000000000000 : ℝ)=(10000505550220244083/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22089815069943523/100000000000000000000 : ℝ)+(505550220244083/20000000000000000000 : ℝ) ≤ ((2447279490766273163/2447600000000000000 : ℝ)+(209554495501/305950000000000 : ℝ)*((16469/100000 : ℝ)+(207/2000 : ℝ)))^(4779/1024 : ℝ) := by
    rw [show (2447279490766273163/2447600000000000000 : ℝ)+(209554495501/305950000000000 : ℝ)*((16469/100000 : ℝ)+(207/2000 : ℝ))=(10000527431473527/10000000000000000 : ℝ) by norm_num, show 1+(22089815069943523/100000000000000000000 : ℝ)+(505550220244083/20000000000000000000 : ℝ)=(50012308783085581969/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22089815069943523/100000000000000000000 : ℝ) ≤ ((2447279490766273163/2447600000000000000 : ℝ)+2*(209554495501/305950000000000 : ℝ)*(16469/100000 : ℝ))^(4779/1024 : ℝ) := by
    rw [show (2447279490766273163/2447600000000000000 : ℝ)+2*(209554495501/305950000000000 : ℝ)*(16469/100000 : ℝ)=(10000946540464529/10000000000000000 : ℝ) by norm_num, show 1+2*(22089815069943523/100000000000000000000 : ℝ)=(50022089815069943523/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2447279490766273163/2447600000000000000 : ℝ)*(X 1 0+X 2 0)+(209554495501/305950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4779/1024 : ℝ)) (lo := (207/2000 : ℝ)) (hi := (16469/100000 : ℝ)) (c := (2447279490766273163/2447600000000000000 : ℝ)) (alpha := (209554495501/305950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2447279490766273163/2447600000000000000 : ℝ)*(X 0 1+X 2 1)+(209554495501/305950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4779/1024 : ℝ)) (lo := (207/2000 : ℝ)) (hi := (16469/100000 : ℝ)) (c := (2447279490766273163/2447600000000000000 : ℝ)) (alpha := (209554495501/305950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2447279490766273163/2447600000000000000 : ℝ)*(X 0 2+X 1 2)+(209554495501/305950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4779/1024 : ℝ)) (lo := (207/2000 : ℝ)) (hi := (16469/100000 : ℝ)) (c := (2447279490766273163/2447600000000000000 : ℝ)) (alpha := (209554495501/305950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-844599109/5000000000 : ℝ)*X 0 0+(5458090983/10000000000 : ℝ)*X 0 1+(2590479023/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338209467/2500000000 : ℝ)*X 1 0+(-366415333/2000000000 : ℝ)*X 1 1+(2590479023/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338209467/2500000000 : ℝ)*X 2 0+(2590479023/5000000000 : ℝ)*X 2 1+(-366415333/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((52594537/125000000 : ℝ)*X 0 0+(3875045941/10000000000 : ℝ)*X 0 1+(1140359877/2500000000 : ℝ)*X 0 2+(52594537/125000000 : ℝ)*X 1 0+(3875045941/10000000000 : ℝ)*X 1 1+(1140359877/2500000000 : ℝ)*X 1 2+(52594537/125000000 : ℝ)*X 2 0+(3875045941/10000000000 : ℝ)*X 2 1+(1140359877/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-105579261/625000000 : ℝ)*X 0 0+(5183029639/10000000000 : ℝ)*X 0 1+(2727998771/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2639580101/5000000000 : ℝ)*X 1 0+(-1557037161/10000000000 : ℝ)*X 1 1+(1091199507/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((41243439/78125000 : ℝ)*X 2 0+(1363999387/2500000000 : ℝ)*X 2 1+(-1557037157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4207736221/10000000000 : ℝ)*X 0 0+(2278154341/5000000000 : ℝ)*X 0 1+(3880230887/10000000000 : ℝ)*X 0 2+(4207736221/10000000000 : ℝ)*X 1 0+(2278154341/5000000000 : ℝ)*X 1 1+(3880230887/10000000000 : ℝ)*X 1 2+(4207736221/10000000000 : ℝ)*X 2 0+(2278154341/5000000000 : ℝ)*X 2 1+(3880230887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1025981723104182452123916189/122380000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1376865207/100000000000000 : ℝ)*(base19) + (257703603/20000000000000 : ℝ)*(base23) + (47290819/100000000000000 : ℝ)*(lower2) + (207526733/100000000000000 : ℝ)*(upper3) + (17880037/12500000000000 : ℝ)*(upper5) + (2532657193686301/100000000000000 : ℝ)*(major0) + (2532657193686301/100000000000000 : ℝ)*(major1) + (2532657193686301/100000000000000 : ℝ)*(major2) + (144335748106953/4000000000000 : ℝ)*(sp0) + (72168178097923/2000000000000 : ℝ)*(sp1) + (1804204496621671/50000000000000 : ℝ)*(sp2) + (58275862485569/4000000000000 : ℝ)*(sp3) + (16579087533/100000000000000 : ℝ)*(sp4) + (3632009779/50000000000000 : ℝ)*(sp7) + (728451913079391/50000000000000 : ℝ)*(f.failure) + (1804205140880679/50000000000000 : ℝ)*(f.sum) + (39720112809549/15297500000000000000000000000 : ℝ)*base66 + (2790244736661231937/244760000000000000000000000000000 : ℝ)*base68 + (1635058365958871937/244760000000000000000000000000000 : ℝ)*base70 + (875946346874231937/244760000000000000000000000000000 : ℝ)*base72 + (192683820392343/30595000000000000000000000000 : ℝ)*base74 + (2491905329296488063/244760000000000000000000000000000 : ℝ)*base75 + (2067699101596791937/244760000000000000000000000000000 : ℝ)*base78 + (1117637683289568063/244760000000000000000000000000000 : ℝ)*base79 + (24556498915959/15297500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (9904829/1250000000000000000000 : ℝ)*base90 + (9904829/1250000000000000000000 : ℝ)*base92 + (9904829/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (509971057375414551630712911/61190000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (643667127/50000000000000 : ℝ)*(base19) + (1384034579/100000000000000 : ℝ)*(base23) + (177601629/100000000000000 : ℝ)*(upper3) + (45729773/100000000000000 : ℝ)*(lower4) + (169727391/100000000000000 : ℝ)*(upper5) + (1285638349605467/50000000000000 : ℝ)*(major0) + (1285638349605467/50000000000000 : ℝ)*(major1) + (1285638349605467/50000000000000 : ℝ)*(major2) + (14717849111/100000000000000 : ℝ)*(sp1) + (15937118671/100000000000000 : ℝ)*(sp2) + (1831716767033179/50000000000000 : ℝ)*(sp4) + (3663417528882993/100000000000000 : ℝ)*(sp5) + (915854053228277/25000000000000 : ℝ)*(sp6) + (369779896637023/25000000000000 : ℝ)*(sp7) + (369779896637023/25000000000000 : ℝ)*(f.failure) + (1831716767033179/50000000000000 : ℝ)*(f.sum) + (1377472748511/3824375000000000000000000000 : ℝ)*base65 + (823001951887638121/122380000000000000000000000000000 : ℝ)*base67 + (245063609288718121/122380000000000000000000000000000 : ℝ)*base69 + (675999002878838121/122380000000000000000000000000000 : ℝ)*base71 + (39553695696887/7648750000000000000000000000 : ℝ)*base73 + (239198263255218121/122380000000000000000000000000000 : ℝ)*base75 + (1163554775731438121/122380000000000000000000000000000 : ℝ)*base77 + (571810725262198121/122380000000000000000000000000000 : ℝ)*base79 + (47096362423233/30595000000000000000000000000 : ℝ)*base81 + (8832637/625000000000000000000 : ℝ)*base90 + (8832637/625000000000000000000 : ℝ)*base92 + (8832637/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1616_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43459581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16469/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (207/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (327/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8171/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1616_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1616_s4_0 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-337859899/2000000000 : ℝ)*x 0 + (1091516733/2000000000 : ℝ)*x 1 + (2590698987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337859899/2000000000 : ℝ)^4783 ≤ (5203481379239/50000000000000 : ℝ)^3759 := by
    have hnat : (337859899 : ℕ)^4783*50000000000000^3759 ≤ 5203481379239^3759*2000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337859899 2000000000 5203481379239 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091516733/2000000000 : ℝ)^4783 ≤ (23138006021333/50000000000000 : ℝ)^3759 := by
    have hnat : (1091516733 : ℕ)^4783*50000000000000^3759 ≤ 23138006021333^3759*2000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091516733 2000000000 23138006021333 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590698987/5000000000 : ℝ)^4783 ≤ (43317025191461/100000000000000 : ℝ)^3759 := by
    have hnat : (2590698987 : ℕ)^4783*100000000000000^3759 ≤ 43317025191461^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590698987 5000000000 43317025191461 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-337859899/2000000000 : ℝ), (1091516733/2000000000 : ℝ), (2590698987/5000000000 : ℝ)] ![(5203481379239/50000000000000 : ℝ), (23138006021333/50000000000000 : ℝ), (43317025191461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-337859899/2000000000 : ℝ)|^4783 ≤ (5203481379239/50000000000000 : ℝ)^3759
        have hw : |(-337859899/2000000000 : ℝ)|=(337859899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1091516733/2000000000 : ℝ)|^4783 ≤ (23138006021333/50000000000000 : ℝ)^3759
        have hw : |(1091516733/2000000000 : ℝ)|=(1091516733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590698987/5000000000 : ℝ)|^4783 ≤ (43317025191461/100000000000000 : ℝ)^3759
        have hw : |(2590698987/5000000000 : ℝ)|=(2590698987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s4_1 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352701821/10000000000 : ℝ)*x 0 + (-228959363/1250000000 : ℝ)*x 1 + (5181397973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352701821/10000000000 : ℝ)^4783 ≤ (45147411509187/100000000000000 : ℝ)^3759 := by
    have hnat : (5352701821 : ℕ)^4783*100000000000000^3759 ≤ 45147411509187^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352701821 10000000000 45147411509187 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (228959363/1250000000 : ℝ)^4783 ≤ (2307112659527/20000000000000 : ℝ)^3759 := by
    have hnat : (228959363 : ℕ)^4783*20000000000000^3759 ≤ 2307112659527^3759*1250000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228959363 1250000000 2307112659527 20000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181397973/10000000000 : ℝ)^4783 ≤ (43317025180823/100000000000000 : ℝ)^3759 := by
    have hnat : (5181397973 : ℕ)^4783*100000000000000^3759 ≤ 43317025180823^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181397973 10000000000 43317025180823 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352701821/10000000000 : ℝ), (-228959363/1250000000 : ℝ), (5181397973/10000000000 : ℝ)] ![(45147411509187/100000000000000 : ℝ), (2307112659527/20000000000000 : ℝ), (43317025180823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352701821/10000000000 : ℝ)|^4783 ≤ (45147411509187/100000000000000 : ℝ)^3759
        have hw : |(5352701821/10000000000 : ℝ)|=(5352701821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-228959363/1250000000 : ℝ)|^4783 ≤ (2307112659527/20000000000000 : ℝ)^3759
        have hw : |(-228959363/1250000000 : ℝ)|=(228959363/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181397973/10000000000 : ℝ)|^4783 ≤ (43317025180823/100000000000000 : ℝ)^3759
        have hw : |(5181397973/10000000000 : ℝ)|=(5181397973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s4_2 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676350909/5000000000 : ℝ)*x 0 + (5181397971/10000000000 : ℝ)*x 1 + (-183167491/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676350909/5000000000 : ℝ)^4783 ≤ (4514741147699/10000000000000 : ℝ)^3759 := by
    have hnat : (2676350909 : ℕ)^4783*10000000000000^3759 ≤ 4514741147699^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676350909 5000000000 4514741147699 10000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181397971/10000000000 : ℝ)^4783 ≤ (10829256289887/25000000000000 : ℝ)^3759 := by
    have hnat : (5181397971 : ℕ)^4783*25000000000000^3759 ≤ 10829256289887^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181397971 10000000000 10829256289887 25000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (183167491/1000000000 : ℝ)^4783 ≤ (2883890836429/25000000000000 : ℝ)^3759 := by
    have hnat : (183167491 : ℕ)^4783*25000000000000^3759 ≤ 2883890836429^3759*1000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183167491 1000000000 2883890836429 25000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676350909/5000000000 : ℝ), (5181397971/10000000000 : ℝ), (-183167491/1000000000 : ℝ)] ![(4514741147699/10000000000000 : ℝ), (10829256289887/25000000000000 : ℝ), (2883890836429/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676350909/5000000000 : ℝ)|^4783 ≤ (4514741147699/10000000000000 : ℝ)^3759
        have hw : |(2676350909/5000000000 : ℝ)|=(2676350909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181397971/10000000000 : ℝ)|^4783 ≤ (10829256289887/25000000000000 : ℝ)^3759
        have hw : |(5181397971/10000000000 : ℝ)|=(5181397971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-183167491/1000000000 : ℝ)|^4783 ≤ (2883890836429/25000000000000 : ℝ)^3759
        have hw : |(-183167491/1000000000 : ℝ)|=(183167491/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s4_3 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2103814423/5000000000 : ℝ)*x 0 + (1938106029/5000000000 : ℝ)*x 1 + (1140064881/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103814423/5000000000 : ℝ)^4783 ≤ (33236889808331/100000000000000 : ℝ)^3759 := by
    have hnat : (2103814423 : ℕ)^4783*100000000000000^3759 ≤ 33236889808331^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103814423 5000000000 33236889808331 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1938106029/5000000000 : ℝ)^4783 ≤ (29942250495227/100000000000000 : ℝ)^3759 := by
    have hnat : (1938106029 : ℕ)^4783*100000000000000^3759 ≤ 29942250495227^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1938106029 5000000000 29942250495227 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1140064881/2500000000 : ℝ)^4783 ≤ (4602607461123/12500000000000 : ℝ)^3759 := by
    have hnat : (1140064881 : ℕ)^4783*12500000000000^3759 ≤ 4602607461123^3759*2500000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140064881 2500000000 4602607461123 12500000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2103814423/5000000000 : ℝ), (1938106029/5000000000 : ℝ), (1140064881/2500000000 : ℝ)] ![(33236889808331/100000000000000 : ℝ), (29942250495227/100000000000000 : ℝ), (4602607461123/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2103814423/5000000000 : ℝ)|^4783 ≤ (33236889808331/100000000000000 : ℝ)^3759
        have hw : |(2103814423/5000000000 : ℝ)|=(2103814423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1938106029/5000000000 : ℝ)|^4783 ≤ (29942250495227/100000000000000 : ℝ)^3759
        have hw : |(1938106029/5000000000 : ℝ)|=(1938106029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1140064881/2500000000 : ℝ)|^4783 ≤ (4602607461123/12500000000000 : ℝ)^3759
        have hw : |(1140064881/2500000000 : ℝ)|=(1140064881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s4_4 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1689368773/10000000000 : ℝ)*x 0 + (2591727751/5000000000 : ℝ)*x 1 + (5455504487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1689368773/10000000000 : ℝ)^4783 ≤ (1040750581267/10000000000000 : ℝ)^3759 := by
    have hnat : (1689368773 : ℕ)^4783*10000000000000^3759 ≤ 1040750581267^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1689368773 10000000000 1040750581267 10000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591727751/5000000000 : ℝ)^4783 ≤ (43338913337057/100000000000000 : ℝ)^3759 := by
    have hnat : (2591727751 : ℕ)^4783*100000000000000^3759 ≤ 43338913337057^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591727751 5000000000 43338913337057 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5455504487/10000000000 : ℝ)^4783 ≤ (9250716166431/20000000000000 : ℝ)^3759 := by
    have hnat : (5455504487 : ℕ)^4783*20000000000000^3759 ≤ 9250716166431^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455504487 10000000000 9250716166431 20000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1689368773/10000000000 : ℝ), (2591727751/5000000000 : ℝ), (5455504487/10000000000 : ℝ)] ![(1040750581267/10000000000000 : ℝ), (43338913337057/100000000000000 : ℝ), (9250716166431/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1689368773/10000000000 : ℝ)|^4783 ≤ (1040750581267/10000000000000 : ℝ)^3759
        have hw : |(-1689368773/10000000000 : ℝ)|=(1689368773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591727751/5000000000 : ℝ)|^4783 ≤ (43338913337057/100000000000000 : ℝ)^3759
        have hw : |(2591727751/5000000000 : ℝ)|=(2591727751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5455504487/10000000000 : ℝ)|^4783 ≤ (9250716166431/20000000000000 : ℝ)^3759
        have hw : |(5455504487/10000000000 : ℝ)|=(5455504487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s4_5 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279276617/10000000000 : ℝ)*x 0 + (-778784189/5000000000 : ℝ)*x 1 + (681938079/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279276617/10000000000 : ℝ)^4783 ≤ (22180438206701/50000000000000 : ℝ)^3759 := by
    have hnat : (5279276617 : ℕ)^4783*50000000000000^3759 ≤ 22180438206701^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279276617 10000000000 22180438206701 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (778784189/5000000000 : ℝ)^4783 ≤ (1877108235871/20000000000000 : ℝ)^3759 := by
    have hnat : (778784189 : ℕ)^4783*20000000000000^3759 ≤ 1877108235871^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      778784189 5000000000 1877108235871 20000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (681938079/1250000000 : ℝ)^4783 ≤ (23126791198203/50000000000000 : ℝ)^3759 := by
    have hnat : (681938079 : ℕ)^4783*50000000000000^3759 ≤ 23126791198203^3759*1250000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681938079 1250000000 23126791198203 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279276617/10000000000 : ℝ), (-778784189/5000000000 : ℝ), (681938079/1250000000 : ℝ)] ![(22180438206701/50000000000000 : ℝ), (1877108235871/20000000000000 : ℝ), (23126791198203/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279276617/10000000000 : ℝ)|^4783 ≤ (22180438206701/50000000000000 : ℝ)^3759
        have hw : |(5279276617/10000000000 : ℝ)|=(5279276617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-778784189/5000000000 : ℝ)|^4783 ≤ (1877108235871/20000000000000 : ℝ)^3759
        have hw : |(-778784189/5000000000 : ℝ)|=(778784189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(681938079/1250000000 : ℝ)|^4783 ≤ (23126791198203/50000000000000 : ℝ)^3759
        have hw : |(681938079/1250000000 : ℝ)|=(681938079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s4_6 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055855339/2000000000 : ℝ)*x 0 + (545550461/1000000000 : ℝ)*x 1 + (-1557568301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055855339/2000000000 : ℝ)^4783 ≤ (5545109655921/12500000000000 : ℝ)^3759 := by
    have hnat : (1055855339 : ℕ)^4783*12500000000000^3759 ≤ 5545109655921^3759*2000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055855339 2000000000 5545109655921 12500000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545550461/1000000000 : ℝ)^4783 ≤ (1445424442471/3125000000000 : ℝ)^3759 := by
    have hnat : (545550461 : ℕ)^4783*3125000000000^3759 ≤ 1445424442471^3759*1000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545550461 1000000000 1445424442471 3125000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1557568301/10000000000 : ℝ)^4783 ≤ (586596286811/6250000000000 : ℝ)^3759 := by
    have hnat : (1557568301 : ℕ)^4783*6250000000000^3759 ≤ 586596286811^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557568301 10000000000 586596286811 6250000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055855339/2000000000 : ℝ), (545550461/1000000000 : ℝ), (-1557568301/10000000000 : ℝ)] ![(5545109655921/12500000000000 : ℝ), (1445424442471/3125000000000 : ℝ), (586596286811/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055855339/2000000000 : ℝ)|^4783 ≤ (5545109655921/12500000000000 : ℝ)^3759
        have hw : |(1055855339/2000000000 : ℝ)|=(1055855339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(545550461/1000000000 : ℝ)|^4783 ≤ (1445424442471/3125000000000 : ℝ)^3759
        have hw : |(545550461/1000000000 : ℝ)|=(545550461/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1557568301/10000000000 : ℝ)|^4783 ≤ (586596286811/6250000000000 : ℝ)^3759
        have hw : |(-1557568301/10000000000 : ℝ)|=(1557568301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s4_7 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525975037/1250000000 : ℝ)*x 0 + (4555163539/10000000000 : ℝ)*x 1 + (3881361657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525975037/1250000000 : ℝ)^4783 ≤ (8309653267183/25000000000000 : ℝ)^3759 := by
    have hnat : (525975037 : ℕ)^4783*25000000000000^3759 ≤ 8309653267183^3759*1250000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525975037 1250000000 8309653267183 25000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4555163539/10000000000 : ℝ)^4783 ≤ (9192128092753/25000000000000 : ℝ)^3759 := by
    have hnat : (4555163539 : ℕ)^4783*25000000000000^3759 ≤ 9192128092753^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4555163539 10000000000 9192128092753 25000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3881361657/10000000000 : ℝ)^4783 ≤ (5998574910111/20000000000000 : ℝ)^3759 := by
    have hnat : (3881361657 : ℕ)^4783*20000000000000^3759 ≤ 5998574910111^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3881361657 10000000000 5998574910111 20000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525975037/1250000000 : ℝ), (4555163539/10000000000 : ℝ), (3881361657/10000000000 : ℝ)] ![(8309653267183/25000000000000 : ℝ), (9192128092753/25000000000000 : ℝ), (5998574910111/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525975037/1250000000 : ℝ)|^4783 ≤ (8309653267183/25000000000000 : ℝ)^3759
        have hw : |(525975037/1250000000 : ℝ)|=(525975037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4555163539/10000000000 : ℝ)|^4783 ≤ (9192128092753/25000000000000 : ℝ)^3759
        have hw : |(4555163539/10000000000 : ℝ)|=(4555163539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3881361657/10000000000 : ℝ)|^4783 ≤ (5998574910111/20000000000000 : ℝ)^3759
        have hw : |(3881361657/10000000000 : ℝ)|=(3881361657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1616_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43459581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8171/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (327/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (5237/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16331/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8171/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (327/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8171/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (327/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8171/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (327/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8171/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (327/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8171/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (327/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8171/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (327/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (327/3125 : ℝ) ^ (4779/1024 : ℝ) ≤ (83135591440511/3125000000000000000 : ℝ) := by
    have hpowers : (327/3125 : ℝ)^4779 ≤ (83135591440511/3125000000000000000 : ℝ)^1024 := by
      have hnat : (327 : ℕ)^4779*3125000000000000000^1024 ≤ 83135591440511^1024*3125^4779 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        327 3125 83135591440511 3125000000000000000 4779 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (327/3125 : ℝ)) (X := (83135591440511/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8171/50000 : ℝ) ^ (4779/1024 : ℝ) ≤ (10652990691807429/50000000000000000000 : ℝ) := by
    have hpowers : (8171/50000 : ℝ)^4779 ≤ (10652990691807429/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8171 : ℕ)^4779*50000000000000000000^1024 ≤ 10652990691807429^1024*50000^4779 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8171 50000 10652990691807429 50000000000000000000 4779 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8171/50000 : ℝ)) (X := (10652990691807429/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562583135591440511/1562500000000000000 : ℝ) ≤ (5000057002094963/5000000000000000 : ℝ) ^ (4779/1024 : ℝ) := by
    have hpowers : (1562583135591440511/1562500000000000000 : ℝ)^1024 ≤ (5000057002094963/5000000000000000 : ℝ)^4779 := by
      have hnat : (1562583135591440511 : ℕ)^1024*5000000000000000^4779 ≤ 5000057002094963^4779*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562583135591440511 1562500000000000000 5000057002094963 5000000000000000 1024 4779 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000057002094963/5000000000000000 : ℝ)) (X := (1562583135591440511/1562500000000000000 : ℝ)) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10002396632030971121/10000000000000000000 : ℝ) ≤ (2000102695968261/2000000000000000 : ℝ) ^ (4779/1024 : ℝ) := by
    have hpowers : (10002396632030971121/10000000000000000000 : ℝ)^1024 ≤ (2000102695968261/2000000000000000 : ℝ)^4779 := by
      have hnat : (10002396632030971121 : ℕ)^1024*2000000000000000^4779 ≤ 2000102695968261^4779*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002396632030971121 10000000000000000000 2000102695968261 2000000000000000 1024 4779 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000102695968261/2000000000000000 : ℝ)) (X := (10002396632030971121/10000000000000000000 : ℝ)) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010652990691807429/25000000000000000000 : ℝ) ≤ (2500228238873171/2500000000000000 : ℝ) ^ (4779/1024 : ℝ) := by
    have hpowers : (25010652990691807429/25000000000000000000 : ℝ)^1024 ≤ (2500228238873171/2500000000000000 : ℝ)^4779 := by
      have hnat : (25010652990691807429 : ℕ)^1024*2500000000000000^4779 ≤ 2500228238873171^4779*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010652990691807429 25000000000000000000 2500228238873171 2500000000000000 1024 4779 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500228238873171/2500000000000000 : ℝ)) (X := (25010652990691807429/25000000000000000000 : ℝ)) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(83135591440511/3125000000000000000 : ℝ) ≤ ((14693077472549081329/14695000000000000000 : ℝ)+2*(399475651379/587800000000000 : ℝ)*(327/3125 : ℝ))^(4779/1024 : ℝ) := by
    rw [show (14693077472549081329/14695000000000000000 : ℝ)+2*(399475651379/587800000000000 : ℝ)*(327/3125 : ℝ)=(5000057002094963/5000000000000000 : ℝ) by norm_num, show 1+2*(83135591440511/3125000000000000000 : ℝ)=(1562583135591440511/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10652990691807429/50000000000000000000 : ℝ)+(83135591440511/3125000000000000000 : ℝ) ≤ ((14693077472549081329/14695000000000000000 : ℝ)+(399475651379/587800000000000 : ℝ)*((8171/50000 : ℝ)+(327/3125 : ℝ)))^(4779/1024 : ℝ) := by
    rw [show (14693077472549081329/14695000000000000000 : ℝ)+(399475651379/587800000000000 : ℝ)*((8171/50000 : ℝ)+(327/3125 : ℝ))=(2000102695968261/2000000000000000 : ℝ) by norm_num, show 1+(10652990691807429/50000000000000000000 : ℝ)+(83135591440511/3125000000000000000 : ℝ)=(10002396632030971121/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10652990691807429/50000000000000000000 : ℝ) ≤ ((14693077472549081329/14695000000000000000 : ℝ)+2*(399475651379/587800000000000 : ℝ)*(8171/50000 : ℝ))^(4779/1024 : ℝ) := by
    rw [show (14693077472549081329/14695000000000000000 : ℝ)+2*(399475651379/587800000000000 : ℝ)*(8171/50000 : ℝ)=(2500228238873171/2500000000000000 : ℝ) by norm_num, show 1+2*(10652990691807429/50000000000000000000 : ℝ)=(25010652990691807429/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14693077472549081329/14695000000000000000 : ℝ)*(X 1 0+X 2 0)+(399475651379/587800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4779/1024 : ℝ)) (lo := (327/3125 : ℝ)) (hi := (8171/50000 : ℝ)) (c := (14693077472549081329/14695000000000000000 : ℝ)) (alpha := (399475651379/587800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14693077472549081329/14695000000000000000 : ℝ)*(X 0 1+X 2 1)+(399475651379/587800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4779/1024 : ℝ)) (lo := (327/3125 : ℝ)) (hi := (8171/50000 : ℝ)) (c := (14693077472549081329/14695000000000000000 : ℝ)) (alpha := (399475651379/587800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14693077472549081329/14695000000000000000 : ℝ)*(X 0 2+X 1 2)+(399475651379/587800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4779/1024 : ℝ)) (lo := (327/3125 : ℝ)) (hi := (8171/50000 : ℝ)) (c := (14693077472549081329/14695000000000000000 : ℝ)) (alpha := (399475651379/587800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-337859899/2000000000 : ℝ)*X 0 0+(1091516733/2000000000 : ℝ)*X 0 1+(2590698987/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352701821/10000000000 : ℝ)*X 1 0+(-228959363/1250000000 : ℝ)*X 1 1+(5181397973/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676350909/5000000000 : ℝ)*X 2 0+(5181397971/10000000000 : ℝ)*X 2 1+(-183167491/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2103814423/5000000000 : ℝ)*X 0 0+(1938106029/5000000000 : ℝ)*X 0 1+(1140064881/2500000000 : ℝ)*X 0 2+(2103814423/5000000000 : ℝ)*X 1 0+(1938106029/5000000000 : ℝ)*X 1 1+(1140064881/2500000000 : ℝ)*X 1 2+(2103814423/5000000000 : ℝ)*X 2 0+(1938106029/5000000000 : ℝ)*X 2 1+(1140064881/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1689368773/10000000000 : ℝ)*X 0 0+(2591727751/5000000000 : ℝ)*X 0 1+(5455504487/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279276617/10000000000 : ℝ)*X 1 0+(-778784189/5000000000 : ℝ)*X 1 1+(681938079/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1055855339/2000000000 : ℝ)*X 2 0+(545550461/1000000000 : ℝ)*X 2 1+(-1557568301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((525975037/1250000000 : ℝ)*X 0 0+(4555163539/10000000000 : ℝ)*X 0 1+(3881361657/10000000000 : ℝ)*X 0 2+(525975037/1250000000 : ℝ)*X 1 0+(4555163539/10000000000 : ℝ)*X 1 1+(3881361657/10000000000 : ℝ)*X 1 2+(525975037/1250000000 : ℝ)*X 2 0+(4555163539/10000000000 : ℝ)*X 2 1+(3881361657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (510450025267889475993637911/183687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (116314721/25000000000000 : ℝ)*(base19) + (220192013/50000000000000 : ℝ)*(base23) + (611427/5000000000000 : ℝ)*(lower2) + (34975307/50000000000000 : ℝ)*(upper3) + (48243801/100000000000000 : ℝ)*(upper5) + (1270663870779353/50000000000000 : ℝ)*(major0) + (1270663870779353/50000000000000 : ℝ)*(major1) + (1270663870779353/50000000000000 : ℝ)*(major2) + (3620758242629517/100000000000000 : ℝ)*(sp0) + (3620763391139083/100000000000000 : ℝ)*(sp1) + (181038170800697/5000000000000 : ℝ)*(sp2) + (730944533755571/50000000000000 : ℝ)*(sp3) + (112275369/2000000000000 : ℝ)*(sp4) + (1233289073/50000000000000 : ℝ)*(sp7) + (182736441761161/12500000000000 : ℝ)*(f.failure) + (1810381928198983/50000000000000 : ℝ)*(f.sum) + (51907796327199/7347500000000000000000000000 : ℝ)*base66 + (5647476529710574863/734750000000000000000000000000000 : ℝ)*base68 + (7151551564824863/734750000000000000000000000000000 : ℝ)*base70 + (5777514683156574863/734750000000000000000000000000000 : ℝ)*base72 + (34467761956677/14695000000000000000000000000 : ℝ)*base73 + (2245820952787074863/734750000000000000000000000000000 : ℝ)*base76 + (7330021431057324863/734750000000000000000000000000000 : ℝ)*base78 + (1779990695573175137/734750000000000000000000000000000 : ℝ)*base79 + (20751110501437/14695000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2883541/312500000000000000000 : ℝ)*base89 + (2883541/312500000000000000000 : ℝ)*base91 + (2883541/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56653256247868725527427/14695000000000000000000000000 : ℝ) := by norm_num
    linear_combination (248073821/50000000000000 : ℝ)*(base19) + (57365131/10000000000000 : ℝ)*(base23) + (189033431/100000000000000 : ℝ)*(lower1) + (1864039/100000000000000 : ℝ)*(upper2) + (44869879/50000000000000 : ℝ)*(upper3) + (9678113/12500000000000 : ℝ)*(upper5) + (161247341631519/6250000000000 : ℝ)*(major0) + (161247341631519/6250000000000 : ℝ)*(major1) + (161247341631519/6250000000000 : ℝ)*(major2) + (706913559/50000000000000 : ℝ)*(sp2) + (3675801630758199/100000000000000 : ℝ)*(sp4) + (3675801134610557/100000000000000 : ℝ)*(sp5) + (918949910819943/25000000000000 : ℝ)*(sp6) + (742056586470629/50000000000000 : ℝ)*(sp7) + (742056586470629/50000000000000 : ℝ)*(f.failure) + (3675801630758199/100000000000000 : ℝ)*(f.sum) + (93149309172387/14695000000000000000000000000 : ℝ)*base66 + (218609304821666249/91843750000000000000000000000000 : ℝ)*base68 + (824448182084552501/91843750000000000000000000000000 : ℝ)*base69 + (152282844512615001/91843750000000000000000000000000 : ℝ)*base71 + (15952806560003/3673750000000000000000000000 : ℝ)*base74 + (147278600671146251/91843750000000000000000000000000 : ℝ)*base75 + (359228834015666249/91843750000000000000000000000000 : ℝ)*base78 + (1428886345396666249/91843750000000000000000000000000 : ℝ)*base80 + (62415388563711/7347500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (5146449/1250000000000000000000 : ℝ)*base89 + (5146449/1250000000000000000000 : ℝ)*base91 + (5146449/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1616_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43459581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8171/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (327/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5237/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16331/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1616_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1616_s5_0 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352690319/10000000000 : ℝ)*x 0 + (5181435409/10000000000 : ℝ)*x 1 + (-1831640613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352690319/10000000000 : ℝ)^4783 ≤ (45147288067713/100000000000000 : ℝ)^3759 := by
    have hnat : (5352690319 : ℕ)^4783*100000000000000^3759 ≤ 45147288067713^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352690319 10000000000 45147288067713 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181435409/10000000000 : ℝ)^4783 ≤ (43317423406807/100000000000000 : ℝ)^3759 := by
    have hnat : (5181435409 : ℕ)^4783*100000000000000^3759 ≤ 43317423406807^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181435409 10000000000 43317423406807 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1831640613/10000000000 : ℝ)^4783 ≤ (2883822127449/25000000000000 : ℝ)^3759 := by
    have hnat : (1831640613 : ℕ)^4783*25000000000000^3759 ≤ 2883822127449^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1831640613 10000000000 2883822127449 25000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352690319/10000000000 : ℝ), (5181435409/10000000000 : ℝ), (-1831640613/10000000000 : ℝ)] ![(45147288067713/100000000000000 : ℝ), (43317423406807/100000000000000 : ℝ), (2883822127449/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352690319/10000000000 : ℝ)|^4783 ≤ (45147288067713/100000000000000 : ℝ)^3759
        have hw : |(5352690319/10000000000 : ℝ)|=(5352690319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181435409/10000000000 : ℝ)|^4783 ≤ (43317423406807/100000000000000 : ℝ)^3759
        have hw : |(5181435409/10000000000 : ℝ)|=(5181435409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1831640613/10000000000 : ℝ)|^4783 ≤ (2883822127449/25000000000000 : ℝ)^3759
        have hw : |(-1831640613/10000000000 : ℝ)|=(1831640613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s5_1 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (841526901/2000000000 : ℝ)*x 0 + (775262273/2000000000 : ℝ)*x 1 + (228007949/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (841526901/2000000000 : ℝ)^4783 ≤ (16618473343589/50000000000000 : ℝ)^3759 := by
    have hnat : (841526901 : ℕ)^4783*50000000000000^3759 ≤ 16618473343589^3759*2000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841526901 2000000000 16618473343589 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (775262273/2000000000 : ℝ)^4783 ≤ (29943226577317/100000000000000 : ℝ)^3759 := by
    have hnat : (775262273 : ℕ)^4783*100000000000000^3759 ≤ 29943226577317^3759*2000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775262273 2000000000 29943226577317 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (228007949/500000000 : ℝ)^4783 ≤ (7363965344003/20000000000000 : ℝ)^3759 := by
    have hnat : (228007949 : ℕ)^4783*20000000000000^3759 ≤ 7363965344003^3759*500000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228007949 500000000 7363965344003 20000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(841526901/2000000000 : ℝ), (775262273/2000000000 : ℝ), (228007949/500000000 : ℝ)] ![(16618473343589/50000000000000 : ℝ), (29943226577317/100000000000000 : ℝ), (7363965344003/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(841526901/2000000000 : ℝ)|^4783 ≤ (16618473343589/50000000000000 : ℝ)^3759
        have hw : |(841526901/2000000000 : ℝ)|=(841526901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(775262273/2000000000 : ℝ)|^4783 ≤ (29943226577317/100000000000000 : ℝ)^3759
        have hw : |(775262273/2000000000 : ℝ)|=(775262273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(228007949/500000000 : ℝ)|^4783 ≤ (7363965344003/20000000000000 : ℝ)^3759
        have hw : |(228007949/500000000 : ℝ)|=(228007949/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s5_2 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-67575051/400000000 : ℝ)*x 0 + (2591747029/5000000000 : ℝ)*x 1 + (5455461013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67575051/400000000 : ℝ)^4783 ≤ (5203782309737/50000000000000 : ℝ)^3759 := by
    have hnat : (67575051 : ℕ)^4783*50000000000000^3759 ≤ 5203782309737^3759*400000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67575051 400000000 5203782309737 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591747029/5000000000 : ℝ)^4783 ≤ (4333932352143/10000000000000 : ℝ)^3759 := by
    have hnat : (2591747029 : ℕ)^4783*10000000000000^3759 ≤ 4333932352143^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591747029 5000000000 4333932352143 10000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5455461013/10000000000 : ℝ)^4783 ≤ (46253111837787/100000000000000 : ℝ)^3759 := by
    have hnat : (5455461013 : ℕ)^4783*100000000000000^3759 ≤ 46253111837787^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455461013 10000000000 46253111837787 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-67575051/400000000 : ℝ), (2591747029/5000000000 : ℝ), (5455461013/10000000000 : ℝ)] ![(5203782309737/50000000000000 : ℝ), (4333932352143/10000000000000 : ℝ), (46253111837787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-67575051/400000000 : ℝ)|^4783 ≤ (5203782309737/50000000000000 : ℝ)^3759
        have hw : |(-67575051/400000000 : ℝ)|=(67575051/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591747029/5000000000 : ℝ)|^4783 ≤ (4333932352143/10000000000000 : ℝ)^3759
        have hw : |(2591747029/5000000000 : ℝ)|=(2591747029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5455461013/10000000000 : ℝ)|^4783 ≤ (46253111837787/100000000000000 : ℝ)^3759
        have hw : |(5455461013/10000000000 : ℝ)|=(5455461013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s5_3 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279286599/10000000000 : ℝ)*x 0 + (-778807163/5000000000 : ℝ)*x 1 + (2727731041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279286599/10000000000 : ℝ)^4783 ≤ (44360983139697/100000000000000 : ℝ)^3759 := by
    have hnat : (5279286599 : ℕ)^4783*100000000000000^3759 ≤ 44360983139697^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279286599 10000000000 44360983139697 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (778807163/5000000000 : ℝ)^4783 ≤ (2346473369021/25000000000000 : ℝ)^3759 := by
    have hnat : (778807163 : ℕ)^4783*25000000000000^3759 ≤ 2346473369021^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      778807163 5000000000 2346473369021 25000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2727731041/5000000000 : ℝ)^4783 ≤ (46253123370069/100000000000000 : ℝ)^3759 := by
    have hnat : (2727731041 : ℕ)^4783*100000000000000^3759 ≤ 46253123370069^3759*5000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727731041 5000000000 46253123370069 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279286599/10000000000 : ℝ), (-778807163/5000000000 : ℝ), (2727731041/5000000000 : ℝ)] ![(44360983139697/100000000000000 : ℝ), (2346473369021/25000000000000 : ℝ), (46253123370069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279286599/10000000000 : ℝ)|^4783 ≤ (44360983139697/100000000000000 : ℝ)^3759
        have hw : |(5279286599/10000000000 : ℝ)|=(5279286599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-778807163/5000000000 : ℝ)|^4783 ≤ (2346473369021/25000000000000 : ℝ)^3759
        have hw : |(-778807163/5000000000 : ℝ)|=(778807163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2727731041/5000000000 : ℝ)|^4783 ≤ (46253123370069/100000000000000 : ℝ)^3759
        have hw : |(2727731041/5000000000 : ℝ)|=(2727731041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s5_4 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055856799/2000000000 : ℝ)*x 0 + (1091093199/2000000000 : ℝ)*x 1 + (-389403113/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055856799/2000000000 : ℝ)^4783 ≤ (887219105961/2000000000000 : ℝ)^3759 := by
    have hnat : (1055856799 : ℕ)^4783*2000000000000^3759 ≤ 887219105961^3759*2000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055856799 2000000000 887219105961 2000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091093199/2000000000 : ℝ)^4783 ≤ (46253165583191/100000000000000 : ℝ)^3759 := by
    have hnat : (1091093199 : ℕ)^4783*100000000000000^3759 ≤ 46253165583191^3759*2000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091093199 2000000000 46253165583191 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (389403113/2500000000 : ℝ)^4783 ≤ (9385879107523/100000000000000 : ℝ)^3759 := by
    have hnat : (389403113 : ℕ)^4783*100000000000000^3759 ≤ 9385879107523^3759*2500000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389403113 2500000000 9385879107523 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055856799/2000000000 : ℝ), (1091093199/2000000000 : ℝ), (-389403113/2500000000 : ℝ)] ![(887219105961/2000000000000 : ℝ), (46253165583191/100000000000000 : ℝ), (9385879107523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055856799/2000000000 : ℝ)|^4783 ≤ (887219105961/2000000000000 : ℝ)^3759
        have hw : |(1055856799/2000000000 : ℝ)|=(1055856799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1091093199/2000000000 : ℝ)|^4783 ≤ (46253165583191/100000000000000 : ℝ)^3759
        have hw : |(1091093199/2000000000 : ℝ)|=(1091093199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-389403113/2500000000 : ℝ)|^4783 ≤ (9385879107523/100000000000000 : ℝ)^3759
        have hw : |(-389403113/2500000000 : ℝ)|=(389403113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1616_s5_5 (p : ℝ) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051951619/2500000000 : ℝ)*x 0 + (45550657/100000000 : ℝ)*x 1 + (3881457539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051951619/2500000000 : ℝ)^4783 ≤ (16619337592431/50000000000000 : ℝ)^3759 := by
    have hnat : (1051951619 : ℕ)^4783*50000000000000^3759 ≤ 16619337592431^3759*2500000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051951619 2500000000 16619337592431 50000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45550657/100000000 : ℝ)^4783 ≤ (36767507498711/100000000000000 : ℝ)^3759 := by
    have hnat : (45550657 : ℕ)^4783*100000000000000^3759 ≤ 36767507498711^3759*100000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45550657 100000000 36767507498711 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3881457539/10000000000 : ℝ)^4783 ≤ (29993817309323/100000000000000 : ℝ)^3759 := by
    have hnat : (3881457539 : ℕ)^4783*100000000000000^3759 ≤ 29993817309323^3759*10000000000^4783 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3881457539 10000000000 29993817309323 100000000000000 4783 3759 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4783/1024 : ℝ)) 4783 3759 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051951619/2500000000 : ℝ), (45550657/100000000 : ℝ), (3881457539/10000000000 : ℝ)] ![(16619337592431/50000000000000 : ℝ), (36767507498711/100000000000000 : ℝ), (29993817309323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051951619/2500000000 : ℝ)|^4783 ≤ (16619337592431/50000000000000 : ℝ)^3759
        have hw : |(1051951619/2500000000 : ℝ)|=(1051951619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(45550657/100000000 : ℝ)|^4783 ≤ (36767507498711/100000000000000 : ℝ)^3759
        have hw : |(45550657/100000000 : ℝ)|=(45550657/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3881457539/10000000000 : ℝ)|^4783 ≤ (29993817309323/100000000000000 : ℝ)^3759
        have hw : |(3881457539/10000000000 : ℝ)|=(3881457539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1616_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43459581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16331/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5237/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5237/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1633/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16331/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5237/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16331/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5237/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16331/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5237/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16331/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5237/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16331/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5237/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16331/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5237/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (5237/50000 : ℝ) ^ (4779/1024 : ℝ) ≤ (2672224968082589/100000000000000000000 : ℝ) := by
    have hpowers : (5237/50000 : ℝ)^4779 ≤ (2672224968082589/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5237 : ℕ)^4779*100000000000000000000^1024 ≤ 2672224968082589^1024*50000^4779 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5237 50000 2672224968082589 100000000000000000000 4779 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5237/50000 : ℝ)) (X := (2672224968082589/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16331/100000 : ℝ) ^ (4779/1024 : ℝ) ≤ (21239133124427693/100000000000000000000 : ℝ) := by
    have hpowers : (16331/100000 : ℝ)^4779 ≤ (21239133124427693/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16331 : ℕ)^4779*100000000000000000000^1024 ≤ 21239133124427693^1024*100000^4779 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16331 100000 21239133124427693 100000000000000000000 4779 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16331/100000 : ℝ)) (X := (21239133124427693/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002672224968082589/50000000000000000000 : ℝ) ≤ (5000057256767427/5000000000000000 : ℝ) ^ (4779/1024 : ℝ) := by
    have hpowers : (50002672224968082589/50000000000000000000 : ℝ)^1024 ≤ (5000057256767427/5000000000000000 : ℝ)^4779 := by
      have hnat : (50002672224968082589 : ℕ)^1024*5000000000000000^4779 ≤ 5000057256767427^4779*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002672224968082589 50000000000000000000 5000057256767427 5000000000000000 1024 4779 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000057256767427/5000000000000000 : ℝ)) (X := (50002672224968082589/50000000000000000000 : ℝ)) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50011955679046255141/50000000000000000000 : ℝ) ≤ (2500128075595781/2500000000000000 : ℝ) ^ (4779/1024 : ℝ) := by
    have hpowers : (50011955679046255141/50000000000000000000 : ℝ)^1024 ≤ (2500128075595781/2500000000000000 : ℝ)^4779 := by
      have hnat : (50011955679046255141 : ℕ)^1024*2500000000000000^4779 ≤ 2500128075595781^4779*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50011955679046255141 50000000000000000000 2500128075595781 2500000000000000 1024 4779 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500128075595781/2500000000000000 : ℝ)) (X := (50011955679046255141/50000000000000000000 : ℝ)) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021239133124427693/50000000000000000000 : ℝ) ≤ (5000455045615697/5000000000000000 : ℝ) ^ (4779/1024 : ℝ) := by
    have hpowers : (50021239133124427693/50000000000000000000 : ℝ)^1024 ≤ (5000455045615697/5000000000000000 : ℝ)^4779 := by
      have hnat : (50021239133124427693 : ℕ)^1024*5000000000000000^4779 ≤ 5000455045615697^4779*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021239133124427693 50000000000000000000 5000455045615697 5000000000000000 1024 4779 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000455045615697/5000000000000000 : ℝ)) (X := (50021239133124427693/50000000000000000000 : ℝ)) (by norm_num) 4779 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2672224968082589/100000000000000000000 : ℝ) ≤ ((29281168912490039959/29285000000000000000 : ℝ)+2*(39778884827/58570000000000 : ℝ)*(5237/50000 : ℝ))^(4779/1024 : ℝ) := by
    rw [show (29281168912490039959/29285000000000000000 : ℝ)+2*(39778884827/58570000000000 : ℝ)*(5237/50000 : ℝ)=(5000057256767427/5000000000000000 : ℝ) by norm_num, show 1+2*(2672224968082589/100000000000000000000 : ℝ)=(50002672224968082589/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21239133124427693/100000000000000000000 : ℝ)+(2672224968082589/100000000000000000000 : ℝ) ≤ ((29281168912490039959/29285000000000000000 : ℝ)+(39778884827/58570000000000 : ℝ)*((16331/100000 : ℝ)+(5237/50000 : ℝ)))^(4779/1024 : ℝ) := by
    rw [show (29281168912490039959/29285000000000000000 : ℝ)+(39778884827/58570000000000 : ℝ)*((16331/100000 : ℝ)+(5237/50000 : ℝ))=(2500128075595781/2500000000000000 : ℝ) by norm_num, show 1+(21239133124427693/100000000000000000000 : ℝ)+(2672224968082589/100000000000000000000 : ℝ)=(50011955679046255141/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21239133124427693/100000000000000000000 : ℝ) ≤ ((29281168912490039959/29285000000000000000 : ℝ)+2*(39778884827/58570000000000 : ℝ)*(16331/100000 : ℝ))^(4779/1024 : ℝ) := by
    rw [show (29281168912490039959/29285000000000000000 : ℝ)+2*(39778884827/58570000000000 : ℝ)*(16331/100000 : ℝ)=(5000455045615697/5000000000000000 : ℝ) by norm_num, show 1+2*(21239133124427693/100000000000000000000 : ℝ)=(50021239133124427693/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29281168912490039959/29285000000000000000 : ℝ)*(X 1 0+X 2 0)+(39778884827/58570000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4779/1024 : ℝ)) (lo := (5237/50000 : ℝ)) (hi := (16331/100000 : ℝ)) (c := (29281168912490039959/29285000000000000000 : ℝ)) (alpha := (39778884827/58570000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29281168912490039959/29285000000000000000 : ℝ)*(X 0 1+X 2 1)+(39778884827/58570000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4779/1024 : ℝ)) (lo := (5237/50000 : ℝ)) (hi := (16331/100000 : ℝ)) (c := (29281168912490039959/29285000000000000000 : ℝ)) (alpha := (39778884827/58570000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29281168912490039959/29285000000000000000 : ℝ)*(X 0 2+X 1 2)+(39778884827/58570000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4779/1024 : ℝ)) (lo := (5237/50000 : ℝ)) (hi := (16331/100000 : ℝ)) (c := (29281168912490039959/29285000000000000000 : ℝ)) (alpha := (39778884827/58570000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5352690319/10000000000 : ℝ)*X 2 0+(5181435409/10000000000 : ℝ)*X 2 1+(-1831640613/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s5_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((841526901/2000000000 : ℝ)*X 0 0+(775262273/2000000000 : ℝ)*X 0 1+(228007949/500000000 : ℝ)*X 0 2+(841526901/2000000000 : ℝ)*X 1 0+(775262273/2000000000 : ℝ)*X 1 1+(228007949/500000000 : ℝ)*X 1 2+(841526901/2000000000 : ℝ)*X 2 0+(775262273/2000000000 : ℝ)*X 2 1+(228007949/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s5_1 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-67575051/400000000 : ℝ)*X 0 0+(2591747029/5000000000 : ℝ)*X 0 1+(5455461013/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s5_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5279286599/10000000000 : ℝ)*X 1 0+(-778807163/5000000000 : ℝ)*X 1 1+(2727731041/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s5_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((1055856799/2000000000 : ℝ)*X 2 0+(1091093199/2000000000 : ℝ)*X 2 1+(-389403113/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s5_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1051951619/2500000000 : ℝ)*X 0 0+(45550657/100000000 : ℝ)*X 0 1+(3881457539/10000000000 : ℝ)*X 0 2+(1051951619/2500000000 : ℝ)*X 1 0+(45550657/100000000 : ℝ)*X 1 1+(3881457539/10000000000 : ℝ)*X 1 2+(1051951619/2500000000 : ℝ)*X 2 0+(45550657/100000000 : ℝ)*X 2 1+(3881457539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1616_s5_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46478082065971659244074603/183031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (144597641/100000000000000 : ℝ)*(base8) + (28097899/10000000000000 : ℝ)*(base15) + (116967279/20000000000000 : ℝ)*(base29) + (124808439/50000000000000 : ℝ)*(upper2) + (138513807/25000000000000 : ℝ)*(lower4) + (161295403980603/6250000000000 : ℝ)*(major0) + (645181762131511/25000000000000 : ℝ)*(major1) + (645181762131511/25000000000000 : ℝ)*(major2) + (39020366463/100000000000000 : ℝ)*(sp0) + (9717713449/100000000000000 : ℝ)*(sp1) + (367689807095583/10000000000000 : ℝ)*(sp2) + (1838448674869043/50000000000000 : ℝ)*(sp3) + (3676858610350613/100000000000000 : ℝ)*(sp4) + (185568269415081/12500000000000 : ℝ)*(sp5) + (742277936517049/50000000000000 : ℝ)*(f.failure) + (57451534618023/1562500000000 : ℝ)*(f.sum) + (1564519089/374848000000000000000000 : ℝ)*base65 + (9177715276748423049/732125000000000000000000000000000 : ℝ)*base67 + (6555929193292298049/732125000000000000000000000000000 : ℝ)*base69 + (1566863796708696527/183031250000000000000000000000000 : ℝ)*base71 + (12821081218491/5857000000000000000000000000 : ℝ)*base73 + (2344260838164048049/732125000000000000000000000000000 : ℝ)*base75 + (135693095420240973/183031250000000000000000000000000 : ℝ)*base78 + (6420386950832673049/732125000000000000000000000000000 : ℝ)*base79 + (2891867427211/1171400000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (11396469/1250000000000000000000 : ℝ)*base89 + (1103531/1250000000000000000000 : ℝ)*base92 + (1103531/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1616_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43459581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16331/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5237/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5237/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1633/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1616_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1616_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43459581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16469/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (207/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5237/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1633/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1616_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1616_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1616_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4779/1024 : ℝ) ≤ p) (hpb : p ≤ (4783/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43459581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16469/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (207/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5237/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1633/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1616_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
