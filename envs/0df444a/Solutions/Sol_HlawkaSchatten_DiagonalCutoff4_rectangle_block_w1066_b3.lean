-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1066_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:07:17.592749+00:00
-- url     : https://prove2.me/submissions/e86755ae-0fe1-4582-bb01-2080bbb06587

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
theorem support_rectangle_w1066_s9_0 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2203771509/10000000000 : ℝ)*x 0 + (5394332893/10000000000 : ℝ)*x 1 + (263223739/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2203771509/10000000000 : ℝ)^8259 ≤ (13383937750323/100000000000000 : ℝ)^6211 := by
    have hnat : (2203771509 : ℕ)^8259*100000000000000^6211 ≤ 13383937750323^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203771509 10000000000 13383937750323 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394332893/10000000000 : ℝ)^8259 ≤ (11002403236969/25000000000000 : ℝ)^6211 := by
    have hnat : (5394332893 : ℕ)^8259*25000000000000^6211 ≤ 11002403236969^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394332893 10000000000 11002403236969 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263223739/500000000 : ℝ)^8259 ≤ (42606449290157/100000000000000 : ℝ)^6211 := by
    have hnat : (263223739 : ℕ)^8259*100000000000000^6211 ≤ 42606449290157^6211*500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263223739 500000000 42606449290157 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2203771509/10000000000 : ℝ), (5394332893/10000000000 : ℝ), (263223739/500000000 : ℝ)] ![(13383937750323/100000000000000 : ℝ), (11002403236969/25000000000000 : ℝ), (42606449290157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2203771509/10000000000 : ℝ)|^8259 ≤ (13383937750323/100000000000000 : ℝ)^6211
        have hw : |(-2203771509/10000000000 : ℝ)|=(2203771509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394332893/10000000000 : ℝ)|^8259 ≤ (11002403236969/25000000000000 : ℝ)^6211
        have hw : |(5394332893/10000000000 : ℝ)|=(5394332893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263223739/500000000 : ℝ)|^8259 ≤ (42606449290157/100000000000000 : ℝ)^6211
        have hw : |(263223739/500000000 : ℝ)|=(263223739/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s9_1 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267248629/500000000 : ℝ)*x 0 + (-2269656943/10000000000 : ℝ)*x 1 + (1316118769/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267248629/500000000 : ℝ)^8259 ≤ (2173746482247/5000000000000 : ℝ)^6211 := by
    have hnat : (267248629 : ℕ)^8259*5000000000000^6211 ≤ 2173746482247^6211*500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267248629 500000000 2173746482247 5000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2269656943/10000000000 : ℝ)^8259 ≤ (3479654465253/25000000000000 : ℝ)^6211 := by
    have hnat : (2269656943 : ℕ)^8259*25000000000000^6211 ≤ 3479654465253^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269656943 10000000000 3479654465253 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316118769/2500000000 : ℝ)^8259 ≤ (2130322623783/5000000000000 : ℝ)^6211 := by
    have hnat : (1316118769 : ℕ)^8259*5000000000000^6211 ≤ 2130322623783^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316118769 2500000000 2130322623783 5000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267248629/500000000 : ℝ), (-2269656943/10000000000 : ℝ), (1316118769/2500000000 : ℝ)] ![(2173746482247/5000000000000 : ℝ), (3479654465253/25000000000000 : ℝ), (2130322623783/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267248629/500000000 : ℝ)|^8259 ≤ (2173746482247/5000000000000 : ℝ)^6211
        have hw : |(267248629/500000000 : ℝ)|=(267248629/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2269656943/10000000000 : ℝ)|^8259 ≤ (3479654465253/25000000000000 : ℝ)^6211
        have hw : |(-2269656943/10000000000 : ℝ)|=(2269656943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316118769/2500000000 : ℝ)|^8259 ≤ (2130322623783/5000000000000 : ℝ)^6211
        have hw : |(1316118769/2500000000 : ℝ)|=(1316118769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s9_2 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336243213/2500000000 : ℝ)*x 0 + (2632237409/5000000000 : ℝ)*x 1 + (-567414231/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336243213/2500000000 : ℝ)^8259 ≤ (21737466293421/50000000000000 : ℝ)^6211 := by
    have hnat : (1336243213 : ℕ)^8259*50000000000000^6211 ≤ 21737466293421^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336243213 2500000000 21737466293421 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632237409/5000000000 : ℝ)^8259 ≤ (42606449699107/100000000000000 : ℝ)^6211 := by
    have hnat : (2632237409 : ℕ)^8259*100000000000000^6211 ≤ 42606449699107^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632237409 5000000000 42606449699107 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (567414231/2500000000 : ℝ)^8259 ≤ (556744708243/4000000000000 : ℝ)^6211 := by
    have hnat : (567414231 : ℕ)^8259*4000000000000^6211 ≤ 556744708243^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567414231 2500000000 556744708243 4000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336243213/2500000000 : ℝ), (2632237409/5000000000 : ℝ), (-567414231/2500000000 : ℝ)] ![(21737466293421/50000000000000 : ℝ), (42606449699107/100000000000000 : ℝ), (556744708243/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336243213/2500000000 : ℝ)|^8259 ≤ (21737466293421/50000000000000 : ℝ)^6211
        have hw : |(1336243213/2500000000 : ℝ)|=(1336243213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632237409/5000000000 : ℝ)|^8259 ≤ (42606449699107/100000000000000 : ℝ)^6211
        have hw : |(2632237409/5000000000 : ℝ)|=(2632237409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-567414231/2500000000 : ℝ)|^8259 ≤ (556744708243/4000000000000 : ℝ)^6211
        have hw : |(-567414231/2500000000 : ℝ)|=(567414231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s9_3 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187746767/5000000000 : ℝ)*x 0 + (265632279/625000000 : ℝ)*x 1 + (1759617/3906250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187746767/5000000000 : ℝ)^8259 ≤ (33316562025671/100000000000000 : ℝ)^6211 := by
    have hnat : (2187746767 : ℕ)^8259*100000000000000^6211 ≤ 33316562025671^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187746767 5000000000 33316562025671 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265632279/625000000 : ℝ)^8259 ≤ (32053143422777/100000000000000 : ℝ)^6211 := by
    have hnat : (265632279 : ℕ)^8259*100000000000000^6211 ≤ 32053143422777^6211*625000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265632279 625000000 32053143422777 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1759617/3906250 : ℝ)^8259 ≤ (4328786817351/12500000000000 : ℝ)^6211 := by
    have hnat : (1759617 : ℕ)^8259*12500000000000^6211 ≤ 4328786817351^6211*3906250^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759617 3906250 4328786817351 12500000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187746767/5000000000 : ℝ), (265632279/625000000 : ℝ), (1759617/3906250 : ℝ)] ![(33316562025671/100000000000000 : ℝ), (32053143422777/100000000000000 : ℝ), (4328786817351/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187746767/5000000000 : ℝ)|^8259 ≤ (33316562025671/100000000000000 : ℝ)^6211
        have hw : |(2187746767/5000000000 : ℝ)|=(2187746767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(265632279/625000000 : ℝ)|^8259 ≤ (32053143422777/100000000000000 : ℝ)^6211
        have hw : |(265632279/625000000 : ℝ)|=(265632279/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1759617/3906250 : ℝ)|^8259 ≤ (4328786817351/12500000000000 : ℝ)^6211
        have hw : |(1759617/3906250 : ℝ)|=(1759617/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s9_4 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2203776499/10000000000 : ℝ)*x 0 + (5264800079/10000000000 : ℝ)*x 1 + (1348501619/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2203776499/10000000000 : ℝ)^8259 ≤ (13383978048369/100000000000000 : ℝ)^6211 := by
    have hnat : (2203776499 : ℕ)^8259*100000000000000^6211 ≤ 13383978048369^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203776499 10000000000 13383978048369 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264800079/10000000000 : ℝ)^8259 ≤ (21304975069593/50000000000000 : ℝ)^6211 := by
    have hnat : (5264800079 : ℕ)^8259*50000000000000^6211 ≤ 21304975069593^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264800079 10000000000 21304975069593 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348501619/2500000000 : ℝ)^8259 ≤ (44006071799061/100000000000000 : ℝ)^6211 := by
    have hnat : (1348501619 : ℕ)^8259*100000000000000^6211 ≤ 44006071799061^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348501619 2500000000 44006071799061 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2203776499/10000000000 : ℝ), (5264800079/10000000000 : ℝ), (1348501619/2500000000 : ℝ)] ![(13383978048369/100000000000000 : ℝ), (21304975069593/50000000000000 : ℝ), (44006071799061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2203776499/10000000000 : ℝ)|^8259 ≤ (13383978048369/100000000000000 : ℝ)^6211
        have hw : |(-2203776499/10000000000 : ℝ)|=(2203776499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264800079/10000000000 : ℝ)|^8259 ≤ (21304975069593/50000000000000 : ℝ)^6211
        have hw : |(5264800079/10000000000 : ℝ)|=(5264800079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348501619/2500000000 : ℝ)|^8259 ≤ (44006071799061/100000000000000 : ℝ)^6211
        have hw : |(1348501619/2500000000 : ℝ)|=(1348501619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s9_5 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4375503317/10000000000 : ℝ)*x 0 + (4503982479/10000000000 : ℝ)*x 1 + (4250755931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375503317/10000000000 : ℝ)^8259 ≤ (2082291317469/6250000000000 : ℝ)^6211 := by
    have hnat : (4375503317 : ℕ)^8259*6250000000000^6211 ≤ 2082291317469^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375503317 10000000000 2082291317469 6250000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4503982479/10000000000 : ℝ)^8259 ≤ (6924756487147/20000000000000 : ℝ)^6211 := by
    have hnat : (4503982479 : ℕ)^8259*20000000000000^6211 ≤ 6924756487147^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503982479 10000000000 6924756487147 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4250755931/10000000000 : ℝ)^8259 ≤ (500930569891/1562500000000 : ℝ)^6211 := by
    have hnat : (4250755931 : ℕ)^8259*1562500000000^6211 ≤ 500930569891^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250755931 10000000000 500930569891 1562500000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375503317/10000000000 : ℝ), (4503982479/10000000000 : ℝ), (4250755931/10000000000 : ℝ)] ![(2082291317469/6250000000000 : ℝ), (6924756487147/20000000000000 : ℝ), (500930569891/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375503317/10000000000 : ℝ)|^8259 ≤ (2082291317469/6250000000000 : ℝ)^6211
        have hw : |(4375503317/10000000000 : ℝ)|=(4375503317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4503982479/10000000000 : ℝ)|^8259 ≤ (6924756487147/20000000000000 : ℝ)^6211
        have hw : |(4503982479/10000000000 : ℝ)|=(4503982479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4250755931/10000000000 : ℝ)|^8259 ≤ (500930569891/1562500000000 : ℝ)^6211
        have hw : |(4250755931/10000000000 : ℝ)|=(4250755931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1066_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14003/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11251/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2813/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14003/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14003/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11251/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14003/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11251/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14003/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11251/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14003/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11251/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14003/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11251/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14003/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11251/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11251/100000 : ℝ) ^ (4129/1024 : ℝ) ≤ (14934395564563731/100000000000000000000 : ℝ) := by
    have hpowers : (11251/100000 : ℝ)^4129 ≤ (14934395564563731/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11251 : ℕ)^4129*100000000000000000000^1024 ≤ 14934395564563731^1024*100000^4129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11251 100000 14934395564563731 100000000000000000000 4129 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11251/100000 : ℝ)) (X := (14934395564563731/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14003/100000 : ℝ) ^ (4129/1024 : ℝ) ≤ (18044298387263499/50000000000000000000 : ℝ) := by
    have hpowers : (14003/100000 : ℝ)^4129 ≤ (18044298387263499/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14003 : ℕ)^4129*50000000000000000000^1024 ≤ 18044298387263499^1024*100000^4129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14003 100000 18044298387263499 50000000000000000000 4129 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14003/100000 : ℝ)) (X := (18044298387263499/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014934395564563731/50000000000000000000 : ℝ) ≤ (2500185167157623/2500000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (50014934395564563731/50000000000000000000 : ℝ)^1024 ≤ (2500185167157623/2500000000000000 : ℝ)^4129 := by
      have hnat : (50014934395564563731 : ℕ)^1024*2500000000000000^4129 ≤ 2500185167157623^4129*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014934395564563731 50000000000000000000 2500185167157623 2500000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500185167157623/2500000000000000 : ℝ)) (X := (50014934395564563731/50000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051022992339090729/100000000000000000000 : ℝ) ≤ (10001265137410047/10000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (100051022992339090729/100000000000000000000 : ℝ)^1024 ≤ (10001265137410047/10000000000000000 : ℝ)^4129 := by
      have hnat : (100051022992339090729 : ℕ)^1024*10000000000000000^4129 ≤ 10001265137410047^4129*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051022992339090729 100000000000000000000 10001265137410047 10000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001265137410047/10000000000000000 : ℝ)) (X := (100051022992339090729/100000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018044298387263499/25000000000000000000 : ℝ) ≤ (5000894803094801/5000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (25018044298387263499/25000000000000000000 : ℝ)^1024 ≤ (5000894803094801/5000000000000000 : ℝ)^4129 := by
      have hnat : (25018044298387263499 : ℕ)^1024*5000000000000000^4129 ≤ 5000894803094801^4129*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018044298387263499 25000000000000000000 5000894803094801 5000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000894803094801/5000000000000000 : ℝ)) (X := (25018044298387263499/25000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14934395564563731/100000000000000000000 : ℝ) ≤ ((13755118361796783687/13760000000000000000 : ℝ)+2*(104893755911/55040000000000 : ℝ)*(11251/100000 : ℝ))^(4129/1024 : ℝ) := by
    rw [show (13755118361796783687/13760000000000000000 : ℝ)+2*(104893755911/55040000000000 : ℝ)*(11251/100000 : ℝ)=(2500185167157623/2500000000000000 : ℝ) by norm_num, show 1+2*(14934395564563731/100000000000000000000 : ℝ)=(50014934395564563731/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18044298387263499/50000000000000000000 : ℝ)+(14934395564563731/100000000000000000000 : ℝ) ≤ ((13755118361796783687/13760000000000000000 : ℝ)+(104893755911/55040000000000 : ℝ)*((14003/100000 : ℝ)+(11251/100000 : ℝ)))^(4129/1024 : ℝ) := by
    rw [show (13755118361796783687/13760000000000000000 : ℝ)+(104893755911/55040000000000 : ℝ)*((14003/100000 : ℝ)+(11251/100000 : ℝ))=(10001265137410047/10000000000000000 : ℝ) by norm_num, show 1+(18044298387263499/50000000000000000000 : ℝ)+(14934395564563731/100000000000000000000 : ℝ)=(100051022992339090729/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18044298387263499/50000000000000000000 : ℝ) ≤ ((13755118361796783687/13760000000000000000 : ℝ)+2*(104893755911/55040000000000 : ℝ)*(14003/100000 : ℝ))^(4129/1024 : ℝ) := by
    rw [show (13755118361796783687/13760000000000000000 : ℝ)+2*(104893755911/55040000000000 : ℝ)*(14003/100000 : ℝ)=(5000894803094801/5000000000000000 : ℝ) by norm_num, show 1+2*(18044298387263499/50000000000000000000 : ℝ)=(25018044298387263499/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13755118361796783687/13760000000000000000 : ℝ)*(X 1 0+X 2 0)+(104893755911/55040000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (11251/100000 : ℝ)) (hi := (14003/100000 : ℝ)) (c := (13755118361796783687/13760000000000000000 : ℝ)) (alpha := (104893755911/55040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13755118361796783687/13760000000000000000 : ℝ)*(X 0 1+X 2 1)+(104893755911/55040000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (11251/100000 : ℝ)) (hi := (14003/100000 : ℝ)) (c := (13755118361796783687/13760000000000000000 : ℝ)) (alpha := (104893755911/55040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13755118361796783687/13760000000000000000 : ℝ)*(X 0 2+X 1 2)+(104893755911/55040000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (11251/100000 : ℝ)) (hi := (14003/100000 : ℝ)) (c := (13755118361796783687/13760000000000000000 : ℝ)) (alpha := (104893755911/55040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2203771509/10000000000 : ℝ)*X 0 0+(5394332893/10000000000 : ℝ)*X 0 1+(263223739/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267248629/500000000 : ℝ)*X 1 0+(-2269656943/10000000000 : ℝ)*X 1 1+(1316118769/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336243213/2500000000 : ℝ)*X 2 0+(2632237409/5000000000 : ℝ)*X 2 1+(-567414231/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2187746767/5000000000 : ℝ)*X 0 0+(265632279/625000000 : ℝ)*X 0 1+(1759617/3906250 : ℝ)*X 0 2+(2187746767/5000000000 : ℝ)*X 1 0+(265632279/625000000 : ℝ)*X 1 1+(1759617/3906250 : ℝ)*X 1 2+(2187746767/5000000000 : ℝ)*X 2 0+(265632279/625000000 : ℝ)*X 2 1+(1759617/3906250 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2203776499/10000000000 : ℝ)*X 0 0+(5264800079/10000000000 : ℝ)*X 0 1+(1348501619/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4375503317/10000000000 : ℝ)*X 0 0+(4503982479/10000000000 : ℝ)*X 0 1+(4250755931/10000000000 : ℝ)*X 0 2+(4375503317/10000000000 : ℝ)*X 1 0+(4503982479/10000000000 : ℝ)*X 1 1+(4250755931/10000000000 : ℝ)*X 1 2+(4375503317/10000000000 : ℝ)*X 2 0+(4503982479/10000000000 : ℝ)*X 2 1+(4250755931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2856236727738770855199/550400000000000000000000000 : ℝ) := by norm_num
    linear_combination (931675099/100000000000000 : ℝ)*(base19) + (156813611/12500000000000 : ℝ)*(base23) + (9226903/25000000000000 : ℝ)*(lower2) + (33031489/25000000000000 : ℝ)*(upper3) + (92956137/50000000000000 : ℝ)*(upper5) + (5815020120911333/100000000000000 : ℝ)*(major0) + (5815020120911333/100000000000000 : ℝ)*(major1) + (5815020120911333/100000000000000 : ℝ)*(major2) + (7700746127269883/100000000000000 : ℝ)*(sp0) + (1925196663435737/25000000000000 : ℝ)*(sp1) + (7700786330909159/100000000000000 : ℝ)*(sp2) + (98230962194617/2500000000000 : ℝ)*(sp3) + (10364537041/25000000000000 : ℝ)*(sp4) + (559825619/4000000000000 : ℝ)*(sp5) + (1964626241712577/50000000000000 : ℝ)*(f.failure) + (7700787585418047/100000000000000 : ℝ)*(f.sum) + (2692988950461/2752000000000000000000000000 : ℝ)*base66 + (3897969474971425229/1376000000000000000000000000000000 : ℝ)*base68 + (11541024920955425229/1376000000000000000000000000000000 : ℝ)*base70 + (17752145224388574771/1376000000000000000000000000000000 : ℝ)*base71 + (47952775549/2752000000000000000000000000 : ℝ)*base74 + (25657479415300574771/1376000000000000000000000000000000 : ℝ)*base75 + (1371160200260574771/1376000000000000000000000000000000 : ℝ)*base77 + (3106757898683425229/1376000000000000000000000000000000 : ℝ)*base80 + (3379564719641/550400000000000000000000000 : ℝ)*base82 + (28480537/2500000000000000000000 : ℝ)*base90 + (28480537/2500000000000000000000 : ℝ)*base92 + (28480537/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1066_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14003/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11251/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2813/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14003/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1066_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1066_s10_0 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2203768021/10000000000 : ℝ)*x 0 + (674291139/1250000000 : ℝ)*x 1 + (658060151/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2203768021/10000000000 : ℝ)^8259 ≤ (13383909582087/100000000000000 : ℝ)^6211 := by
    have hnat : (2203768021 : ℕ)^8259*100000000000000^6211 ≤ 13383909582087^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203768021 10000000000 13383909582087 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674291139/1250000000 : ℝ)^8259 ≤ (44009571929131/100000000000000 : ℝ)^6211 := by
    have hnat : (674291139 : ℕ)^8259*100000000000000^6211 ≤ 44009571929131^6211*1250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674291139 1250000000 44009571929131 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658060151/1250000000 : ℝ)^8259 ≤ (42606518467231/100000000000000 : ℝ)^6211 := by
    have hnat : (658060151 : ℕ)^8259*100000000000000^6211 ≤ 42606518467231^6211*1250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658060151 1250000000 42606518467231 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2203768021/10000000000 : ℝ), (674291139/1250000000 : ℝ), (658060151/1250000000 : ℝ)] ![(13383909582087/100000000000000 : ℝ), (44009571929131/100000000000000 : ℝ), (42606518467231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2203768021/10000000000 : ℝ)|^8259 ≤ (13383909582087/100000000000000 : ℝ)^6211
        have hw : |(-2203768021/10000000000 : ℝ)|=(2203768021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674291139/1250000000 : ℝ)|^8259 ≤ (44009571929131/100000000000000 : ℝ)^6211
        have hw : |(674291139/1250000000 : ℝ)|=(674291139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658060151/1250000000 : ℝ)|^8259 ≤ (42606518467231/100000000000000 : ℝ)^6211
        have hw : |(658060151/1250000000 : ℝ)|=(658060151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s10_1 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334060767/625000000 : ℝ)*x 0 + (-2269649141/10000000000 : ℝ)*x 1 + (5264481297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334060767/625000000 : ℝ)^8259 ≤ (10868731578417/25000000000000 : ℝ)^6211 := by
    have hnat : (334060767 : ℕ)^8259*25000000000000^6211 ≤ 10868731578417^6211*625000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334060767 625000000 10868731578417 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2269649141/10000000000 : ℝ)^8259 ≤ (13918554238981/100000000000000 : ℝ)^6211 := by
    have hnat : (2269649141 : ℕ)^8259*100000000000000^6211 ≤ 13918554238981^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269649141 10000000000 13918554238981 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264481297/10000000000 : ℝ)^8259 ≤ (21303259712517/50000000000000 : ℝ)^6211 := by
    have hnat : (5264481297 : ℕ)^8259*50000000000000^6211 ≤ 21303259712517^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264481297 10000000000 21303259712517 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334060767/625000000 : ℝ), (-2269649141/10000000000 : ℝ), (5264481297/10000000000 : ℝ)] ![(10868731578417/25000000000000 : ℝ), (13918554238981/100000000000000 : ℝ), (21303259712517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334060767/625000000 : ℝ)|^8259 ≤ (10868731578417/25000000000000 : ℝ)^6211
        have hw : |(334060767/625000000 : ℝ)|=(334060767/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2269649141/10000000000 : ℝ)|^8259 ≤ (13918554238981/100000000000000 : ℝ)^6211
        have hw : |(-2269649141/10000000000 : ℝ)|=(2269649141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264481297/10000000000 : ℝ)|^8259 ≤ (21303259712517/50000000000000 : ℝ)^6211
        have hw : |(5264481297/10000000000 : ℝ)|=(5264481297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s10_2 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-137735623/625000000 : ℝ)*x 0 + (5264802007/10000000000 : ℝ)*x 1 + (215760377/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (137735623/625000000 : ℝ)^8259 ≤ (6691962652791/50000000000000 : ℝ)^6211 := by
    have hnat : (137735623 : ℕ)^8259*50000000000000^6211 ≤ 6691962652791^6211*625000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137735623 625000000 6691962652791 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264802007/10000000000 : ℝ)^8259 ≤ (5326246361053/12500000000000 : ℝ)^6211 := by
    have hnat : (5264802007 : ℕ)^8259*12500000000000^6211 ≤ 5326246361053^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264802007 10000000000 5326246361053 12500000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215760377/400000000 : ℝ)^8259 ≤ (44006103791097/100000000000000 : ℝ)^6211 := by
    have hnat : (215760377 : ℕ)^8259*100000000000000^6211 ≤ 44006103791097^6211*400000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215760377 400000000 44006103791097 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-137735623/625000000 : ℝ), (5264802007/10000000000 : ℝ), (215760377/400000000 : ℝ)] ![(6691962652791/50000000000000 : ℝ), (5326246361053/12500000000000 : ℝ), (44006103791097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-137735623/625000000 : ℝ)|^8259 ≤ (6691962652791/50000000000000 : ℝ)^6211
        have hw : |(-137735623/625000000 : ℝ)|=(137735623/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264802007/10000000000 : ℝ)|^8259 ≤ (5326246361053/12500000000000 : ℝ)^6211
        have hw : |(5264802007/10000000000 : ℝ)|=(5264802007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215760377/400000000 : ℝ)|^8259 ≤ (44006103791097/100000000000000 : ℝ)^6211
        have hw : |(215760377/400000000 : ℝ)|=(215760377/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s10_3 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312268907/10000000000 : ℝ)*x 0 + (-1070062647/5000000000 : ℝ)*x 1 + (84281277/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312268907/10000000000 : ℝ)^8259 ≤ (10780392499541/25000000000000 : ℝ)^6211 := by
    have hnat : (5312268907 : ℕ)^8259*25000000000000^6211 ≤ 10780392499541^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312268907 10000000000 10780392499541 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1070062647/5000000000 : ℝ)^8259 ≤ (1609051212209/12500000000000 : ℝ)^6211 := by
    have hnat : (1070062647 : ℕ)^8259*12500000000000^6211 ≤ 1609051212209^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070062647 5000000000 1609051212209 12500000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84281277/156250000 : ℝ)^8259 ≤ (44006020290701/100000000000000 : ℝ)^6211 := by
    have hnat : (84281277 : ℕ)^8259*100000000000000^6211 ≤ 44006020290701^6211*156250000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84281277 156250000 44006020290701 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312268907/10000000000 : ℝ), (-1070062647/5000000000 : ℝ), (84281277/156250000 : ℝ)] ![(10780392499541/25000000000000 : ℝ), (1609051212209/12500000000000 : ℝ), (44006020290701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312268907/10000000000 : ℝ)|^8259 ≤ (10780392499541/25000000000000 : ℝ)^6211
        have hw : |(5312268907/10000000000 : ℝ)|=(5312268907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1070062647/5000000000 : ℝ)|^8259 ≤ (1609051212209/12500000000000 : ℝ)^6211
        have hw : |(-1070062647/5000000000 : ℝ)|=(1070062647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84281277/156250000 : ℝ)|^8259 ≤ (44006020290701/100000000000000 : ℝ)^6211
        have hw : |(84281277/156250000 : ℝ)|=(84281277/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s10_4 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656132373/5000000000 : ℝ)*x 0 + (5394001167/10000000000 : ℝ)*x 1 + (-214013167/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656132373/5000000000 : ℝ)^8259 ≤ (43121525084539/100000000000000 : ℝ)^6211 := by
    have hnat : (2656132373 : ℕ)^8259*100000000000000^6211 ≤ 43121525084539^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656132373 5000000000 43121525084539 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394001167/10000000000 : ℝ)^8259 ≤ (44006014204731/100000000000000 : ℝ)^6211 := by
    have hnat : (5394001167 : ℕ)^8259*100000000000000^6211 ≤ 44006014204731^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394001167 10000000000 44006014204731 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (214013167/1000000000 : ℝ)^8259 ≤ (6436230346777/50000000000000 : ℝ)^6211 := by
    have hnat : (214013167 : ℕ)^8259*50000000000000^6211 ≤ 6436230346777^6211*1000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214013167 1000000000 6436230346777 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656132373/5000000000 : ℝ), (5394001167/10000000000 : ℝ), (-214013167/1000000000 : ℝ)] ![(43121525084539/100000000000000 : ℝ), (44006014204731/100000000000000 : ℝ), (6436230346777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656132373/5000000000 : ℝ)|^8259 ≤ (43121525084539/100000000000000 : ℝ)^6211
        have hw : |(2656132373/5000000000 : ℝ)|=(2656132373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394001167/10000000000 : ℝ)|^8259 ≤ (44006014204731/100000000000000 : ℝ)^6211
        have hw : |(5394001167/10000000000 : ℝ)|=(5394001167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-214013167/1000000000 : ℝ)|^8259 ≤ (6436230346777/50000000000000 : ℝ)^6211
        have hw : |(-214013167/1000000000 : ℝ)|=(214013167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s10_5 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4375511743/10000000000 : ℝ)*x 0 + (562996061/1250000000 : ℝ)*x 1 + (1062690421/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375511743/10000000000 : ℝ)^8259 ≤ (33316746393637/100000000000000 : ℝ)^6211 := by
    have hnat : (4375511743 : ℕ)^8259*100000000000000^6211 ≤ 33316746393637^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375511743 10000000000 33316746393637 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562996061/1250000000 : ℝ)^8259 ≤ (8655909854303/25000000000000 : ℝ)^6211 := by
    have hnat : (562996061 : ℕ)^8259*25000000000000^6211 ≤ 8655909854303^6211*1250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562996061 1250000000 8655909854303 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1062690421/2500000000 : ℝ)^8259 ≤ (32059614169827/100000000000000 : ℝ)^6211 := by
    have hnat : (1062690421 : ℕ)^8259*100000000000000^6211 ≤ 32059614169827^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062690421 2500000000 32059614169827 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375511743/10000000000 : ℝ), (562996061/1250000000 : ℝ), (1062690421/2500000000 : ℝ)] ![(33316746393637/100000000000000 : ℝ), (8655909854303/25000000000000 : ℝ), (32059614169827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375511743/10000000000 : ℝ)|^8259 ≤ (33316746393637/100000000000000 : ℝ)^6211
        have hw : |(4375511743/10000000000 : ℝ)|=(4375511743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(562996061/1250000000 : ℝ)|^8259 ≤ (8655909854303/25000000000000 : ℝ)^6211
        have hw : |(562996061/1250000000 : ℝ)|=(562996061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1062690421/2500000000 : ℝ)|^8259 ≤ (32059614169827/100000000000000 : ℝ)^6211
        have hw : |(1062690421/2500000000 : ℝ)|=(1062690421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1066_s10 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14003/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2813/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2813/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7001/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14003/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2813/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14003/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2813/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14003/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2813/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14003/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2813/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14003/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2813/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14003/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2813/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2813/25000 : ℝ) ^ (4129/1024 : ℝ) ≤ (7469874299111071/50000000000000000000 : ℝ) := by
    have hpowers : (2813/25000 : ℝ)^4129 ≤ (7469874299111071/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2813 : ℕ)^4129*50000000000000000000^1024 ≤ 7469874299111071^1024*25000^4129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2813 25000 7469874299111071 50000000000000000000 4129 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2813/25000 : ℝ)) (X := (7469874299111071/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14003/100000 : ℝ) ^ (4129/1024 : ℝ) ≤ (18044298387263499/50000000000000000000 : ℝ) := by
    have hpowers : (14003/100000 : ℝ)^4129 ≤ (18044298387263499/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14003 : ℕ)^4129*50000000000000000000^1024 ≤ 18044298387263499^1024*100000^4129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14003 100000 18044298387263499 50000000000000000000 4129 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14003/100000 : ℝ)) (X := (18044298387263499/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007469874299111071/25000000000000000000 : ℝ) ≤ (10000740934083403/10000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (25007469874299111071/25000000000000000000 : ℝ)^1024 ≤ (10000740934083403/10000000000000000 : ℝ)^4129 := by
      have hnat : (25007469874299111071 : ℕ)^1024*10000000000000000^4129 ≤ 10000740934083403^4129*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007469874299111071 25000000000000000000 10000740934083403 10000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000740934083403/10000000000000000 : ℝ)) (X := (25007469874299111071/25000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002551417268637457/5000000000000000000 : ℝ) ≤ (10001265270115401/10000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (5002551417268637457/5000000000000000000 : ℝ)^1024 ≤ (10001265270115401/10000000000000000 : ℝ)^4129 := by
      have hnat : (5002551417268637457 : ℕ)^1024*10000000000000000^4129 ≤ 10001265270115401^4129*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002551417268637457 5000000000000000000 10001265270115401 10000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001265270115401/10000000000000000 : ℝ)) (X := (5002551417268637457/5000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018044298387263499/25000000000000000000 : ℝ) ≤ (10001789606147399/10000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (25018044298387263499/25000000000000000000 : ℝ)^1024 ≤ (10001789606147399/10000000000000000 : ℝ)^4129 := by
      have hnat : (25018044298387263499 : ℕ)^1024*10000000000000000^4129 ≤ 10001789606147399^4129*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018044298387263499 25000000000000000000 10001789606147399 10000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001789606147399/10000000000000000 : ℝ)) (X := (25018044298387263499/25000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7469874299111071/50000000000000000000 : ℝ) ≤ ((27500238651599358661/27510000000000000000 : ℝ)+2*(262168015999/137550000000000 : ℝ)*(2813/25000 : ℝ))^(4129/1024 : ℝ) := by
    rw [show (27500238651599358661/27510000000000000000 : ℝ)+2*(262168015999/137550000000000 : ℝ)*(2813/25000 : ℝ)=(10000740934083403/10000000000000000 : ℝ) by norm_num, show 1+2*(7469874299111071/50000000000000000000 : ℝ)=(25007469874299111071/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18044298387263499/50000000000000000000 : ℝ)+(7469874299111071/50000000000000000000 : ℝ) ≤ ((27500238651599358661/27510000000000000000 : ℝ)+(262168015999/137550000000000 : ℝ)*((14003/100000 : ℝ)+(2813/25000 : ℝ)))^(4129/1024 : ℝ) := by
    rw [show (27500238651599358661/27510000000000000000 : ℝ)+(262168015999/137550000000000 : ℝ)*((14003/100000 : ℝ)+(2813/25000 : ℝ))=(10001265270115401/10000000000000000 : ℝ) by norm_num, show 1+(18044298387263499/50000000000000000000 : ℝ)+(7469874299111071/50000000000000000000 : ℝ)=(5002551417268637457/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18044298387263499/50000000000000000000 : ℝ) ≤ ((27500238651599358661/27510000000000000000 : ℝ)+2*(262168015999/137550000000000 : ℝ)*(14003/100000 : ℝ))^(4129/1024 : ℝ) := by
    rw [show (27500238651599358661/27510000000000000000 : ℝ)+2*(262168015999/137550000000000 : ℝ)*(14003/100000 : ℝ)=(10001789606147399/10000000000000000 : ℝ) by norm_num, show 1+2*(18044298387263499/50000000000000000000 : ℝ)=(25018044298387263499/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27500238651599358661/27510000000000000000 : ℝ)*(X 1 0+X 2 0)+(262168015999/137550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (2813/25000 : ℝ)) (hi := (14003/100000 : ℝ)) (c := (27500238651599358661/27510000000000000000 : ℝ)) (alpha := (262168015999/137550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27500238651599358661/27510000000000000000 : ℝ)*(X 0 1+X 2 1)+(262168015999/137550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (2813/25000 : ℝ)) (hi := (14003/100000 : ℝ)) (c := (27500238651599358661/27510000000000000000 : ℝ)) (alpha := (262168015999/137550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27500238651599358661/27510000000000000000 : ℝ)*(X 0 2+X 1 2)+(262168015999/137550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (2813/25000 : ℝ)) (hi := (14003/100000 : ℝ)) (c := (27500238651599358661/27510000000000000000 : ℝ)) (alpha := (262168015999/137550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2203768021/10000000000 : ℝ)*X 0 0+(674291139/1250000000 : ℝ)*X 0 1+(658060151/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s10_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334060767/625000000 : ℝ)*X 1 0+(-2269649141/10000000000 : ℝ)*X 1 1+(5264481297/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s10_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-137735623/625000000 : ℝ)*X 0 0+(5264802007/10000000000 : ℝ)*X 0 1+(215760377/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s10_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5312268907/10000000000 : ℝ)*X 1 0+(-1070062647/5000000000 : ℝ)*X 1 1+(84281277/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s10_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((2656132373/5000000000 : ℝ)*X 2 0+(5394001167/10000000000 : ℝ)*X 2 1+(-214013167/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s10_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4375511743/10000000000 : ℝ)*X 0 0+(562996061/1250000000 : ℝ)*X 0 1+(1062690421/2500000000 : ℝ)*X 0 2+(4375511743/10000000000 : ℝ)*X 1 0+(562996061/1250000000 : ℝ)*X 1 1+(1062690421/2500000000 : ℝ)*X 1 2+(4375511743/10000000000 : ℝ)*X 2 0+(562996061/1250000000 : ℝ)*X 2 1+(1062690421/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s10_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (128910216929634372111860227/114625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2508967/10000000000000 : ℝ)*(base23) + (4340305783/100000000000000 : ℝ)*(upper1) + (204745267/20000000000000 : ℝ)*(lower2) + (361040829/50000000000000 : ℝ)*(upper3) + (2455189703/50000000000000 : ℝ)*(lower4) + (1461227113817131/25000000000000 : ℝ)*(major0) + (1461227113817131/25000000000000 : ℝ)*(major1) + (1461227113817131/25000000000000 : ℝ)*(major2) + (95036556517/25000000000000 : ℝ)*(sp0) + (199538301761/100000000000000 : ℝ)*(sp1) + (7739988472866709/100000000000000 : ℝ)*(sp2) + (3870084540395507/50000000000000 : ℝ)*(sp3) + (1548073718800621/20000000000000 : ℝ)*(sp4) + (987362063489183/25000000000000 : ℝ)*(sp5) + (987362063489183/25000000000000 : ℝ)*(f.failure) + (967546077386597/12500000000000 : ℝ)*(f.sum) + (8360405240659/1719375000000000000000000000 : ℝ)*base65 + (1709507391165857197/229250000000000000000000000000000 : ℝ)*base67 + (1982158688927357197/229250000000000000000000000000000 : ℝ)*base69 + (4122240127914107197/229250000000000000000000000000000 : ℝ)*base71 + (26347854584293/13755000000000000000000000000 : ℝ)*base74 + (3167593534032357197/229250000000000000000000000000000 : ℝ)*base75 + (3536491788444107197/229250000000000000000000000000000 : ℝ)*base77 + (4589060026502857197/229250000000000000000000000000000 : ℝ)*base79 + (17851124863381/6877500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (13846023/1250000000000000000000 : ℝ)*base90 + (13846023/1250000000000000000000 : ℝ)*base92 + (13846023/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1066_s10 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14003/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2813/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2813/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7001/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1066_s10 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1066_box_0 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1037157551/5000000000 : ℝ)*x 0 + (5377364959/10000000000 : ℝ)*x 1 + (1075473007/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037157551/5000000000 : ℝ)^8259 ≤ (1234874059403/10000000000000 : ℝ)^6211 := by
    have hnat : (1037157551 : ℕ)^8259*10000000000000^6211 ≤ 1234874059403^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037157551 5000000000 1234874059403 10000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377364959/10000000000 : ℝ)^8259 ≤ (43825629282137/100000000000000 : ℝ)^6211 := by
    have hnat : (5377364959 : ℕ)^8259*100000000000000^6211 ≤ 43825629282137^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377364959 10000000000 43825629282137 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075473007/2000000000 : ℝ)^8259 ≤ (21912815052889/50000000000000 : ℝ)^6211 := by
    have hnat : (1075473007 : ℕ)^8259*50000000000000^6211 ≤ 21912815052889^6211*2000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075473007 2000000000 21912815052889 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1037157551/5000000000 : ℝ), (5377364959/10000000000 : ℝ), (1075473007/2000000000 : ℝ)] ![(1234874059403/10000000000000 : ℝ), (43825629282137/100000000000000 : ℝ), (21912815052889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1037157551/5000000000 : ℝ)|^8259 ≤ (1234874059403/10000000000000 : ℝ)^6211
        have hw : |(-1037157551/5000000000 : ℝ)|=(1037157551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377364959/10000000000 : ℝ)|^8259 ≤ (43825629282137/100000000000000 : ℝ)^6211
        have hw : |(5377364959/10000000000 : ℝ)|=(5377364959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075473007/2000000000 : ℝ)|^8259 ≤ (21912815052889/50000000000000 : ℝ)^6211
        have hw : |(1075473007/2000000000 : ℝ)|=(1075473007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_box_1 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295203937/10000000000 : ℝ)*x 0 + (-2185539439/10000000000 : ℝ)*x 1 + (5251333/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295203937/10000000000 : ℝ)^8259 ≤ (536718364623/1250000000000 : ℝ)^6211 := by
    have hnat : (5295203937 : ℕ)^8259*1250000000000^6211 ≤ 536718364623^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295203937 10000000000 536718364623 1250000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2185539439/10000000000 : ℝ)^8259 ≤ (13236901172227/100000000000000 : ℝ)^6211 := by
    have hnat : (2185539439 : ℕ)^8259*100000000000000^6211 ≤ 13236901172227^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185539439 10000000000 13236901172227 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5251333/9765625 : ℝ)^8259 ≤ (43825629639771/100000000000000 : ℝ)^6211 := by
    have hnat : (5251333 : ℕ)^8259*100000000000000^6211 ≤ 43825629639771^6211*9765625^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251333 9765625 43825629639771 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295203937/10000000000 : ℝ), (-2185539439/10000000000 : ℝ), (5251333/9765625 : ℝ)] ![(536718364623/1250000000000 : ℝ), (13236901172227/100000000000000 : ℝ), (43825629639771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295203937/10000000000 : ℝ)|^8259 ≤ (536718364623/1250000000000 : ℝ)^6211
        have hw : |(5295203937/10000000000 : ℝ)|=(5295203937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2185539439/10000000000 : ℝ)|^8259 ≤ (13236901172227/100000000000000 : ℝ)^6211
        have hw : |(-2185539439/10000000000 : ℝ)|=(2185539439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5251333/9765625 : ℝ)|^8259 ≤ (43825629639771/100000000000000 : ℝ)^6211
        have hw : |(5251333/9765625 : ℝ)|=(5251333/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_box_2 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (165475123/312500000 : ℝ)*x 0 + (1075473001/2000000000 : ℝ)*x 1 + (-2185539423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165475123/312500000 : ℝ)^8259 ≤ (21468734579529/50000000000000 : ℝ)^6211 := by
    have hnat : (165475123 : ℕ)^8259*50000000000000^6211 ≤ 21468734579529^6211*312500000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165475123 312500000 21468734579529 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075473001/2000000000 : ℝ)^8259 ≤ (43825629780657/100000000000000 : ℝ)^6211 := by
    have hnat : (1075473001 : ℕ)^8259*100000000000000^6211 ≤ 43825629780657^6211*2000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075473001 2000000000 43825629780657 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2185539423/10000000000 : ℝ)^8259 ≤ (1654612630421/12500000000000 : ℝ)^6211 := by
    have hnat : (2185539423 : ℕ)^8259*12500000000000^6211 ≤ 1654612630421^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185539423 10000000000 1654612630421 12500000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165475123/312500000 : ℝ), (1075473001/2000000000 : ℝ), (-2185539423/10000000000 : ℝ)] ![(21468734579529/50000000000000 : ℝ), (43825629780657/100000000000000 : ℝ), (1654612630421/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165475123/312500000 : ℝ)|^8259 ≤ (21468734579529/50000000000000 : ℝ)^6211
        have hw : |(165475123/312500000 : ℝ)|=(165475123/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075473001/2000000000 : ℝ)|^8259 ≤ (43825629780657/100000000000000 : ℝ)^6211
        have hw : |(1075473001/2000000000 : ℝ)|=(1075473001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2185539423/10000000000 : ℝ)|^8259 ≤ (1654612630421/12500000000000 : ℝ)^6211
        have hw : |(-2185539423/10000000000 : ℝ)|=(2185539423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_box_3 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (14012113/31250000 : ℝ)*x 0 + (2161732229/5000000000 : ℝ)*x 1 + (4323464471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14012113/31250000 : ℝ)^8259 ≤ (34418403335073/100000000000000 : ℝ)^6211 := by
    have hnat : (14012113 : ℕ)^8259*100000000000000^6211 ≤ 34418403335073^6211*31250000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14012113 31250000 34418403335073 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2161732229/5000000000 : ℝ)^8259 ≤ (32790798257983/100000000000000 : ℝ)^6211 := by
    have hnat : (2161732229 : ℕ)^8259*100000000000000^6211 ≤ 32790798257983^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161732229 5000000000 32790798257983 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4323464471/10000000000 : ℝ)^8259 ≤ (32790798389091/100000000000000 : ℝ)^6211 := by
    have hnat : (4323464471 : ℕ)^8259*100000000000000^6211 ≤ 32790798389091^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323464471 10000000000 32790798389091 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(14012113/31250000 : ℝ), (2161732229/5000000000 : ℝ), (4323464471/10000000000 : ℝ)] ![(34418403335073/100000000000000 : ℝ), (32790798257983/100000000000000 : ℝ), (32790798389091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(14012113/31250000 : ℝ)|^8259 ≤ (34418403335073/100000000000000 : ℝ)^6211
        have hw : |(14012113/31250000 : ℝ)|=(14012113/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2161732229/5000000000 : ℝ)|^8259 ≤ (32790798257983/100000000000000 : ℝ)^6211
        have hw : |(2161732229/5000000000 : ℝ)|=(2161732229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4323464471/10000000000 : ℝ)|^8259 ≤ (32790798389091/100000000000000 : ℝ)^6211
        have hw : |(4323464471/10000000000 : ℝ)|=(4323464471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_box_4 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-583653711/2500000000 : ℝ)*x 0 + (5280091613/10000000000 : ℝ)*x 1 + (132002289/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (583653711/2500000000 : ℝ)^8259 ≤ (1445080619713/10000000000000 : ℝ)^6211 := by
    have hnat : (583653711 : ℕ)^8259*10000000000000^6211 ≤ 1445080619713^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583653711 2500000000 1445080619713 10000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280091613/10000000000 : ℝ)^8259 ≤ (427745971743/1000000000000 : ℝ)^6211 := by
    have hnat : (5280091613 : ℕ)^8259*1000000000000^6211 ≤ 427745971743^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280091613 10000000000 427745971743 1000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132002289/250000000 : ℝ)^8259 ≤ (8554919320673/20000000000000 : ℝ)^6211 := by
    have hnat : (132002289 : ℕ)^8259*20000000000000^6211 ≤ 8554919320673^6211*250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132002289 250000000 8554919320673 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-583653711/2500000000 : ℝ), (5280091613/10000000000 : ℝ), (132002289/250000000 : ℝ)] ![(1445080619713/10000000000000 : ℝ), (427745971743/1000000000000 : ℝ), (8554919320673/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-583653711/2500000000 : ℝ)|^8259 ≤ (1445080619713/10000000000000 : ℝ)^6211
        have hw : |(-583653711/2500000000 : ℝ)|=(583653711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280091613/10000000000 : ℝ)|^8259 ≤ (427745971743/1000000000000 : ℝ)^6211
        have hw : |(5280091613/10000000000 : ℝ)|=(5280091613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(132002289/250000000 : ℝ)|^8259 ≤ (8554919320673/20000000000000 : ℝ)^6211
        have hw : |(132002289/250000000 : ℝ)|=(132002289/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_box_5 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (335252889/625000000 : ℝ)*x 0 + (-2223569283/10000000000 : ℝ)*x 1 + (660011437/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335252889/625000000 : ℝ)^8259 ≤ (21840673984819/50000000000000 : ℝ)^6211 := by
    have hnat : (335252889 : ℕ)^8259*50000000000000^6211 ≤ 21840673984819^6211*625000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335252889 625000000 21840673984819 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2223569283/10000000000 : ℝ)^8259 ≤ (1354405610623/10000000000000 : ℝ)^6211 := by
    have hnat : (2223569283 : ℕ)^8259*10000000000000^6211 ≤ 1354405610623^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2223569283 10000000000 1354405610623 10000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660011437/1250000000 : ℝ)^8259 ≤ (8554919182787/20000000000000 : ℝ)^6211 := by
    have hnat : (660011437 : ℕ)^8259*20000000000000^6211 ≤ 8554919182787^6211*1250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660011437 1250000000 8554919182787 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335252889/625000000 : ℝ), (-2223569283/10000000000 : ℝ), (660011437/1250000000 : ℝ)] ![(21840673984819/50000000000000 : ℝ), (1354405610623/10000000000000 : ℝ), (8554919182787/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335252889/625000000 : ℝ)|^8259 ≤ (21840673984819/50000000000000 : ℝ)^6211
        have hw : |(335252889/625000000 : ℝ)|=(335252889/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2223569283/10000000000 : ℝ)|^8259 ≤ (1354405610623/10000000000000 : ℝ)^6211
        have hw : |(-2223569283/10000000000 : ℝ)|=(2223569283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(660011437/1250000000 : ℝ)|^8259 ≤ (8554919182787/20000000000000 : ℝ)^6211
        have hw : |(660011437/1250000000 : ℝ)|=(660011437/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_box_6 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5364045997/10000000000 : ℝ)*x 0 + (1056018371/2000000000 : ℝ)*x 1 + (-555892277/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364045997/10000000000 : ℝ)^8259 ≤ (21840672755781/50000000000000 : ℝ)^6211 := by
    have hnat : (5364045997 : ℕ)^8259*50000000000000^6211 ≤ 21840672755781^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364045997 10000000000 21840672755781 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056018371/2000000000 : ℝ)^8259 ≤ (5346824972651/12500000000000 : ℝ)^6211 := by
    have hnat : (1056018371 : ℕ)^8259*12500000000000^6211 ≤ 5346824972651^6211*2000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056018371 2000000000 5346824972651 12500000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (555892277/2500000000 : ℝ)^8259 ≤ (6772027344399/50000000000000 : ℝ)^6211 := by
    have hnat : (555892277 : ℕ)^8259*50000000000000^6211 ≤ 6772027344399^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555892277 2500000000 6772027344399 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364045997/10000000000 : ℝ), (1056018371/2000000000 : ℝ), (-555892277/2500000000 : ℝ)] ![(21840672755781/50000000000000 : ℝ), (5346824972651/12500000000000 : ℝ), (6772027344399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364045997/10000000000 : ℝ)|^8259 ≤ (21840672755781/50000000000000 : ℝ)^6211
        have hw : |(5364045997/10000000000 : ℝ)|=(5364045997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056018371/2000000000 : ℝ)|^8259 ≤ (5346824972651/12500000000000 : ℝ)^6211
        have hw : |(1056018371/2000000000 : ℝ)|=(1056018371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-555892277/2500000000 : ℝ)|^8259 ≤ (6772027344399/50000000000000 : ℝ)^6211
        have hw : |(-555892277/2500000000 : ℝ)|=(555892277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_box_7 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2133391193/5000000000 : ℝ)*x 0 + (4431989937/10000000000 : ℝ)*x 1 + (138499683/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133391193/5000000000 : ℝ)^8259 ≤ (805509637103/2500000000000 : ℝ)^6211 := by
    have hnat : (2133391193 : ℕ)^8259*2500000000000^6211 ≤ 805509637103^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133391193 5000000000 805509637103 2500000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4431989937/10000000000 : ℝ)^8259 ≤ (16944903831933/50000000000000 : ℝ)^6211 := by
    have hnat : (4431989937 : ℕ)^8259*50000000000000^6211 ≤ 16944903831933^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4431989937 10000000000 16944903831933 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (138499683/312500000 : ℝ)^8259 ≤ (33889806840257/100000000000000 : ℝ)^6211 := by
    have hnat : (138499683 : ℕ)^8259*100000000000000^6211 ≤ 33889806840257^6211*312500000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138499683 312500000 33889806840257 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2133391193/5000000000 : ℝ), (4431989937/10000000000 : ℝ), (138499683/312500000 : ℝ)] ![(805509637103/2500000000000 : ℝ), (16944903831933/50000000000000 : ℝ), (33889806840257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2133391193/5000000000 : ℝ)|^8259 ≤ (805509637103/2500000000000 : ℝ)^6211
        have hw : |(2133391193/5000000000 : ℝ)|=(2133391193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4431989937/10000000000 : ℝ)|^8259 ≤ (16944903831933/50000000000000 : ℝ)^6211
        have hw : |(4431989937/10000000000 : ℝ)|=(4431989937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(138499683/312500000 : ℝ)|^8259 ≤ (33889806840257/100000000000000 : ℝ)^6211
        have hw : |(138499683/312500000 : ℝ)|=(138499683/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_box_8 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2280274853/10000000000 : ℝ)*x 0 + (260704299/500000000 : ℝ)*x 1 + (1346741261/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2280274853/10000000000 : ℝ)^8259 ≤ (7002634607929/50000000000000 : ℝ)^6211 := by
    have hnat : (2280274853 : ℕ)^8259*50000000000000^6211 ≤ 7002634607929^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2280274853 10000000000 7002634607929 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260704299/500000000 : ℝ)^8259 ≤ (10516257757861/25000000000000 : ℝ)^6211 := by
    have hnat : (260704299 : ℕ)^8259*25000000000000^6211 ≤ 10516257757861^6211*500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260704299 500000000 10516257757861 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346741261/2500000000 : ℝ)^8259 ≤ (2745606233103/6250000000000 : ℝ)^6211 := by
    have hnat : (1346741261 : ℕ)^8259*6250000000000^6211 ≤ 2745606233103^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346741261 2500000000 2745606233103 6250000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2280274853/10000000000 : ℝ), (260704299/500000000 : ℝ), (1346741261/2500000000 : ℝ)] ![(7002634607929/50000000000000 : ℝ), (10516257757861/25000000000000 : ℝ), (2745606233103/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2280274853/10000000000 : ℝ)|^8259 ≤ (7002634607929/50000000000000 : ℝ)^6211
        have hw : |(-2280274853/10000000000 : ℝ)|=(2280274853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260704299/500000000 : ℝ)|^8259 ≤ (10516257757861/25000000000000 : ℝ)^6211
        have hw : |(260704299/500000000 : ℝ)|=(260704299/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346741261/2500000000 : ℝ)|^8259 ≤ (2745606233103/6250000000000 : ℝ)^6211
        have hw : |(1346741261/2500000000 : ℝ)|=(1346741261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_box_9 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (661050783/1250000000 : ℝ)*x 0 + (-2181714769/10000000000 : ℝ)*x 1 + (5386965419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661050783/1250000000 : ℝ)^8259 ≤ (4286418874077/10000000000000 : ℝ)^6211 := by
    have hnat : (661050783 : ℕ)^8259*10000000000000^6211 ≤ 4286418874077^6211*1250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661050783 1250000000 4286418874077 10000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2181714769/10000000000 : ℝ)^8259 ≤ (13206107448043/100000000000000 : ℝ)^6211 := by
    have hnat : (2181714769 : ℕ)^8259*100000000000000^6211 ≤ 13206107448043^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181714769 10000000000 13206107448043 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386965419/10000000000 : ℝ)^8259 ≤ (43929703796059/100000000000000 : ℝ)^6211 := by
    have hnat : (5386965419 : ℕ)^8259*100000000000000^6211 ≤ 43929703796059^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386965419 10000000000 43929703796059 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661050783/1250000000 : ℝ), (-2181714769/10000000000 : ℝ), (5386965419/10000000000 : ℝ)] ![(4286418874077/10000000000000 : ℝ), (13206107448043/100000000000000 : ℝ), (43929703796059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661050783/1250000000 : ℝ)|^8259 ≤ (4286418874077/10000000000000 : ℝ)^6211
        have hw : |(661050783/1250000000 : ℝ)|=(661050783/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2181714769/10000000000 : ℝ)|^8259 ≤ (13206107448043/100000000000000 : ℝ)^6211
        have hw : |(-2181714769/10000000000 : ℝ)|=(2181714769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386965419/10000000000 : ℝ)|^8259 ≤ (43929703796059/100000000000000 : ℝ)^6211
        have hw : |(5386965419/10000000000 : ℝ)|=(5386965419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_box_10 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288406151/10000000000 : ℝ)*x 0 + (5386964917/10000000000 : ℝ)*x 1 + (-2181715597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288406151/10000000000 : ℝ)^8259 ≤ (42864187522863/100000000000000 : ℝ)^6211 := by
    have hnat : (5288406151 : ℕ)^8259*100000000000000^6211 ≤ 42864187522863^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288406151 10000000000 42864187522863 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386964917/10000000000 : ℝ)^8259 ≤ (4392969835249/10000000000000 : ℝ)^6211 := by
    have hnat : (5386964917 : ℕ)^8259*10000000000000^6211 ≤ 4392969835249^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386964917 10000000000 4392969835249 10000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2181715597/10000000000 : ℝ)^8259 ≤ (3301528528157/25000000000000 : ℝ)^6211 := by
    have hnat : (2181715597 : ℕ)^8259*25000000000000^6211 ≤ 3301528528157^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181715597 10000000000 3301528528157 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288406151/10000000000 : ℝ), (5386964917/10000000000 : ℝ), (-2181715597/10000000000 : ℝ)] ![(42864187522863/100000000000000 : ℝ), (4392969835249/10000000000000 : ℝ), (3301528528157/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288406151/10000000000 : ℝ)|^8259 ≤ (42864187522863/100000000000000 : ℝ)^6211
        have hw : |(5288406151/10000000000 : ℝ)|=(5288406151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386964917/10000000000 : ℝ)|^8259 ≤ (4392969835249/10000000000000 : ℝ)^6211
        have hw : |(5386964917/10000000000 : ℝ)|=(5386964917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2181715597/10000000000 : ℝ)|^8259 ≤ (3301528528157/25000000000000 : ℝ)^6211
        have hw : |(-2181715597/10000000000 : ℝ)|=(2181715597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_box_11 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4505028903/10000000000 : ℝ)*x 0 + (862549507/2000000000 : ℝ)*x 1 + (2156373811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4505028903/10000000000 : ℝ)^8259 ≤ (34634479585609/100000000000000 : ℝ)^6211 := by
    have hnat : (4505028903 : ℕ)^8259*100000000000000^6211 ≤ 34634479585609^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505028903 10000000000 34634479585609 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (862549507/2000000000 : ℝ)^8259 ≤ (32682759763431/100000000000000 : ℝ)^6211 := by
    have hnat : (862549507 : ℕ)^8259*100000000000000^6211 ≤ 32682759763431^6211*2000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862549507 2000000000 32682759763431 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2156373811/5000000000 : ℝ)^8259 ≤ (32682760640129/100000000000000 : ℝ)^6211 := by
    have hnat : (2156373811 : ℕ)^8259*100000000000000^6211 ≤ 32682760640129^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156373811 5000000000 32682760640129 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4505028903/10000000000 : ℝ), (862549507/2000000000 : ℝ), (2156373811/5000000000 : ℝ)] ![(34634479585609/100000000000000 : ℝ), (32682759763431/100000000000000 : ℝ), (32682760640129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4505028903/10000000000 : ℝ)|^8259 ≤ (34634479585609/100000000000000 : ℝ)^6211
        have hw : |(4505028903/10000000000 : ℝ)|=(4505028903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(862549507/2000000000 : ℝ)|^8259 ≤ (32682759763431/100000000000000 : ℝ)^6211
        have hw : |(862549507/2000000000 : ℝ)|=(862549507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2156373811/5000000000 : ℝ)|^8259 ≤ (32682760640129/100000000000000 : ℝ)^6211
        have hw : |(2156373811/5000000000 : ℝ)|=(2156373811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_box_12 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1064511619/5000000000 : ℝ)*x 0 + (5442035019/10000000000 : ℝ)*x 1 + (5272091611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064511619/5000000000 : ℝ)^8259 ≤ (2556738084903/20000000000000 : ℝ)^6211 := by
    have hnat : (1064511619 : ℕ)^8259*20000000000000^6211 ≤ 2556738084903^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064511619 5000000000 2556738084903 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442035019/10000000000 : ℝ)^8259 ≤ (44527869671373/100000000000000 : ℝ)^6211 := by
    have hnat : (5442035019 : ℕ)^8259*100000000000000^6211 ≤ 44527869671373^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442035019 10000000000 44527869671373 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272091611/10000000000 : ℝ)^8259 ≤ (21344219948403/50000000000000 : ℝ)^6211 := by
    have hnat : (5272091611 : ℕ)^8259*50000000000000^6211 ≤ 21344219948403^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272091611 10000000000 21344219948403 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1064511619/5000000000 : ℝ), (5442035019/10000000000 : ℝ), (5272091611/10000000000 : ℝ)] ![(2556738084903/20000000000000 : ℝ), (44527869671373/100000000000000 : ℝ), (21344219948403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1064511619/5000000000 : ℝ)|^8259 ≤ (2556738084903/20000000000000 : ℝ)^6211
        have hw : |(-1064511619/5000000000 : ℝ)|=(1064511619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442035019/10000000000 : ℝ)|^8259 ≤ (44527869671373/100000000000000 : ℝ)^6211
        have hw : |(5442035019/10000000000 : ℝ)|=(5442035019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272091611/10000000000 : ℝ)|^8259 ≤ (21344219948403/50000000000000 : ℝ)^6211
        have hw : |(5272091611/10000000000 : ℝ)|=(5272091611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_box_13 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684852939/5000000000 : ℝ)*x 0 + (-1113319287/5000000000 : ℝ)*x 1 + (5272091047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684852939/5000000000 : ℝ)^8259 ≤ (5467830544319/12500000000000 : ℝ)^6211 := by
    have hnat : (2684852939 : ℕ)^8259*12500000000000^6211 ≤ 5467830544319^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684852939 5000000000 5467830544319 12500000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1113319287/5000000000 : ℝ)^8259 ≤ (6784460908397/50000000000000 : ℝ)^6211 := by
    have hnat : (1113319287 : ℕ)^8259*50000000000000^6211 ≤ 6784460908397^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113319287 5000000000 6784460908397 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272091047/10000000000 : ℝ)^8259 ≤ (42688433824239/100000000000000 : ℝ)^6211 := by
    have hnat : (5272091047 : ℕ)^8259*100000000000000^6211 ≤ 42688433824239^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272091047 10000000000 42688433824239 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684852939/5000000000 : ℝ), (-1113319287/5000000000 : ℝ), (5272091047/10000000000 : ℝ)] ![(5467830544319/12500000000000 : ℝ), (6784460908397/50000000000000 : ℝ), (42688433824239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684852939/5000000000 : ℝ)|^8259 ≤ (5467830544319/12500000000000 : ℝ)^6211
        have hw : |(2684852939/5000000000 : ℝ)|=(2684852939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1113319287/5000000000 : ℝ)|^8259 ≤ (6784460908397/50000000000000 : ℝ)^6211
        have hw : |(-1113319287/5000000000 : ℝ)|=(1113319287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272091047/10000000000 : ℝ)|^8259 ≤ (42688433824239/100000000000000 : ℝ)^6211
        have hw : |(5272091047/10000000000 : ℝ)|=(5272091047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_box_14 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (335606601/625000000 : ℝ)*x 0 + (5272091403/10000000000 : ℝ)*x 1 + (-2226638451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335606601/625000000 : ℝ)^8259 ≤ (43742641516491/100000000000000 : ℝ)^6211 := by
    have hnat : (335606601 : ℕ)^8259*100000000000000^6211 ≤ 43742641516491^6211*625000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335606601 625000000 43742641516491 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5272091403/10000000000 : ℝ)^8259 ≤ (21344218828639/50000000000000 : ℝ)^6211 := by
    have hnat : (5272091403 : ℕ)^8259*50000000000000^6211 ≤ 21344218828639^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272091403 10000000000 21344218828639 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2226638451/10000000000 : ℝ)^8259 ≤ (13568920820089/100000000000000 : ℝ)^6211 := by
    have hnat : (2226638451 : ℕ)^8259*100000000000000^6211 ≤ 13568920820089^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2226638451 10000000000 13568920820089 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335606601/625000000 : ℝ), (5272091403/10000000000 : ℝ), (-2226638451/10000000000 : ℝ)] ![(43742641516491/100000000000000 : ℝ), (21344218828639/50000000000000 : ℝ), (13568920820089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335606601/625000000 : ℝ)|^8259 ≤ (43742641516491/100000000000000 : ℝ)^6211
        have hw : |(335606601/625000000 : ℝ)|=(335606601/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5272091403/10000000000 : ℝ)|^8259 ≤ (21344218828639/50000000000000 : ℝ)^6211
        have hw : |(5272091403/10000000000 : ℝ)|=(5272091403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2226638451/10000000000 : ℝ)|^8259 ≤ (13568920820089/100000000000000 : ℝ)^6211
        have hw : |(-2226638451/10000000000 : ℝ)|=(2226638451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_box_15 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4248695443/10000000000 : ℝ)*x 0 + (2220455813/5000000000 : ℝ)*x 1 + (2220455773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4248695443/10000000000 : ℝ)^8259 ≤ (6407778701473/20000000000000 : ℝ)^6211 := by
    have hnat : (4248695443 : ℕ)^8259*20000000000000^6211 ≤ 6407778701473^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248695443 10000000000 6407778701473 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2220455813/5000000000 : ℝ)^8259 ≤ (16990276822687/50000000000000 : ℝ)^6211 := by
    have hnat : (2220455813 : ℕ)^8259*50000000000000^6211 ≤ 16990276822687^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220455813 5000000000 16990276822687 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2220455773/5000000000 : ℝ)^8259 ≤ (33980552831393/100000000000000 : ℝ)^6211 := by
    have hnat : (2220455773 : ℕ)^8259*100000000000000^6211 ≤ 33980552831393^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220455773 5000000000 33980552831393 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4248695443/10000000000 : ℝ), (2220455813/5000000000 : ℝ), (2220455773/5000000000 : ℝ)] ![(6407778701473/20000000000000 : ℝ), (16990276822687/50000000000000 : ℝ), (33980552831393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4248695443/10000000000 : ℝ)|^8259 ≤ (6407778701473/20000000000000 : ℝ)^6211
        have hw : |(4248695443/10000000000 : ℝ)|=(4248695443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2220455813/5000000000 : ℝ)|^8259 ≤ (16990276822687/50000000000000 : ℝ)^6211
        have hw : |(2220455813/5000000000 : ℝ)|=(2220455813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2220455773/5000000000 : ℝ)|^8259 ≤ (33980552831393/100000000000000 : ℝ)^6211
        have hw : |(2220455773/5000000000 : ℝ)|=(2220455773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1066_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7001/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2813/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(3889/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59241/100000 : ℝ) ∧ (19893/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10369/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7001/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2813/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7001/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2813/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7001/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2813/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7001/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2813/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7001/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2813/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7001/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2813/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2813/25000 : ℝ) ^ (4129/1024 : ℝ) ≤ (7469874299111071/50000000000000000000 : ℝ) := by
    have hpowers : (2813/25000 : ℝ)^4129 ≤ (7469874299111071/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2813 : ℕ)^4129*50000000000000000000^1024 ≤ 7469874299111071^1024*25000^4129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2813 25000 7469874299111071 50000000000000000000 4129 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2813/25000 : ℝ)) (X := (7469874299111071/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7001/50000 : ℝ) ^ (4129/1024 : ℝ) ≤ (36078206026542781/100000000000000000000 : ℝ) := by
    have hpowers : (7001/50000 : ℝ)^4129 ≤ (36078206026542781/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7001 : ℕ)^4129*100000000000000000000^1024 ≤ 36078206026542781^1024*50000^4129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7001 50000 36078206026542781 100000000000000000000 4129 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7001/50000 : ℝ)) (X := (36078206026542781/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007469874299111071/25000000000000000000 : ℝ) ≤ (10000740934083403/10000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (25007469874299111071/25000000000000000000 : ℝ)^1024 ≤ (10000740934083403/10000000000000000 : ℝ)^4129 := by
      have hnat : (25007469874299111071 : ℕ)^1024*10000000000000000^4129 ≤ 10000740934083403^4129*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007469874299111071 25000000000000000000 10000740934083403 10000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000740934083403/10000000000000000 : ℝ)) (X := (25007469874299111071/25000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051017954624764923/100000000000000000000 : ℝ) ≤ (10001265012521669/10000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (100051017954624764923/100000000000000000000 : ℝ)^1024 ≤ (10001265012521669/10000000000000000 : ℝ)^4129 := by
      have hnat : (100051017954624764923 : ℕ)^1024*10000000000000000^4129 ≤ 10001265012521669^4129*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051017954624764923 100000000000000000000 10001265012521669 10000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001265012521669/10000000000000000 : ℝ)) (X := (100051017954624764923/100000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036078206026542781/50000000000000000000 : ℝ) ≤ (2000357818191987/2000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (50036078206026542781/50000000000000000000 : ℝ)^1024 ≤ (2000357818191987/2000000000000000 : ℝ)^4129 := by
      have hnat : (50036078206026542781 : ℕ)^1024*2000000000000000^4129 ≤ 2000357818191987^4129*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036078206026542781 50000000000000000000 2000357818191987 2000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000357818191987/2000000000000000 : ℝ)) (X := (50036078206026542781/50000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7469874299111071/50000000000000000000 : ℝ) ≤ ((13745121853777310093/13750000000000000000 : ℝ)+2*(262039219133/137500000000000 : ℝ)*(2813/25000 : ℝ))^(4129/1024 : ℝ) := by
    rw [show (13745121853777310093/13750000000000000000 : ℝ)+2*(262039219133/137500000000000 : ℝ)*(2813/25000 : ℝ)=(10000740934083403/10000000000000000 : ℝ) by norm_num, show 1+2*(7469874299111071/50000000000000000000 : ℝ)=(25007469874299111071/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36078206026542781/100000000000000000000 : ℝ)+(7469874299111071/50000000000000000000 : ℝ) ≤ ((13745121853777310093/13750000000000000000 : ℝ)+(262039219133/137500000000000 : ℝ)*((7001/50000 : ℝ)+(2813/25000 : ℝ)))^(4129/1024 : ℝ) := by
    rw [show (13745121853777310093/13750000000000000000 : ℝ)+(262039219133/137500000000000 : ℝ)*((7001/50000 : ℝ)+(2813/25000 : ℝ))=(10001265012521669/10000000000000000 : ℝ) by norm_num, show 1+(36078206026542781/100000000000000000000 : ℝ)+(7469874299111071/50000000000000000000 : ℝ)=(100051017954624764923/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36078206026542781/100000000000000000000 : ℝ) ≤ ((13745121853777310093/13750000000000000000 : ℝ)+2*(262039219133/137500000000000 : ℝ)*(7001/50000 : ℝ))^(4129/1024 : ℝ) := by
    rw [show (13745121853777310093/13750000000000000000 : ℝ)+2*(262039219133/137500000000000 : ℝ)*(7001/50000 : ℝ)=(2000357818191987/2000000000000000 : ℝ) by norm_num, show 1+2*(36078206026542781/100000000000000000000 : ℝ)=(50036078206026542781/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13745121853777310093/13750000000000000000 : ℝ)*(X 1 0+X 2 0)+(262039219133/137500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (2813/25000 : ℝ)) (hi := (7001/50000 : ℝ)) (c := (13745121853777310093/13750000000000000000 : ℝ)) (alpha := (262039219133/137500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13745121853777310093/13750000000000000000 : ℝ)*(X 0 1+X 2 1)+(262039219133/137500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (2813/25000 : ℝ)) (hi := (7001/50000 : ℝ)) (c := (13745121853777310093/13750000000000000000 : ℝ)) (alpha := (262039219133/137500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13745121853777310093/13750000000000000000 : ℝ)*(X 0 2+X 1 2)+(262039219133/137500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (2813/25000 : ℝ)) (hi := (7001/50000 : ℝ)) (c := (13745121853777310093/13750000000000000000 : ℝ)) (alpha := (262039219133/137500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1037157551/5000000000 : ℝ)*X 0 0+(5377364959/10000000000 : ℝ)*X 0 1+(1075473007/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295203937/10000000000 : ℝ)*X 1 0+(-2185539439/10000000000 : ℝ)*X 1 1+(5251333/9765625 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((165475123/312500000 : ℝ)*X 2 0+(1075473001/2000000000 : ℝ)*X 2 1+(-2185539423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((14012113/31250000 : ℝ)*X 0 0+(2161732229/5000000000 : ℝ)*X 0 1+(4323464471/10000000000 : ℝ)*X 0 2+(14012113/31250000 : ℝ)*X 1 0+(2161732229/5000000000 : ℝ)*X 1 1+(4323464471/10000000000 : ℝ)*X 1 2+(14012113/31250000 : ℝ)*X 2 0+(2161732229/5000000000 : ℝ)*X 2 1+(4323464471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-583653711/2500000000 : ℝ)*X 0 0+(5280091613/10000000000 : ℝ)*X 0 1+(132002289/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((335252889/625000000 : ℝ)*X 1 0+(-2223569283/10000000000 : ℝ)*X 1 1+(660011437/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5364045997/10000000000 : ℝ)*X 2 0+(1056018371/2000000000 : ℝ)*X 2 1+(-555892277/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2133391193/5000000000 : ℝ)*X 0 0+(4431989937/10000000000 : ℝ)*X 0 1+(138499683/312500000 : ℝ)*X 0 2+(2133391193/5000000000 : ℝ)*X 1 0+(4431989937/10000000000 : ℝ)*X 1 1+(138499683/312500000 : ℝ)*X 1 2+(2133391193/5000000000 : ℝ)*X 2 0+(4431989937/10000000000 : ℝ)*X 2 1+(138499683/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2280274853/10000000000 : ℝ)*X 0 0+(260704299/500000000 : ℝ)*X 0 1+(1346741261/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((661050783/1250000000 : ℝ)*X 1 0+(-2181714769/10000000000 : ℝ)*X 1 1+(5386965419/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288406151/10000000000 : ℝ)*X 2 0+(5386964917/10000000000 : ℝ)*X 2 1+(-2181715597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4505028903/10000000000 : ℝ)*X 0 0+(862549507/2000000000 : ℝ)*X 0 1+(2156373811/5000000000 : ℝ)*X 0 2+(4505028903/10000000000 : ℝ)*X 1 0+(862549507/2000000000 : ℝ)*X 1 1+(2156373811/5000000000 : ℝ)*X 1 2+(4505028903/10000000000 : ℝ)*X 2 0+(862549507/2000000000 : ℝ)*X 2 1+(2156373811/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1064511619/5000000000 : ℝ)*X 0 0+(5442035019/10000000000 : ℝ)*X 0 1+(5272091611/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2684852939/5000000000 : ℝ)*X 1 0+(-1113319287/5000000000 : ℝ)*X 1 1+(5272091047/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((335606601/625000000 : ℝ)*X 2 0+(5272091403/10000000000 : ℝ)*X 2 1+(-2226638451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4248695443/10000000000 : ℝ)*X 0 0+(2220455813/5000000000 : ℝ)*X 0 1+(2220455773/5000000000 : ℝ)*X 0 2+(4248695443/10000000000 : ℝ)*X 1 0+(2220455813/5000000000 : ℝ)*X 1 1+(2220455773/5000000000 : ℝ)*X 1 2+(4248695443/10000000000 : ℝ)*X 2 0+(2220455813/5000000000 : ℝ)*X 2 1+(2220455773/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3889/6250 : ℝ) ≤ (-3888874538051073031301137781769/6250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7380669/50000000000000 : ℝ)*(upper0) + (31452643/50000000000000 : ℝ)*(upper1) + (53379537/100000000000000 : ℝ)*(upper5) + (771349202961579/20000000000000 : ℝ)*(major0) + (771349202961579/20000000000000 : ℝ)*(major1) + (771349202961579/20000000000000 : ℝ)*(major2) + (3843448601/100000000000000 : ℝ)*(sp1) + (1766491419/100000000000000 : ℝ)*(sp3) + (5128194321997029/100000000000000 : ℝ)*(sp4) + (5128196791748621/100000000000000 : ℝ)*(sp5) + (641005212564207/12500000000000 : ℝ)*(sp6) + (2606030292130079/100000000000000 : ℝ)*(sp7) + (3156600097/50000000000000 : ℝ)*(sp8) + (79467341783/50000000000000 : ℝ)*(sp14) + (1303016029310749/50000000000000 : ℝ)*(f.failure) + (2564100317598611/50000000000000 : ℝ)*(f.sum) + (3823297637/125000000000000000000000000 : ℝ)*base65 + (124121983718056077/25000000000000000000000000000000 : ℝ)*base67 + (198676714456943923/25000000000000000000000000000000 : ℝ)*base70 + (51939515106943923/25000000000000000000000000000000 : ℝ)*base72 + (1437274461619/62500000000000000000000000 : ℝ)*base74 + (105191950256943923/25000000000000000000000000000000 : ℝ)*base76 + (110418076281943923/25000000000000000000000000000000 : ℝ)*base78 + (538211943306943923/25000000000000000000000000000000 : ℝ)*base80 + (267449493869/62500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (20282731/2500000000000000000000 : ℝ)*base89 + (20282731/2500000000000000000000 : ℝ)*base91 + (20282731/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59241/100000 : ℝ) ≤ (4072979192397633085331577927/6875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5355497/25000000000000 : ℝ)*(upper1) + (19782611/100000000000000 : ℝ)*(upper2) + (4241727/100000000000000 : ℝ)*(upper3) + (4608343/50000000000000 : ℝ)*(upper4) + (2151627/5000000000000 : ℝ)*(upper5) + (3919654321943977/100000000000000 : ℝ)*(major0) + (3919654321943977/100000000000000 : ℝ)*(major1) + (3919654321943977/100000000000000 : ℝ)*(major2) + (5171021194853059/100000000000000 : ℝ)*(sp0) + (517101592932467/10000000000000 : ℝ)*(sp1) + (323187571682209/6250000000000 : ℝ)*(sp2) + (41383432361443/1562500000000 : ℝ)*(sp3) + (5265528389/100000000000000 : ℝ)*(sp9) + (5011984429/25000000000000 : ℝ)*(sp10) + (41383432361443/1562500000000 : ℝ)*(f.failure) + (5171021194853059/100000000000000 : ℝ)*(f.sum) + (11936999810691/6875000000000000000000000000 : ℝ)*base65 + (9473418661021759861/1375000000000000000000000000000000 : ℝ)*base67 + (2016016796478240139/1375000000000000000000000000000000 : ℝ)*base70 + (5769611398646759861/1375000000000000000000000000000000 : ℝ)*base71 + (11770048945033/3437500000000000000000000000 : ℝ)*base73 + (28878485074728240139/1375000000000000000000000000000000 : ℝ)*base76 + (305044304396759861/1375000000000000000000000000000000 : ℝ)*base77 + (15545650566603240139/1375000000000000000000000000000000 : ℝ)*base80 + (111746804430559/6875000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (214333/78125000000000000000 : ℝ)*base90 + (214333/78125000000000000000 : ℝ)*base92 + (214333/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (19893/25000 : ℝ) ≤ (24867123105181538130002749283991/31250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19269831/10000000000000 : ℝ)*(upper0) + (25326883/50000000000000 : ℝ)*(lower1) + (185413217/100000000000000 : ℝ)*(upper2) + (157239239/25000000000000 : ℝ)*(lower5) + (2193954556553419/50000000000000 : ℝ)*(major0) + (2193954556553419/50000000000000 : ℝ)*(major1) + (2193954556553419/50000000000000 : ℝ)*(major2) + (1712822109/50000000000000 : ℝ)*(sp0) + (35320927953/20000000000000 : ℝ)*(sp1) + (30258934303/20000000000000 : ℝ)*(sp3) + (5784346941937363/100000000000000 : ℝ)*(sp8) + (723021720367727/12500000000000 : ℝ)*(sp9) + (5784350367581581/100000000000000 : ℝ)*(sp10) + (370598954081047/12500000000000 : ℝ)*(sp11) + (296494292731989/10000000000000 : ℝ)*(f.failure) + (5784350367581581/100000000000000 : ℝ)*(f.sum) + (927682090189/625000000000000000000000000 : ℝ)*base65 + (155709212867722003/62500000000000000000000000000000 : ℝ)*base68 + (544257163305222003/62500000000000000000000000000000 : ℝ)*base70 + (362146045680222003/62500000000000000000000000000000 : ℝ)*base72 + (1350173566439/625000000000000000000000000 : ℝ)*base73 + (3148387819777997/62500000000000000000000000000000 : ℝ)*base75 + (446728047944777997/62500000000000000000000000000000 : ℝ)*base77 + (2196444586305222003/62500000000000000000000000000000 : ℝ)*base80 + (23964317907/312500000000000000000000000 : ℝ)*base81 + (4053709/500000000000000000000 : ℝ)*base90 + (4053709/500000000000000000000 : ℝ)*base92 + (4053709/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-10369/12500 : ℝ) ≤ (-10368740662065727548789790459503/12500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6126783/50000000000000 : ℝ)*(upper1) + (106965431/100000000000000 : ℝ)*(upper3) + (84083957/100000000000000 : ℝ)*(upper5) + (884502562496973/20000000000000 : ℝ)*(major0) + (884502562496973/20000000000000 : ℝ)*(major1) + (884502562496973/20000000000000 : ℝ)*(major2) + (38772741389/100000000000000 : ℝ)*(sp4) + (285988469999/50000000000000 : ℝ)*(sp5) + (29957700287/10000000000000 : ℝ)*(sp6) + (448166617649/100000000000000 : ℝ)*(sp7) + (5884311922148271/100000000000000 : ℝ)*(sp12) + (2941889358974831/50000000000000 : ℝ)*(sp13) + (5884051117886789/100000000000000 : ℝ)*(sp14) + (1493938369280623/50000000000000 : ℝ)*(sp15) + (1494162452589447/50000000000000 : ℝ)*(f.failure) + (294217534744483/5000000000000 : ℝ)*(f.sum) + (414626252159/1375000000000000000000000000 : ℝ)*base65 + (2797980748789251511/275000000000000000000000000000000 : ℝ)*base68 + (3663548620560748489/275000000000000000000000000000000 : ℝ)*base69 + (6080737304164251511/275000000000000000000000000000000 : ℝ)*base72 + (128514657527/171875000000000000000000000 : ℝ)*base74 + (19610770652785748489/275000000000000000000000000000000 : ℝ)*base75 + (3751635151314251511/275000000000000000000000000000000 : ℝ)*base78 + (1544977956814251511/275000000000000000000000000000000 : ℝ)*base80 + (303512012233/687500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (10865007/2500000000000000000000 : ℝ)*base90 + (10865007/2500000000000000000000 : ℝ)*base92 + (10865007/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1066_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7001/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2813/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59241/100000 : ℝ) else (19893/25000 : ℝ) ≤ X j i ∧ X j i ≤ (10369/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1066_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1066_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14003/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11251/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59241/100000 : ℝ) else (19893/25000 : ℝ) ≤ X j i ∧ X j i ≤ (10369/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1066_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1066_s10 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1066_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14003/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11251/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59241/100000 : ℝ) else (19893/25000 : ℝ) ≤ X j i ∧ X j i ≤ (10369/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1066_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
