-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1415_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:49:34.564786+00:00
-- url     : https://prove2.me/submissions/80dc8645-f31f-48b4-96af-3f3fb6e4fa37

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
theorem support_rectangle_w1415_s3_0 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-198140059/1000000000 : ℝ)*x 0 + (1354679799/2500000000 : ℝ)*x 1 + (5237560931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (198140059/1000000000 : ℝ)^4375 ≤ (7551283913/62500000000 : ℝ)^3351 := by
    have hnat : (198140059 : ℕ)^4375*62500000000^3351 ≤ 7551283913^3351*1000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198140059 1000000000 7551283913 62500000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354679799/2500000000 : ℝ)^4375 ≤ (11233644574833/25000000000000 : ℝ)^3351 := by
    have hnat : (1354679799 : ℕ)^4375*25000000000000^3351 ≤ 11233644574833^3351*2500000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354679799 2500000000 11233644574833 25000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5237560931/10000000000 : ℝ)^4375 ≤ (10745841854891/25000000000000 : ℝ)^3351 := by
    have hnat : (5237560931 : ℕ)^4375*25000000000000^3351 ≤ 10745841854891^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237560931 10000000000 10745841854891 25000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-198140059/1000000000 : ℝ), (1354679799/2500000000 : ℝ), (5237560931/10000000000 : ℝ)] ![(7551283913/62500000000 : ℝ), (11233644574833/25000000000000 : ℝ), (10745841854891/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-198140059/1000000000 : ℝ)|^4375 ≤ (7551283913/62500000000 : ℝ)^3351
        have hw : |(-198140059/1000000000 : ℝ)|=(198140059/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354679799/2500000000 : ℝ)|^4375 ≤ (11233644574833/25000000000000 : ℝ)^3351
        have hw : |(1354679799/2500000000 : ℝ)|=(1354679799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5237560931/10000000000 : ℝ)|^4375 ≤ (10745841854891/25000000000000 : ℝ)^3351
        have hw : |(5237560931/10000000000 : ℝ)|=(5237560931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s3_1 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337534363/2500000000 : ℝ)*x 0 + (-2073834107/10000000000 : ℝ)*x 1 + (5237560843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337534363/2500000000 : ℝ)^4375 ≤ (44193518837943/100000000000000 : ℝ)^3351 := by
    have hnat : (1337534363 : ℕ)^4375*100000000000000^3351 ≤ 44193518837943^3351*2500000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337534363 2500000000 44193518837943 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2073834107/10000000000 : ℝ)^4375 ≤ (6411557336749/50000000000000 : ℝ)^3351 := by
    have hnat : (2073834107 : ℕ)^4375*50000000000000^3351 ≤ 6411557336749^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073834107 10000000000 6411557336749 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5237560843/10000000000 : ℝ)^4375 ≤ (42983366476681/100000000000000 : ℝ)^3351 := by
    have hnat : (5237560843 : ℕ)^4375*100000000000000^3351 ≤ 42983366476681^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237560843 10000000000 42983366476681 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337534363/2500000000 : ℝ), (-2073834107/10000000000 : ℝ), (5237560843/10000000000 : ℝ)] ![(44193518837943/100000000000000 : ℝ), (6411557336749/50000000000000 : ℝ), (42983366476681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337534363/2500000000 : ℝ)|^4375 ≤ (44193518837943/100000000000000 : ℝ)^3351
        have hw : |(1337534363/2500000000 : ℝ)|=(1337534363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2073834107/10000000000 : ℝ)|^4375 ≤ (6411557336749/50000000000000 : ℝ)^3351
        have hw : |(-2073834107/10000000000 : ℝ)|=(2073834107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5237560843/10000000000 : ℝ)|^4375 ≤ (42983366476681/100000000000000 : ℝ)^3351
        have hw : |(5237560843/10000000000 : ℝ)|=(5237560843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s3_2 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350137389/10000000000 : ℝ)*x 0 + (1309390241/2500000000 : ℝ)*x 1 + (-207383403/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350137389/10000000000 : ℝ)^4375 ≤ (11048379539631/25000000000000 : ℝ)^3351 := by
    have hnat : (5350137389 : ℕ)^4375*25000000000000^3351 ≤ 11048379539631^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350137389 10000000000 11048379539631 25000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309390241/2500000000 : ℝ)^4375 ≤ (8596673554629/20000000000000 : ℝ)^3351 := by
    have hnat : (1309390241 : ℕ)^4375*20000000000000^3351 ≤ 8596673554629^3351*2500000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309390241 2500000000 8596673554629 20000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207383403/1000000000 : ℝ)^4375 ≤ (6411557025947/50000000000000 : ℝ)^3351 := by
    have hnat : (207383403 : ℕ)^4375*50000000000000^3351 ≤ 6411557025947^3351*1000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207383403 1000000000 6411557025947 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350137389/10000000000 : ℝ), (1309390241/2500000000 : ℝ), (-207383403/1000000000 : ℝ)] ![(11048379539631/25000000000000 : ℝ), (8596673554629/20000000000000 : ℝ), (6411557025947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350137389/10000000000 : ℝ)|^4375 ≤ (11048379539631/25000000000000 : ℝ)^3351
        have hw : |(5350137389/10000000000 : ℝ)|=(5350137389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1309390241/2500000000 : ℝ)|^4375 ≤ (8596673554629/20000000000000 : ℝ)^3351
        have hw : |(1309390241/2500000000 : ℝ)|=(1309390241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-207383403/1000000000 : ℝ)|^4375 ≤ (6411557025947/50000000000000 : ℝ)^3351
        have hw : |(-207383403/1000000000 : ℝ)|=(207383403/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s3_3 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (430718653/1000000000 : ℝ)*x 0 + (4116229267/10000000000 : ℝ)*x 1 + (2253062891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430718653/1000000000 : ℝ)^4375 ≤ (8324352040459/25000000000000 : ℝ)^3351 := by
    have hnat : (430718653 : ℕ)^4375*25000000000000^3351 ≤ 8324352040459^3351*1000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430718653 1000000000 8324352040459 25000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4116229267/10000000000 : ℝ)^4375 ≤ (7845817031479/25000000000000 : ℝ)^3351 := by
    have hnat : (4116229267 : ℕ)^4375*25000000000000^3351 ≤ 7845817031479^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4116229267 10000000000 7845817031479 25000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253062891/5000000000 : ℝ)^4375 ≤ (35319323705081/100000000000000 : ℝ)^3351 := by
    have hnat : (2253062891 : ℕ)^4375*100000000000000^3351 ≤ 35319323705081^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253062891 5000000000 35319323705081 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(430718653/1000000000 : ℝ), (4116229267/10000000000 : ℝ), (2253062891/5000000000 : ℝ)] ![(8324352040459/25000000000000 : ℝ), (7845817031479/25000000000000 : ℝ), (35319323705081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(430718653/1000000000 : ℝ)|^4375 ≤ (8324352040459/25000000000000 : ℝ)^3351
        have hw : |(430718653/1000000000 : ℝ)|=(430718653/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4116229267/10000000000 : ℝ)|^4375 ≤ (7845817031479/25000000000000 : ℝ)^3351
        have hw : |(4116229267/10000000000 : ℝ)|=(4116229267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2253062891/5000000000 : ℝ)|^4375 ≤ (35319323705081/100000000000000 : ℝ)^3351
        have hw : |(2253062891/5000000000 : ℝ)|=(2253062891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s3_4 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1981416409/10000000000 : ℝ)*x 0 + (1309572129/2500000000 : ℝ)*x 1 + (541798747/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1981416409/10000000000 : ℝ)^4375 ≤ (12082180197317/100000000000000 : ℝ)^3351 := by
    have hnat : (1981416409 : ℕ)^4375*100000000000000^3351 ≤ 12082180197317^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981416409 10000000000 12082180197317 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309572129/2500000000 : ℝ)^4375 ≤ (21495581674791/50000000000000 : ℝ)^3351 := by
    have hnat : (1309572129 : ℕ)^4375*50000000000000^3351 ≤ 21495581674791^3351*2500000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309572129 2500000000 21495581674791 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541798747/1000000000 : ℝ)^4375 ≤ (22463328219513/50000000000000 : ℝ)^3351 := by
    have hnat : (541798747 : ℕ)^4375*50000000000000^3351 ≤ 22463328219513^3351*1000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541798747 1000000000 22463328219513 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1981416409/10000000000 : ℝ), (1309572129/2500000000 : ℝ), (541798747/1000000000 : ℝ)] ![(12082180197317/100000000000000 : ℝ), (21495581674791/50000000000000 : ℝ), (22463328219513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1981416409/10000000000 : ℝ)|^4375 ≤ (12082180197317/100000000000000 : ℝ)^3351
        have hw : |(-1981416409/10000000000 : ℝ)|=(1981416409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1309572129/2500000000 : ℝ)|^4375 ≤ (21495581674791/50000000000000 : ℝ)^3351
        have hw : |(1309572129/2500000000 : ℝ)|=(1309572129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541798747/1000000000 : ℝ)|^4375 ≤ (22463328219513/50000000000000 : ℝ)^3351
        have hw : |(541798747/1000000000 : ℝ)|=(541798747/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s3_5 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303107179/10000000000 : ℝ)*x 0 + (-236675933/1250000000 : ℝ)*x 1 + (2708993739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303107179/10000000000 : ℝ)^4375 ≤ (5460875833167/12500000000000 : ℝ)^3351 := by
    have hnat : (5303107179 : ℕ)^4375*12500000000000^3351 ≤ 5460875833167^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303107179 10000000000 5460875833167 12500000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (236675933/1250000000 : ℝ)^4375 ≤ (5693168402451/50000000000000 : ℝ)^3351 := by
    have hnat : (236675933 : ℕ)^4375*50000000000000^3351 ≤ 5693168402451^3351*1250000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236675933 1250000000 5693168402451 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2708993739/5000000000 : ℝ)^4375 ≤ (22463328262817/50000000000000 : ℝ)^3351 := by
    have hnat : (2708993739 : ℕ)^4375*50000000000000^3351 ≤ 22463328262817^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708993739 5000000000 22463328262817 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303107179/10000000000 : ℝ), (-236675933/1250000000 : ℝ), (2708993739/5000000000 : ℝ)] ![(5460875833167/12500000000000 : ℝ), (5693168402451/50000000000000 : ℝ), (22463328262817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303107179/10000000000 : ℝ)|^4375 ≤ (5460875833167/12500000000000 : ℝ)^3351
        have hw : |(5303107179/10000000000 : ℝ)|=(5303107179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-236675933/1250000000 : ℝ)|^4375 ≤ (5693168402451/50000000000000 : ℝ)^3351
        have hw : |(-236675933/1250000000 : ℝ)|=(236675933/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2708993739/5000000000 : ℝ)|^4375 ≤ (22463328262817/50000000000000 : ℝ)^3351
        have hw : |(2708993739/5000000000 : ℝ)|=(2708993739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s3_6 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303107189/10000000000 : ℝ)*x 0 + (5417987453/10000000000 : ℝ)*x 1 + (-473351871/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303107189/10000000000 : ℝ)^4375 ≤ (4368700677289/10000000000000 : ℝ)^3351 := by
    have hnat : (5303107189 : ℕ)^4375*10000000000000^3351 ≤ 4368700677289^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303107189 10000000000 4368700677289 10000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417987453/10000000000 : ℝ)^4375 ≤ (44926656254983/100000000000000 : ℝ)^3351 := by
    have hnat : (5417987453 : ℕ)^4375*100000000000000^3351 ≤ 44926656254983^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417987453 10000000000 44926656254983 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (473351871/2500000000 : ℝ)^4375 ≤ (11386336961929/100000000000000 : ℝ)^3351 := by
    have hnat : (473351871 : ℕ)^4375*100000000000000^3351 ≤ 11386336961929^3351*2500000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473351871 2500000000 11386336961929 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303107189/10000000000 : ℝ), (5417987453/10000000000 : ℝ), (-473351871/2500000000 : ℝ)] ![(4368700677289/10000000000000 : ℝ), (44926656254983/100000000000000 : ℝ), (11386336961929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303107189/10000000000 : ℝ)|^4375 ≤ (4368700677289/10000000000000 : ℝ)^3351
        have hw : |(5303107189/10000000000 : ℝ)|=(5303107189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417987453/10000000000 : ℝ)|^4375 ≤ (44926656254983/100000000000000 : ℝ)^3351
        have hw : |(5417987453/10000000000 : ℝ)|=(5417987453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-473351871/2500000000 : ℝ)|^4375 ≤ (11386336961929/100000000000000 : ℝ)^3351
        have hw : |(-473351871/2500000000 : ℝ)|=(473351871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s3_7 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (861444151/2000000000 : ℝ)*x 0 + (4504559937/10000000000 : ℝ)*x 1 + (4117804139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (861444151/2000000000 : ℝ)^4375 ≤ (6659550719053/20000000000000 : ℝ)^3351 := by
    have hnat : (861444151 : ℕ)^4375*20000000000000^3351 ≤ 6659550719053^3351*2000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861444151 2000000000 6659550719053 20000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4504559937/10000000000 : ℝ)^4375 ≤ (8825825226309/25000000000000 : ℝ)^3351 := by
    have hnat : (4504559937 : ℕ)^4375*25000000000000^3351 ≤ 8825825226309^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504559937 10000000000 8825825226309 25000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4117804139/10000000000 : ℝ)^4375 ≤ (31398945484323/100000000000000 : ℝ)^3351 := by
    have hnat : (4117804139 : ℕ)^4375*100000000000000^3351 ≤ 31398945484323^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4117804139 10000000000 31398945484323 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(861444151/2000000000 : ℝ), (4504559937/10000000000 : ℝ), (4117804139/10000000000 : ℝ)] ![(6659550719053/20000000000000 : ℝ), (8825825226309/25000000000000 : ℝ), (31398945484323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(861444151/2000000000 : ℝ)|^4375 ≤ (6659550719053/20000000000000 : ℝ)^3351
        have hw : |(861444151/2000000000 : ℝ)|=(861444151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4504559937/10000000000 : ℝ)|^4375 ≤ (8825825226309/25000000000000 : ℝ)^3351
        have hw : |(4504559937/10000000000 : ℝ)|=(4504559937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4117804139/10000000000 : ℝ)|^4375 ≤ (31398945484323/100000000000000 : ℝ)^3351
        have hw : |(4117804139/10000000000 : ℝ)|=(4117804139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1415_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15843/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10291/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5559/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7477/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15843/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10291/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15843/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10291/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15843/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10291/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15843/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10291/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15843/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10291/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15843/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10291/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10291/100000 : ℝ) ^ (2187/512 : ℝ) ≤ (1512404581548853/25000000000000000000 : ℝ) := by
    have hpowers : (10291/100000 : ℝ)^2187 ≤ (1512404581548853/25000000000000000000 : ℝ)^512 := by
      have hnat : (10291 : ℕ)^2187*25000000000000000000^512 ≤ 1512404581548853^512*100000^2187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10291 100000 1512404581548853 25000000000000000000 2187 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10291/100000 : ℝ)) (X := (1512404581548853/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hpowhi : (15843/100000 : ℝ) ^ (2187/512 : ℝ) ≤ (19102405321496327/50000000000000000000 : ℝ) := by
    have hpowers : (15843/100000 : ℝ)^2187 ≤ (19102405321496327/50000000000000000000 : ℝ)^512 := by
      have hnat : (15843 : ℕ)^2187*50000000000000000000^512 ≤ 19102405321496327^512*100000^2187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15843 100000 19102405321496327 50000000000000000000 2187 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15843/100000 : ℝ)) (X := (19102405321496327/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501512404581548853/12500000000000000000 : ℝ) ≤ (62501770268107/62500000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (12501512404581548853/12500000000000000000 : ℝ)^512 ≤ (62501770268107/62500000000000 : ℝ)^2187 := by
      have hnat : (12501512404581548853 : ℕ)^512*62500000000000^2187 ≤ 62501770268107^2187*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501512404581548853 12500000000000000000 62501770268107 62500000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62501770268107/62500000000000 : ℝ)) (X := (12501512404581548853/12500000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022127214484594033/50000000000000000000 : ℝ) ≤ (10001035867797717/10000000000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (50022127214484594033/50000000000000000000 : ℝ)^512 ≤ (10001035867797717/10000000000000000 : ℝ)^2187 := by
      have hnat : (50022127214484594033 : ℕ)^512*10000000000000000^2187 ≤ 10001035867797717^2187*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022127214484594033 50000000000000000000 10001035867797717 10000000000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001035867797717/10000000000000000 : ℝ)) (X := (50022127214484594033/50000000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25019102405321496327/25000000000000000000 : ℝ) ≤ (5000894246349157/5000000000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (25019102405321496327/25000000000000000000 : ℝ)^512 ≤ (5000894246349157/5000000000000000 : ℝ)^2187 := by
      have hnat : (25019102405321496327 : ℕ)^512*5000000000000000^2187 ≤ 5000894246349157^2187*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019102405321496327 25000000000000000000 5000894246349157 5000000000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000894246349157/5000000000000000 : ℝ)) (X := (25019102405321496327/25000000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1512404581548853/25000000000000000000 : ℝ) ≤ ((27753041019430361393/27760000000000000000 : ℝ)+2*(752624900597/555200000000000 : ℝ)*(10291/100000 : ℝ))^(2187/512 : ℝ) := by
    rw [show (27753041019430361393/27760000000000000000 : ℝ)+2*(752624900597/555200000000000 : ℝ)*(10291/100000 : ℝ)=(62501770268107/62500000000000 : ℝ) by norm_num, show 1+2*(1512404581548853/25000000000000000000 : ℝ)=(12501512404581548853/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19102405321496327/50000000000000000000 : ℝ)+(1512404581548853/25000000000000000000 : ℝ) ≤ ((27753041019430361393/27760000000000000000 : ℝ)+(752624900597/555200000000000 : ℝ)*((15843/100000 : ℝ)+(10291/100000 : ℝ)))^(2187/512 : ℝ) := by
    rw [show (27753041019430361393/27760000000000000000 : ℝ)+(752624900597/555200000000000 : ℝ)*((15843/100000 : ℝ)+(10291/100000 : ℝ))=(10001035867797717/10000000000000000 : ℝ) by norm_num, show 1+(19102405321496327/50000000000000000000 : ℝ)+(1512404581548853/25000000000000000000 : ℝ)=(50022127214484594033/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19102405321496327/50000000000000000000 : ℝ) ≤ ((27753041019430361393/27760000000000000000 : ℝ)+2*(752624900597/555200000000000 : ℝ)*(15843/100000 : ℝ))^(2187/512 : ℝ) := by
    rw [show (27753041019430361393/27760000000000000000 : ℝ)+2*(752624900597/555200000000000 : ℝ)*(15843/100000 : ℝ)=(5000894246349157/5000000000000000 : ℝ) by norm_num, show 1+2*(19102405321496327/50000000000000000000 : ℝ)=(25019102405321496327/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27753041019430361393/27760000000000000000 : ℝ)*(X 1 0+X 2 0)+(752624900597/555200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (10291/100000 : ℝ)) (hi := (15843/100000 : ℝ)) (c := (27753041019430361393/27760000000000000000 : ℝ)) (alpha := (752624900597/555200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27753041019430361393/27760000000000000000 : ℝ)*(X 0 1+X 2 1)+(752624900597/555200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (10291/100000 : ℝ)) (hi := (15843/100000 : ℝ)) (c := (27753041019430361393/27760000000000000000 : ℝ)) (alpha := (752624900597/555200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27753041019430361393/27760000000000000000 : ℝ)*(X 0 2+X 1 2)+(752624900597/555200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (10291/100000 : ℝ)) (hi := (15843/100000 : ℝ)) (c := (27753041019430361393/27760000000000000000 : ℝ)) (alpha := (752624900597/555200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-198140059/1000000000 : ℝ)*X 0 0+(1354679799/2500000000 : ℝ)*X 0 1+(5237560931/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337534363/2500000000 : ℝ)*X 1 0+(-2073834107/10000000000 : ℝ)*X 1 1+(5237560843/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350137389/10000000000 : ℝ)*X 2 0+(1309390241/2500000000 : ℝ)*X 2 1+(-207383403/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((430718653/1000000000 : ℝ)*X 0 0+(4116229267/10000000000 : ℝ)*X 0 1+(2253062891/5000000000 : ℝ)*X 0 2+(430718653/1000000000 : ℝ)*X 1 0+(4116229267/10000000000 : ℝ)*X 1 1+(2253062891/5000000000 : ℝ)*X 1 2+(430718653/1000000000 : ℝ)*X 2 0+(4116229267/10000000000 : ℝ)*X 2 1+(2253062891/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1981416409/10000000000 : ℝ)*X 0 0+(1309572129/2500000000 : ℝ)*X 0 1+(541798747/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303107179/10000000000 : ℝ)*X 1 0+(-236675933/1250000000 : ℝ)*X 1 1+(2708993739/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303107189/10000000000 : ℝ)*X 2 0+(5417987453/10000000000 : ℝ)*X 2 1+(-473351871/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((861444151/2000000000 : ℝ)*X 0 0+(4504559937/10000000000 : ℝ)*X 0 1+(4117804139/10000000000 : ℝ)*X 0 2+(861444151/2000000000 : ℝ)*X 1 0+(4504559937/10000000000 : ℝ)*X 1 1+(4117804139/10000000000 : ℝ)*X 1 2+(861444151/2000000000 : ℝ)*X 2 0+(4504559937/10000000000 : ℝ)*X 2 1+(4117804139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2699842073691711743090509359/277600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (909174577/50000000000000 : ℝ)*(base19) + (174234271/10000000000000 : ℝ)*(base23) + (2943931/50000000000000 : ℝ)*(lower2) + (195413219/100000000000000 : ℝ)*(upper3) + (132132633/50000000000000 : ℝ)*(upper5) + (2021228970601053/50000000000000 : ℝ)*(major0) + (2021228970601053/50000000000000 : ℝ)*(major1) + (4042457941202107/100000000000000 : ℝ)*(major2) + (5520067286079753/100000000000000 : ℝ)*(sp0) + (5520099940907907/100000000000000 : ℝ)*(sp1) + (5520100016914351/100000000000000 : ℝ)*(sp2) + (51295978787233/2000000000000 : ℝ)*(sp3) + (8618294327/25000000000000 : ℝ)*(sp4) + (14859596963/100000000000000 : ℝ)*(sp7) + (1282406899479307/50000000000000 : ℝ)*(f.failure) + (5520101759257061/100000000000000 : ℝ)*(f.sum) + (202233403717799/55520000000000000000000000000 : ℝ)*base66 + (14510985889872678171/1388000000000000000000000000000000 : ℝ)*base68 + (20821112871767155051/2776000000000000000000000000000000 : ℝ)*base69 + (7054593165088678171/1388000000000000000000000000000000 : ℝ)*base72 + (152358539382521/55520000000000000000000000000 : ℝ)*base73 + (28380092032519155051/2776000000000000000000000000000000 : ℝ)*base75 + (9255534353703603171/1388000000000000000000000000000000 : ℝ)*base78 + (15685673569411603171/1388000000000000000000000000000000 : ℝ)*base80 + (70385844825881/13880000000000000000000000000 : ℝ)*base81 + (61466287/5000000000000000000000 : ℝ)*base89 + (61466287/5000000000000000000000 : ℝ)*base91 + (11466287/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (317153342824040443818439917/69400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (403972931/50000000000000 : ℝ)*(base19) + (106619991/12500000000000 : ℝ)*(base23) + (13117577/12500000000000 : ℝ)*(upper3) + (878209/5000000000000 : ℝ)*(lower4) + (100903333/100000000000000 : ℝ)*(upper5) + (407523661132777/10000000000000 : ℝ)*(major0) + (407523661132777/10000000000000 : ℝ)*(major1) + (407523661132777/10000000000000 : ℝ)*(major2) + (14948628823/100000000000000 : ℝ)*(sp1) + (15106507839/100000000000000 : ℝ)*(sp2) + (1780755911983/32000000000 : ℝ)*(sp4) + (556484646837219/10000000000000 : ℝ)*(sp5) + (1391211566369777/25000000000000 : ℝ)*(sp6) + (1292805422688779/50000000000000 : ℝ)*(sp7) + (1292805422688779/50000000000000 : ℝ)*(f.failure) + (1780755911983/32000000000 : ℝ)*(f.sum) + (8652932271829/2776000000000000000000000000 : ℝ)*base65 + (2372311481611528361/277600000000000000000000000000000 : ℝ)*base67 + (176719278950071639/277600000000000000000000000000000 : ℝ)*base70 + (334376053891528361/277600000000000000000000000000000 : ℝ)*base71 + (1550655056869/2776000000000000000000000000 : ℝ)*base73 + (327469400591528361/277600000000000000000000000000000 : ℝ)*base75 + (3774487201396328361/277600000000000000000000000000000 : ℝ)*base77 + (2355255398939528361/277600000000000000000000000000000 : ℝ)*base79 + (8243920997251/2776000000000000000000000000 : ℝ)*base82 + (65134161/5000000000000000000000 : ℝ)*base90 + (65134161/5000000000000000000000 : ℝ)*base92 + (65134161/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1415_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15843/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10291/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5559/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7477/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1415_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1415_s4_0 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-247796811/1250000000 : ℝ)*x 0 + (1082092163/2000000000 : ℝ)*x 1 + (5245178261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (247796811/1250000000 : ℝ)^4375 ≤ (2417961625061/20000000000000 : ℝ)^3351 := by
    have hnat : (247796811 : ℕ)^4375*20000000000000^3351 ≤ 2417961625061^3351*1250000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247796811 1250000000 2417961625061 20000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082092163/2000000000 : ℝ)^4375 ≤ (44845189852359/100000000000000 : ℝ)^3351 := by
    have hnat : (1082092163 : ℕ)^4375*100000000000000^3351 ≤ 44845189852359^3351*2000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082092163 2000000000 44845189852359 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245178261/10000000000 : ℝ)^4375 ≤ (21532501004283/50000000000000 : ℝ)^3351 := by
    have hnat : (5245178261 : ℕ)^4375*50000000000000^3351 ≤ 21532501004283^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245178261 10000000000 21532501004283 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-247796811/1250000000 : ℝ), (1082092163/2000000000 : ℝ), (5245178261/10000000000 : ℝ)] ![(2417961625061/20000000000000 : ℝ), (44845189852359/100000000000000 : ℝ), (21532501004283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-247796811/1250000000 : ℝ)|^4375 ≤ (2417961625061/20000000000000 : ℝ)^3351
        have hw : |(-247796811/1250000000 : ℝ)|=(247796811/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082092163/2000000000 : ℝ)|^4375 ≤ (44845189852359/100000000000000 : ℝ)^3351
        have hw : |(1082092163/2000000000 : ℝ)|=(1082092163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245178261/10000000000 : ℝ)|^4375 ≤ (21532501004283/50000000000000 : ℝ)^3351
        have hw : |(5245178261/10000000000 : ℝ)|=(5245178261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s4_1 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167125293/312500000 : ℝ)*x 0 + (-129160013/625000000 : ℝ)*x 1 + (5245178471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167125293/312500000 : ℝ)^4375 ≤ (22085285071061/50000000000000 : ℝ)^3351 := by
    have hnat : (167125293 : ℕ)^4375*50000000000000^3351 ≤ 22085285071061^3351*312500000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167125293 312500000 22085285071061 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129160013/625000000 : ℝ)^4375 ≤ (12764425577983/100000000000000 : ℝ)^3351 := by
    have hnat : (129160013 : ℕ)^4375*100000000000000^3351 ≤ 12764425577983^3351*625000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129160013 625000000 12764425577983 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245178471/10000000000 : ℝ)^4375 ≤ (21532502129813/50000000000000 : ℝ)^3351 := by
    have hnat : (5245178471 : ℕ)^4375*50000000000000^3351 ≤ 21532502129813^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245178471 10000000000 21532502129813 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167125293/312500000 : ℝ), (-129160013/625000000 : ℝ), (5245178471/10000000000 : ℝ)] ![(22085285071061/50000000000000 : ℝ), (12764425577983/100000000000000 : ℝ), (21532502129813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167125293/312500000 : ℝ)|^4375 ≤ (22085285071061/50000000000000 : ℝ)^3351
        have hw : |(167125293/312500000 : ℝ)|=(167125293/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-129160013/625000000 : ℝ)|^4375 ≤ (12764425577983/100000000000000 : ℝ)^3351
        have hw : |(-129160013/625000000 : ℝ)|=(129160013/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245178471/10000000000 : ℝ)|^4375 ≤ (21532502129813/50000000000000 : ℝ)^3351
        have hw : |(5245178471/10000000000 : ℝ)|=(5245178471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s4_2 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348010459/10000000000 : ℝ)*x 0 + (5245178249/10000000000 : ℝ)*x 1 + (-413311811/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348010459/10000000000 : ℝ)^4375 ≤ (22085290910121/50000000000000 : ℝ)^3351 := by
    have hnat : (5348010459 : ℕ)^4375*50000000000000^3351 ≤ 22085290910121^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348010459 10000000000 22085290910121 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245178249/10000000000 : ℝ)^4375 ≤ (21532500939967/50000000000000 : ℝ)^3351 := by
    have hnat : (5245178249 : ℕ)^4375*50000000000000^3351 ≤ 21532500939967^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245178249 10000000000 21532500939967 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413311811/2000000000 : ℝ)^4375 ≤ (1595552035007/12500000000000 : ℝ)^3351 := by
    have hnat : (413311811 : ℕ)^4375*12500000000000^3351 ≤ 1595552035007^3351*2000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413311811 2000000000 1595552035007 12500000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348010459/10000000000 : ℝ), (5245178249/10000000000 : ℝ), (-413311811/2000000000 : ℝ)] ![(22085290910121/50000000000000 : ℝ), (21532500939967/50000000000000 : ℝ), (1595552035007/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348010459/10000000000 : ℝ)|^4375 ≤ (22085290910121/50000000000000 : ℝ)^3351
        have hw : |(5348010459/10000000000 : ℝ)|=(5348010459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245178249/10000000000 : ℝ)|^4375 ≤ (21532500939967/50000000000000 : ℝ)^3351
        have hw : |(5245178249/10000000000 : ℝ)|=(5245178249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-413311811/2000000000 : ℝ)|^4375 ≤ (1595552035007/12500000000000 : ℝ)^3351
        have hw : |(-413311811/2000000000 : ℝ)|=(413311811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s4_3 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4307782699/10000000000 : ℝ)*x 0 + (1033310211/2500000000 : ℝ)*x 1 + (280560611/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307782699/10000000000 : ℝ)^4375 ≤ (33303425424269/100000000000000 : ℝ)^3351 := by
    have hnat : (4307782699 : ℕ)^4375*100000000000000^3351 ≤ 33303425424269^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307782699 10000000000 33303425424269 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033310211/2500000000 : ℝ)^4375 ≤ (15776354991723/50000000000000 : ℝ)^3351 := by
    have hnat : (1033310211 : ℕ)^4375*50000000000000^3351 ≤ 15776354991723^3351*2500000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033310211 2500000000 15776354991723 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280560611/625000000 : ℝ)^4375 ≤ (35143864581129/100000000000000 : ℝ)^3351 := by
    have hnat : (280560611 : ℕ)^4375*100000000000000^3351 ≤ 35143864581129^3351*625000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280560611 625000000 35143864581129 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307782699/10000000000 : ℝ), (1033310211/2500000000 : ℝ), (280560611/625000000 : ℝ)] ![(33303425424269/100000000000000 : ℝ), (15776354991723/50000000000000 : ℝ), (35143864581129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307782699/10000000000 : ℝ)|^4375 ≤ (33303425424269/100000000000000 : ℝ)^3351
        have hw : |(4307782699/10000000000 : ℝ)|=(4307782699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1033310211/2500000000 : ℝ)|^4375 ≤ (15776354991723/50000000000000 : ℝ)^3351
        have hw : |(1033310211/2500000000 : ℝ)|=(1033310211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(280560611/625000000 : ℝ)|^4375 ≤ (35143864581129/100000000000000 : ℝ)^3351
        have hw : |(280560611/625000000 : ℝ)|=(280560611/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s4_4 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-396477277/2000000000 : ℝ)*x 0 + (1311446063/2500000000 : ℝ)*x 1 + (5409851767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (396477277/2000000000 : ℝ)^4375 ≤ (6044951426307/50000000000000 : ℝ)^3351 := by
    have hnat : (396477277 : ℕ)^4375*50000000000000^3351 ≤ 6044951426307^3351*2000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396477277 2000000000 6044951426307 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311446063/2500000000 : ℝ)^4375 ≤ (43071497943841/100000000000000 : ℝ)^3351 := by
    have hnat : (1311446063 : ℕ)^4375*100000000000000^3351 ≤ 43071497943841^3351*2500000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311446063 2500000000 43071497943841 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409851767/10000000000 : ℝ)^4375 ≤ (1401206224579/3125000000000 : ℝ)^3351 := by
    have hnat : (5409851767 : ℕ)^4375*3125000000000^3351 ≤ 1401206224579^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409851767 10000000000 1401206224579 3125000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-396477277/2000000000 : ℝ), (1311446063/2500000000 : ℝ), (5409851767/10000000000 : ℝ)] ![(6044951426307/50000000000000 : ℝ), (43071497943841/100000000000000 : ℝ), (1401206224579/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-396477277/2000000000 : ℝ)|^4375 ≤ (6044951426307/50000000000000 : ℝ)^3351
        have hw : |(-396477277/2000000000 : ℝ)|=(396477277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311446063/2500000000 : ℝ)|^4375 ≤ (43071497943841/100000000000000 : ℝ)^3351
        have hw : |(1311446063/2500000000 : ℝ)|=(1311446063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409851767/10000000000 : ℝ)|^4375 ≤ (1401206224579/3125000000000 : ℝ)^3351
        have hw : |(5409851767/10000000000 : ℝ)|=(5409851767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s4_5 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652550421/5000000000 : ℝ)*x 0 + (-950943011/5000000000 : ℝ)*x 1 + (5409851767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652550421/5000000000 : ℝ)^4375 ≤ (43708450487943/100000000000000 : ℝ)^3351 := by
    have hnat : (2652550421 : ℕ)^4375*100000000000000^3351 ≤ 43708450487943^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652550421 5000000000 43708450487943 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (950943011/5000000000 : ℝ)^4375 ≤ (11452950311361/100000000000000 : ℝ)^3351 := by
    have hnat : (950943011 : ℕ)^4375*100000000000000^3351 ≤ 11452950311361^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      950943011 5000000000 11452950311361 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409851767/10000000000 : ℝ)^4375 ≤ (1401206224579/3125000000000 : ℝ)^3351 := by
    have hnat : (5409851767 : ℕ)^4375*3125000000000^3351 ≤ 1401206224579^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409851767 10000000000 1401206224579 3125000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652550421/5000000000 : ℝ), (-950943011/5000000000 : ℝ), (5409851767/10000000000 : ℝ)] ![(43708450487943/100000000000000 : ℝ), (11452950311361/100000000000000 : ℝ), (1401206224579/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652550421/5000000000 : ℝ)|^4375 ≤ (43708450487943/100000000000000 : ℝ)^3351
        have hw : |(2652550421/5000000000 : ℝ)|=(2652550421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-950943011/5000000000 : ℝ)|^4375 ≤ (11452950311361/100000000000000 : ℝ)^3351
        have hw : |(-950943011/5000000000 : ℝ)|=(950943011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409851767/10000000000 : ℝ)|^4375 ≤ (1401206224579/3125000000000 : ℝ)^3351
        have hw : |(5409851767/10000000000 : ℝ)|=(5409851767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s4_6 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652550421/5000000000 : ℝ)*x 0 + (5409851767/10000000000 : ℝ)*x 1 + (-950943011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652550421/5000000000 : ℝ)^4375 ≤ (43708450487943/100000000000000 : ℝ)^3351 := by
    have hnat : (2652550421 : ℕ)^4375*100000000000000^3351 ≤ 43708450487943^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652550421 5000000000 43708450487943 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409851767/10000000000 : ℝ)^4375 ≤ (1401206224579/3125000000000 : ℝ)^3351 := by
    have hnat : (5409851767 : ℕ)^4375*3125000000000^3351 ≤ 1401206224579^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409851767 10000000000 1401206224579 3125000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (950943011/5000000000 : ℝ)^4375 ≤ (11452950311361/100000000000000 : ℝ)^3351 := by
    have hnat : (950943011 : ℕ)^4375*100000000000000^3351 ≤ 11452950311361^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      950943011 5000000000 11452950311361 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652550421/5000000000 : ℝ), (5409851767/10000000000 : ℝ), (-950943011/5000000000 : ℝ)] ![(43708450487943/100000000000000 : ℝ), (1401206224579/3125000000000 : ℝ), (11452950311361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652550421/5000000000 : ℝ)|^4375 ≤ (43708450487943/100000000000000 : ℝ)^3351
        have hw : |(2652550421/5000000000 : ℝ)|=(2652550421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409851767/10000000000 : ℝ)|^4375 ≤ (1401206224579/3125000000000 : ℝ)^3351
        have hw : |(5409851767/10000000000 : ℝ)|=(5409851767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-950943011/5000000000 : ℝ)|^4375 ≤ (11452950311361/100000000000000 : ℝ)^3351
        have hw : |(-950943011/5000000000 : ℝ)|=(950943011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s4_7 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2153904287/5000000000 : ℝ)*x 0 + (35901323/80000000 : ℝ)*x 1 + (826910449/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153904287/5000000000 : ℝ)^4375 ≤ (4162960823999/12500000000000 : ℝ)^3351 := by
    have hnat : (2153904287 : ℕ)^4375*12500000000000^3351 ≤ 4162960823999^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153904287 5000000000 4162960823999 12500000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35901323/80000000 : ℝ)^4375 ≤ (35130532489043/100000000000000 : ℝ)^3351 := by
    have hnat : (35901323 : ℕ)^4375*100000000000000^3351 ≤ 35130532489043^3351*80000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35901323 80000000 35130532489043 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (826910449/2000000000 : ℝ)^4375 ≤ (31565780903091/100000000000000 : ℝ)^3351 := by
    have hnat : (826910449 : ℕ)^4375*100000000000000^3351 ≤ 31565780903091^3351*2000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826910449 2000000000 31565780903091 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2153904287/5000000000 : ℝ), (35901323/80000000 : ℝ), (826910449/2000000000 : ℝ)] ![(4162960823999/12500000000000 : ℝ), (35130532489043/100000000000000 : ℝ), (31565780903091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2153904287/5000000000 : ℝ)|^4375 ≤ (4162960823999/12500000000000 : ℝ)^3351
        have hw : |(2153904287/5000000000 : ℝ)|=(2153904287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(35901323/80000000 : ℝ)|^4375 ≤ (35130532489043/100000000000000 : ℝ)^3351
        have hw : |(35901323/80000000 : ℝ)|=(35901323/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(826910449/2000000000 : ℝ)|^4375 ≤ (31565780903091/100000000000000 : ℝ)^3351
        have hw : |(826910449/2000000000 : ℝ)|=(826910449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1415_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7477/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5559/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11281/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7391/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7477/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5559/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7477/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5559/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7477/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5559/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7477/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5559/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7477/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5559/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7477/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5559/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5559/50000 : ℝ) ^ (2187/512 : ℝ) ≤ (8416234457789593/100000000000000000000 : ℝ) := by
    have hpowers : (5559/50000 : ℝ)^2187 ≤ (8416234457789593/100000000000000000000 : ℝ)^512 := by
      have hnat : (5559 : ℕ)^2187*100000000000000000000^512 ≤ 8416234457789593^512*50000^2187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5559 50000 8416234457789593 100000000000000000000 2187 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5559/50000 : ℝ)) (X := (8416234457789593/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7477/50000 : ℝ) ^ (2187/512 : ℝ) ≤ (7463267981616199/25000000000000000000 : ℝ) := by
    have hpowers : (7477/50000 : ℝ)^2187 ≤ (7463267981616199/25000000000000000000 : ℝ)^512 := by
      have hnat : (7477 : ℕ)^2187*25000000000000000000^512 ≤ 7463267981616199^512*50000^2187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7477 50000 7463267981616199 25000000000000000000 2187 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7477/50000 : ℝ)) (X := (7463267981616199/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008416234457789593/50000000000000000000 : ℝ) ≤ (5000197020315897/5000000000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (50008416234457789593/50000000000000000000 : ℝ)^512 ≤ (5000197020315897/5000000000000000 : ℝ)^2187 := by
      have hnat : (50008416234457789593 : ℕ)^512*5000000000000000^2187 ≤ 5000197020315897^2187*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008416234457789593 50000000000000000000 5000197020315897 5000000000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000197020315897/5000000000000000 : ℝ)) (X := (50008416234457789593/50000000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038269306384254389/100000000000000000000 : ℝ) ≤ (10000895793965537/10000000000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (100038269306384254389/100000000000000000000 : ℝ)^512 ≤ (10000895793965537/10000000000000000 : ℝ)^2187 := by
      have hnat : (100038269306384254389 : ℕ)^512*10000000000000000^2187 ≤ 10000895793965537^2187*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038269306384254389 100000000000000000000 10000895793965537 10000000000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000895793965537/10000000000000000 : ℝ)) (X := (100038269306384254389/100000000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507463267981616199/12500000000000000000 : ℝ) ≤ (125017469341241/125000000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (12507463267981616199/12500000000000000000 : ℝ)^512 ≤ (125017469341241/125000000000000 : ℝ)^2187 := by
      have hnat : (12507463267981616199 : ℕ)^512*125000000000000^2187 ≤ 125017469341241^2187*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507463267981616199 12500000000000000000 125017469341241 125000000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125017469341241/125000000000000 : ℝ)) (X := (12507463267981616199/12500000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8416234457789593/100000000000000000000 : ℝ) ≤ ((9587588638183613109/9590000000000000000 : ℝ)+2*(501753333743/383600000000000 : ℝ)*(5559/50000 : ℝ))^(2187/512 : ℝ) := by
    rw [show (9587588638183613109/9590000000000000000 : ℝ)+2*(501753333743/383600000000000 : ℝ)*(5559/50000 : ℝ)=(5000197020315897/5000000000000000 : ℝ) by norm_num, show 1+2*(8416234457789593/100000000000000000000 : ℝ)=(50008416234457789593/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7463267981616199/25000000000000000000 : ℝ)+(8416234457789593/100000000000000000000 : ℝ) ≤ ((9587588638183613109/9590000000000000000 : ℝ)+(501753333743/383600000000000 : ℝ)*((7477/50000 : ℝ)+(5559/50000 : ℝ)))^(2187/512 : ℝ) := by
    rw [show (9587588638183613109/9590000000000000000 : ℝ)+(501753333743/383600000000000 : ℝ)*((7477/50000 : ℝ)+(5559/50000 : ℝ))=(10000895793965537/10000000000000000 : ℝ) by norm_num, show 1+(7463267981616199/25000000000000000000 : ℝ)+(8416234457789593/100000000000000000000 : ℝ)=(100038269306384254389/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7463267981616199/25000000000000000000 : ℝ) ≤ ((9587588638183613109/9590000000000000000 : ℝ)+2*(501753333743/383600000000000 : ℝ)*(7477/50000 : ℝ))^(2187/512 : ℝ) := by
    rw [show (9587588638183613109/9590000000000000000 : ℝ)+2*(501753333743/383600000000000 : ℝ)*(7477/50000 : ℝ)=(125017469341241/125000000000000 : ℝ) by norm_num, show 1+2*(7463267981616199/25000000000000000000 : ℝ)=(12507463267981616199/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9587588638183613109/9590000000000000000 : ℝ)*(X 1 0+X 2 0)+(501753333743/383600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (5559/50000 : ℝ)) (hi := (7477/50000 : ℝ)) (c := (9587588638183613109/9590000000000000000 : ℝ)) (alpha := (501753333743/383600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9587588638183613109/9590000000000000000 : ℝ)*(X 0 1+X 2 1)+(501753333743/383600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (5559/50000 : ℝ)) (hi := (7477/50000 : ℝ)) (c := (9587588638183613109/9590000000000000000 : ℝ)) (alpha := (501753333743/383600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9587588638183613109/9590000000000000000 : ℝ)*(X 0 2+X 1 2)+(501753333743/383600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (5559/50000 : ℝ)) (hi := (7477/50000 : ℝ)) (c := (9587588638183613109/9590000000000000000 : ℝ)) (alpha := (501753333743/383600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-247796811/1250000000 : ℝ)*X 0 0+(1082092163/2000000000 : ℝ)*X 0 1+(5245178261/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167125293/312500000 : ℝ)*X 1 0+(-129160013/625000000 : ℝ)*X 1 1+(5245178471/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348010459/10000000000 : ℝ)*X 2 0+(5245178249/10000000000 : ℝ)*X 2 1+(-413311811/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4307782699/10000000000 : ℝ)*X 0 0+(1033310211/2500000000 : ℝ)*X 0 1+(280560611/625000000 : ℝ)*X 0 2+(4307782699/10000000000 : ℝ)*X 1 0+(1033310211/2500000000 : ℝ)*X 1 1+(280560611/625000000 : ℝ)*X 1 2+(4307782699/10000000000 : ℝ)*X 2 0+(1033310211/2500000000 : ℝ)*X 2 1+(280560611/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-396477277/2000000000 : ℝ)*X 0 0+(1311446063/2500000000 : ℝ)*X 0 1+(5409851767/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652550421/5000000000 : ℝ)*X 1 0+(-950943011/5000000000 : ℝ)*X 1 1+(5409851767/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652550421/5000000000 : ℝ)*X 2 0+(5409851767/10000000000 : ℝ)*X 2 1+(-950943011/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2153904287/5000000000 : ℝ)*X 0 0+(35901323/80000000 : ℝ)*X 0 1+(826910449/2000000000 : ℝ)*X 0 2+(2153904287/5000000000 : ℝ)*X 1 0+(35901323/80000000 : ℝ)*X 1 1+(826910449/2000000000 : ℝ)*X 1 2+(2153904287/5000000000 : ℝ)*X 2 0+(35901323/80000000 : ℝ)*X 2 1+(826910449/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (310669550097967423328841909/47950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (151860083/50000000000000 : ℝ)*(base19) + (1762688157/100000000000000 : ℝ)*(base23) + (16267349/50000000000000 : ℝ)*(upper4) + (416410879/100000000000000 : ℝ)*(upper5) + (443074755036311/10000000000000 : ℝ)*(major0) + (443074755036311/10000000000000 : ℝ)*(major1) + (443074755036311/10000000000000 : ℝ)*(major2) + (302513510384129/5000000000000 : ℝ)*(sp0) + (605028638928211/10000000000000 : ℝ)*(sp1) + (1512580411540077/25000000000000 : ℝ)*(sp2) + (562230117213371/20000000000000 : ℝ)*(sp3) + (10640233177/20000000000000 : ℝ)*(sp4) + (36715846189/100000000000000 : ℝ)*(sp5) + (10444921591/50000000000000 : ℝ)*(sp7) + (1405585737955019/50000000000000 : ℝ)*(f.failure) + (1210064681769693/20000000000000 : ℝ)*(f.sum) + (8964072772609/1918000000000000000000000000 : ℝ)*base65 + (1652204890841425899/95900000000000000000000000000000 : ℝ)*base67 + (312502446526925899/95900000000000000000000000000000 : ℝ)*base69 + (549906889227525899/95900000000000000000000000000000 : ℝ)*base71 + (13084683864297/1918000000000000000000000000 : ℝ)*base73 + (528511672878725899/95900000000000000000000000000000 : ℝ)*base75 + (340920950010925899/95900000000000000000000000000000 : ℝ)*base77 + (1338804173026625899/95900000000000000000000000000000 : ℝ)*base79 + (5990137470733/1918000000000000000000000000 : ℝ)*base81 + (6285679/5000000000000000000000 : ℝ)*base89 + (6285679/5000000000000000000000 : ℝ)*base91 + (6285679/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (349592506890106742052598839/29968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (396111621/20000000000000 : ℝ)*(base19) + (537869539/25000000000000 : ℝ)*(base23) + (118971683/50000000000000 : ℝ)*(upper3) + (15516971/20000000000000 : ℝ)*(lower4) + (240181713/100000000000000 : ℝ)*(upper5) + (557937726518657/12500000000000 : ℝ)*(major0) + (557937726518657/12500000000000 : ℝ)*(major1) + (557937726518657/12500000000000 : ℝ)*(major2) + (10189298719/25000000000000 : ℝ)*(sp1) + (21903376847/50000000000000 : ℝ)*(sp2) + (3047525099730209/50000000000000 : ℝ)*(sp4) + (1523751865426859/25000000000000 : ℝ)*(sp5) + (761875530153571/12500000000000 : ℝ)*(sp6) + (1415976517998463/50000000000000 : ℝ)*(sp7) + (1415976517998463/50000000000000 : ℝ)*(f.failure) + (3047525099730209/50000000000000 : ℝ)*(f.sum) + (253977801009/599375000000000000000000000 : ℝ)*base65 + (702849626559700387/119875000000000000000000000000000 : ℝ)*base68 + (175049937998450387/119875000000000000000000000000000 : ℝ)*base70 + (1027337756751450387/119875000000000000000000000000000 : ℝ)*base72 + (127583627243/74921875000000000000000000 : ℝ)*base73 + (734206324313200387/119875000000000000000000000000000 : ℝ)*base76 + (198777150732799613/119875000000000000000000000000000 : ℝ)*base77 + (1694592778663950387/119875000000000000000000000000000 : ℝ)*base80 + (4231225761561/2397500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (11860717/5000000000000000000000 : ℝ)*base90 + (11860717/5000000000000000000000 : ℝ)*base92 + (11860717/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1415_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7477/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5559/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7391/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1415_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1415_s5_0 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-79300837/400000000 : ℝ)*x 0 + (5409147951/10000000000 : ℝ)*x 1 + (1311598691/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (79300837/400000000 : ℝ)^4375 ≤ (12090974110571/100000000000000 : ℝ)^3351 := by
    have hnat : (79300837 : ℕ)^4375*100000000000000^3351 ≤ 12090974110571^3351*400000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79300837 400000000 12090974110571 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409147951/10000000000 : ℝ)^4375 ≤ (44830983294073/100000000000000 : ℝ)^3351 := by
    have hnat : (5409147951 : ℕ)^4375*100000000000000^3351 ≤ 44830983294073^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409147951 10000000000 44830983294073 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311598691/2500000000 : ℝ)^4375 ≤ (10769510643493/25000000000000 : ℝ)^3351 := by
    have hnat : (1311598691 : ℕ)^4375*25000000000000^3351 ≤ 10769510643493^3351*2500000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311598691 2500000000 10769510643493 25000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-79300837/400000000 : ℝ), (5409147951/10000000000 : ℝ), (1311598691/2500000000 : ℝ)] ![(12090974110571/100000000000000 : ℝ), (44830983294073/100000000000000 : ℝ), (10769510643493/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-79300837/400000000 : ℝ)|^4375 ≤ (12090974110571/100000000000000 : ℝ)^3351
        have hw : |(-79300837/400000000 : ℝ)|=(79300837/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409147951/10000000000 : ℝ)|^4375 ≤ (44830983294073/100000000000000 : ℝ)^3351
        have hw : |(5409147951/10000000000 : ℝ)|=(5409147951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311598691/2500000000 : ℝ)|^4375 ≤ (10769510643493/25000000000000 : ℝ)^3351
        have hw : |(1311598691/2500000000 : ℝ)|=(1311598691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s5_1 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673835823/5000000000 : ℝ)*x 0 + (-1032697051/5000000000 : ℝ)*x 1 + (2623197673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673835823/5000000000 : ℝ)^4375 ≤ (44166928393839/100000000000000 : ℝ)^3351 := by
    have hnat : (2673835823 : ℕ)^4375*100000000000000^3351 ≤ 44166928393839^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673835823 5000000000 44166928393839 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1032697051/5000000000 : ℝ)^4375 ≤ (1594377846641/12500000000000 : ℝ)^3351 := by
    have hnat : (1032697051 : ℕ)^4375*12500000000000^3351 ≤ 1594377846641^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032697051 5000000000 1594377846641 12500000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623197673/5000000000 : ℝ)^4375 ≤ (43078048813067/100000000000000 : ℝ)^3351 := by
    have hnat : (2623197673 : ℕ)^4375*100000000000000^3351 ≤ 43078048813067^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623197673 5000000000 43078048813067 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673835823/5000000000 : ℝ), (-1032697051/5000000000 : ℝ), (2623197673/5000000000 : ℝ)] ![(44166928393839/100000000000000 : ℝ), (1594377846641/12500000000000 : ℝ), (43078048813067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673835823/5000000000 : ℝ)|^4375 ≤ (44166928393839/100000000000000 : ℝ)^3351
        have hw : |(2673835823/5000000000 : ℝ)|=(2673835823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1032697051/5000000000 : ℝ)|^4375 ≤ (1594377846641/12500000000000 : ℝ)^3351
        have hw : |(-1032697051/5000000000 : ℝ)|=(1032697051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623197673/5000000000 : ℝ)|^4375 ≤ (43078048813067/100000000000000 : ℝ)^3351
        have hw : |(2623197673/5000000000 : ℝ)|=(2623197673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s5_2 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347671759/10000000000 : ℝ)*x 0 + (5246394921/10000000000 : ℝ)*x 1 + (-516348629/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347671759/10000000000 : ℝ)^4375 ≤ (44166929612309/100000000000000 : ℝ)^3351 := by
    have hnat : (5347671759 : ℕ)^4375*100000000000000^3351 ≤ 44166929612309^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347671759 10000000000 44166929612309 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246394921/10000000000 : ℝ)^4375 ≤ (43078044257027/100000000000000 : ℝ)^3351 := by
    have hnat : (5246394921 : ℕ)^4375*100000000000000^3351 ≤ 43078044257027^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246394921 10000000000 43078044257027 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516348629/2500000000 : ℝ)^4375 ≤ (12755026111097/100000000000000 : ℝ)^3351 := by
    have hnat : (516348629 : ℕ)^4375*100000000000000^3351 ≤ 12755026111097^3351*2500000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516348629 2500000000 12755026111097 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347671759/10000000000 : ℝ), (5246394921/10000000000 : ℝ), (-516348629/2500000000 : ℝ)] ![(44166929612309/100000000000000 : ℝ), (43078044257027/100000000000000 : ℝ), (12755026111097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347671759/10000000000 : ℝ)|^4375 ≤ (44166929612309/100000000000000 : ℝ)^3351
        have hw : |(5347671759/10000000000 : ℝ)|=(5347671759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246394921/10000000000 : ℝ)|^4375 ≤ (43078044257027/100000000000000 : ℝ)^3351
        have hw : |(5246394921/10000000000 : ℝ)|=(5246394921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-516348629/2500000000 : ℝ)|^4375 ≤ (12755026111097/100000000000000 : ℝ)^3351
        have hw : |(-516348629/2500000000 : ℝ)|=(516348629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s5_3 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2153936309/5000000000 : ℝ)*x 0 + (4135952879/10000000000 : ℝ)*x 1 + (4486235993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153936309/5000000000 : ℝ)^4375 ≤ (8326083254559/25000000000000 : ℝ)^3351 := by
    have hnat : (2153936309 : ℕ)^4375*25000000000000^3351 ≤ 8326083254559^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153936309 5000000000 8326083254559 25000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4135952879/10000000000 : ℝ)^4375 ≤ (7894935654971/25000000000000 : ℝ)^3351 := by
    have hnat : (4135952879 : ℕ)^4375*25000000000000^3351 ≤ 7894935654971^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135952879 10000000000 7894935654971 25000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4486235993/10000000000 : ℝ)^4375 ≤ (35115924344159/100000000000000 : ℝ)^3351 := by
    have hnat : (4486235993 : ℕ)^4375*100000000000000^3351 ≤ 35115924344159^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486235993 10000000000 35115924344159 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2153936309/5000000000 : ℝ), (4135952879/10000000000 : ℝ), (4486235993/10000000000 : ℝ)] ![(8326083254559/25000000000000 : ℝ), (7894935654971/25000000000000 : ℝ), (35115924344159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2153936309/5000000000 : ℝ)|^4375 ≤ (8326083254559/25000000000000 : ℝ)^3351
        have hw : |(2153936309/5000000000 : ℝ)|=(2153936309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4135952879/10000000000 : ℝ)|^4375 ≤ (7894935654971/25000000000000 : ℝ)^3351
        have hw : |(4135952879/10000000000 : ℝ)|=(4135952879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4486235993/10000000000 : ℝ)|^4375 ≤ (35115924344159/100000000000000 : ℝ)^3351
        have hw : |(4486235993/10000000000 : ℝ)|=(4486235993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s5_4 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-396506501/2000000000 : ℝ)*x 0 + (52469827/100000000 : ℝ)*x 1 + (2704278469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (396506501/2000000000 : ℝ)^4375 ≤ (6045533157957/50000000000000 : ℝ)^3351 := by
    have hnat : (396506501 : ℕ)^4375*50000000000000^3351 ≤ 6045533157957^3351*2000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396506501 2000000000 6045533157957 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52469827/100000000 : ℝ)^4375 ≤ (21542172705763/50000000000000 : ℝ)^3351 := by
    have hnat : (52469827 : ℕ)^4375*50000000000000^3351 ≤ 21542172705763^3351*100000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52469827 100000000 21542172705763 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704278469/5000000000 : ℝ)^4375 ≤ (22412294130337/50000000000000 : ℝ)^3351 := by
    have hnat : (2704278469 : ℕ)^4375*50000000000000^3351 ≤ 22412294130337^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704278469 5000000000 22412294130337 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-396506501/2000000000 : ℝ), (52469827/100000000 : ℝ), (2704278469/5000000000 : ℝ)] ![(6045533157957/50000000000000 : ℝ), (21542172705763/50000000000000 : ℝ), (22412294130337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-396506501/2000000000 : ℝ)|^4375 ≤ (6045533157957/50000000000000 : ℝ)^3351
        have hw : |(-396506501/2000000000 : ℝ)|=(396506501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52469827/100000000 : ℝ)|^4375 ≤ (21542172705763/50000000000000 : ℝ)^3351
        have hw : |(52469827/100000000 : ℝ)|=(52469827/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704278469/5000000000 : ℝ)|^4375 ≤ (22412294130337/50000000000000 : ℝ)^3351
        have hw : |(2704278469/5000000000 : ℝ)|=(2704278469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s5_5 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305419203/10000000000 : ℝ)*x 0 + (-380646479/2000000000 : ℝ)*x 1 + (2704278469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305419203/10000000000 : ℝ)^4375 ≤ (43711875004251/100000000000000 : ℝ)^3351 := by
    have hnat : (5305419203 : ℕ)^4375*100000000000000^3351 ≤ 43711875004251^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305419203 10000000000 43711875004251 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (380646479/2000000000 : ℝ)^4375 ≤ (11463536725447/100000000000000 : ℝ)^3351 := by
    have hnat : (380646479 : ℕ)^4375*100000000000000^3351 ≤ 11463536725447^3351*2000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      380646479 2000000000 11463536725447 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704278469/5000000000 : ℝ)^4375 ≤ (22412294130337/50000000000000 : ℝ)^3351 := by
    have hnat : (2704278469 : ℕ)^4375*50000000000000^3351 ≤ 22412294130337^3351*5000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704278469 5000000000 22412294130337 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305419203/10000000000 : ℝ), (-380646479/2000000000 : ℝ), (2704278469/5000000000 : ℝ)] ![(43711875004251/100000000000000 : ℝ), (11463536725447/100000000000000 : ℝ), (22412294130337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305419203/10000000000 : ℝ)|^4375 ≤ (43711875004251/100000000000000 : ℝ)^3351
        have hw : |(5305419203/10000000000 : ℝ)|=(5305419203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-380646479/2000000000 : ℝ)|^4375 ≤ (11463536725447/100000000000000 : ℝ)^3351
        have hw : |(-380646479/2000000000 : ℝ)|=(380646479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704278469/5000000000 : ℝ)|^4375 ≤ (22412294130337/50000000000000 : ℝ)^3351
        have hw : |(2704278469/5000000000 : ℝ)|=(2704278469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s5_6 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305419201/10000000000 : ℝ)*x 0 + (270427847/500000000 : ℝ)*x 1 + (-380646479/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305419201/10000000000 : ℝ)^4375 ≤ (43711874982737/100000000000000 : ℝ)^3351 := by
    have hnat : (5305419201 : ℕ)^4375*100000000000000^3351 ≤ 43711874982737^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305419201 10000000000 43711874982737 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270427847/500000000 : ℝ)^4375 ≤ (22412294141157/50000000000000 : ℝ)^3351 := by
    have hnat : (270427847 : ℕ)^4375*50000000000000^3351 ≤ 22412294141157^3351*500000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270427847 500000000 22412294141157 50000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (380646479/2000000000 : ℝ)^4375 ≤ (11463536725447/100000000000000 : ℝ)^3351 := by
    have hnat : (380646479 : ℕ)^4375*100000000000000^3351 ≤ 11463536725447^3351*2000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      380646479 2000000000 11463536725447 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305419201/10000000000 : ℝ), (270427847/500000000 : ℝ), (-380646479/2000000000 : ℝ)] ![(43711874982737/100000000000000 : ℝ), (22412294141157/50000000000000 : ℝ), (11463536725447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305419201/10000000000 : ℝ)|^4375 ≤ (43711874982737/100000000000000 : ℝ)^3351
        have hw : |(5305419201/10000000000 : ℝ)|=(5305419201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270427847/500000000 : ℝ)|^4375 ≤ (22412294141157/50000000000000 : ℝ)^3351
        have hw : |(270427847/500000000 : ℝ)|=(270427847/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-380646479/2000000000 : ℝ)|^4375 ≤ (11463536725447/100000000000000 : ℝ)^3351
        have hw : |(-380646479/2000000000 : ℝ)|=(380646479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1415_s5_7 (p : ℝ) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538487169/1250000000 : ℝ)*x 0 + (4484971261/10000000000 : ℝ)*x 1 + (517153033/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538487169/1250000000 : ℝ)^4375 ≤ (33304582670929/100000000000000 : ℝ)^3351 := by
    have hnat : (538487169 : ℕ)^4375*100000000000000^3351 ≤ 33304582670929^3351*1250000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538487169 1250000000 33304582670929 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484971261/10000000000 : ℝ)^4375 ≤ (35103000092151/100000000000000 : ℝ)^3351 := by
    have hnat : (4484971261 : ℕ)^4375*100000000000000^3351 ≤ 35103000092151^3351*10000000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484971261 10000000000 35103000092151 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517153033/1250000000 : ℝ)^4375 ≤ (31592417215513/100000000000000 : ℝ)^3351 := by
    have hnat : (517153033 : ℕ)^4375*100000000000000^3351 ≤ 31592417215513^3351*1250000000^4375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517153033 1250000000 31592417215513 100000000000000 4375 3351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4375/1024 : ℝ)) 4375 3351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538487169/1250000000 : ℝ), (4484971261/10000000000 : ℝ), (517153033/1250000000 : ℝ)] ![(33304582670929/100000000000000 : ℝ), (35103000092151/100000000000000 : ℝ), (31592417215513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538487169/1250000000 : ℝ)|^4375 ≤ (33304582670929/100000000000000 : ℝ)^3351
        have hw : |(538487169/1250000000 : ℝ)|=(538487169/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484971261/10000000000 : ℝ)|^4375 ≤ (35103000092151/100000000000000 : ℝ)^3351
        have hw : |(4484971261/10000000000 : ℝ)|=(4484971261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(517153033/1250000000 : ℝ)|^4375 ≤ (31592417215513/100000000000000 : ℝ)^3351
        have hw : |(517153033/1250000000 : ℝ)|=(517153033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1415_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7391/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11307/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7377/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7391/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11281/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7391/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11281/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7391/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11281/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7391/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11281/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7391/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11281/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7391/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11281/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11281/100000 : ℝ) ^ (2187/512 : ℝ) ≤ (223901800432503/2500000000000000000 : ℝ) := by
    have hpowers : (11281/100000 : ℝ)^2187 ≤ (223901800432503/2500000000000000000 : ℝ)^512 := by
      have hnat : (11281 : ℕ)^2187*2500000000000000000^512 ≤ 223901800432503^512*100000^2187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11281 100000 223901800432503 2500000000000000000 2187 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11281/100000 : ℝ)) (X := (223901800432503/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7391/50000 : ℝ) ^ (2187/512 : ℝ) ≤ (14206867572721461/50000000000000000000 : ℝ) := by
    have hpowers : (7391/50000 : ℝ)^2187 ≤ (14206867572721461/50000000000000000000 : ℝ)^512 := by
      have hnat : (7391 : ℕ)^2187*50000000000000000000^512 ≤ 14206867572721461^512*50000^2187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7391 50000 14206867572721461 50000000000000000000 2187 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7391/50000 : ℝ)) (X := (14206867572721461/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250223901800432503/1250000000000000000 : ℝ) ≤ (10000419313614033/10000000000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (1250223901800432503/1250000000000000000 : ℝ)^512 ≤ (10000419313614033/10000000000000000 : ℝ)^2187 := by
      have hnat : (1250223901800432503 : ℕ)^512*10000000000000000^2187 ≤ 10000419313614033^2187*1250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250223901800432503 1250000000000000000 10000419313614033 10000000000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000419313614033/10000000000000000 : ℝ)) (X := (1250223901800432503/1250000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018684903581371521/50000000000000000000 : ℝ) ≤ (2000174948365611/2000000000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (50018684903581371521/50000000000000000000 : ℝ)^512 ≤ (2000174948365611/2000000000000000 : ℝ)^2187 := by
      have hnat : (50018684903581371521 : ℕ)^512*2000000000000000^2187 ≤ 2000174948365611^2187*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018684903581371521 50000000000000000000 2000174948365611 2000000000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000174948365611/2000000000000000 : ℝ)) (X := (50018684903581371521/50000000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014206867572721461/25000000000000000000 : ℝ) ≤ (10001330170042077/10000000000000000 : ℝ) ^ (2187/512 : ℝ) := by
    have hpowers : (25014206867572721461/25000000000000000000 : ℝ)^512 ≤ (10001330170042077/10000000000000000 : ℝ)^2187 := by
      have hnat : (25014206867572721461 : ℕ)^512*10000000000000000^2187 ≤ 10001330170042077^2187*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014206867572721461 25000000000000000000 10001330170042077 10000000000000000 512 2187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001330170042077/10000000000000000 : ℝ)) (X := (25014206867572721461/25000000000000000000 : ℝ)) (by norm_num) 2187 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(223901800432503/2500000000000000000 : ℝ) ≤ ((29992452995371007/30000000000000000 : ℝ)+2*(75904702337/58350000000000 : ℝ)*(11281/100000 : ℝ))^(2187/512 : ℝ) := by
    rw [show (29992452995371007/30000000000000000 : ℝ)+2*(75904702337/58350000000000 : ℝ)*(11281/100000 : ℝ)=(10000419313614033/10000000000000000 : ℝ) by norm_num, show 1+2*(223901800432503/2500000000000000000 : ℝ)=(1250223901800432503/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14206867572721461/50000000000000000000 : ℝ)+(223901800432503/2500000000000000000 : ℝ) ≤ ((29992452995371007/30000000000000000 : ℝ)+(75904702337/58350000000000 : ℝ)*((7391/50000 : ℝ)+(11281/100000 : ℝ)))^(2187/512 : ℝ) := by
    rw [show (29992452995371007/30000000000000000 : ℝ)+(75904702337/58350000000000 : ℝ)*((7391/50000 : ℝ)+(11281/100000 : ℝ))=(2000174948365611/2000000000000000 : ℝ) by norm_num, show 1+(14206867572721461/50000000000000000000 : ℝ)+(223901800432503/2500000000000000000 : ℝ)=(50018684903581371521/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14206867572721461/50000000000000000000 : ℝ) ≤ ((29992452995371007/30000000000000000 : ℝ)+2*(75904702337/58350000000000 : ℝ)*(7391/50000 : ℝ))^(2187/512 : ℝ) := by
    rw [show (29992452995371007/30000000000000000 : ℝ)+2*(75904702337/58350000000000 : ℝ)*(7391/50000 : ℝ)=(10001330170042077/10000000000000000 : ℝ) by norm_num, show 1+2*(14206867572721461/50000000000000000000 : ℝ)=(25014206867572721461/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29992452995371007/30000000000000000 : ℝ)*(X 1 0+X 2 0)+(75904702337/58350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (11281/100000 : ℝ)) (hi := (7391/50000 : ℝ)) (c := (29992452995371007/30000000000000000 : ℝ)) (alpha := (75904702337/58350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29992452995371007/30000000000000000 : ℝ)*(X 0 1+X 2 1)+(75904702337/58350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (11281/100000 : ℝ)) (hi := (7391/50000 : ℝ)) (c := (29992452995371007/30000000000000000 : ℝ)) (alpha := (75904702337/58350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29992452995371007/30000000000000000 : ℝ)*(X 0 2+X 1 2)+(75904702337/58350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2187/512 : ℝ)) (lo := (11281/100000 : ℝ)) (hi := (7391/50000 : ℝ)) (c := (29992452995371007/30000000000000000 : ℝ)) (alpha := (75904702337/58350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-79300837/400000000 : ℝ)*X 0 0+(5409147951/10000000000 : ℝ)*X 0 1+(1311598691/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673835823/5000000000 : ℝ)*X 1 0+(-1032697051/5000000000 : ℝ)*X 1 1+(2623197673/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347671759/10000000000 : ℝ)*X 2 0+(5246394921/10000000000 : ℝ)*X 2 1+(-516348629/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2153936309/5000000000 : ℝ)*X 0 0+(4135952879/10000000000 : ℝ)*X 0 1+(4486235993/10000000000 : ℝ)*X 0 2+(2153936309/5000000000 : ℝ)*X 1 0+(4135952879/10000000000 : ℝ)*X 1 1+(4486235993/10000000000 : ℝ)*X 1 2+(2153936309/5000000000 : ℝ)*X 2 0+(4135952879/10000000000 : ℝ)*X 2 1+(4486235993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-396506501/2000000000 : ℝ)*X 0 0+(52469827/100000000 : ℝ)*X 0 1+(2704278469/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305419203/10000000000 : ℝ)*X 1 0+(-380646479/2000000000 : ℝ)*X 1 1+(2704278469/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305419201/10000000000 : ℝ)*X 2 0+(270427847/500000000 : ℝ)*X 2 1+(-380646479/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((538487169/1250000000 : ℝ)*X 0 0+(4484971261/10000000000 : ℝ)*X 0 1+(517153033/1250000000 : ℝ)*X 0 2+(538487169/1250000000 : ℝ)*X 1 0+(4484971261/10000000000 : ℝ)*X 1 1+(517153033/1250000000 : ℝ)*X 1 2+(538487169/1250000000 : ℝ)*X 2 0+(4484971261/10000000000 : ℝ)*X 2 1+(517153033/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1415_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (160265891735445544656105849/24312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (774679427/100000000000000 : ℝ)*(base19) + (530290037/50000000000000 : ℝ)*(base23) + (137163359/50000000000000 : ℝ)*(upper3) + (96178177/100000000000000 : ℝ)*(lower4) + (562449725614221/12500000000000 : ℝ)*(major0) + (562449725614221/12500000000000 : ℝ)*(major1) + (562449725614221/12500000000000 : ℝ)*(major2) + (61443127255783/1000000000000 : ℝ)*(sp0) + (153608494874813/2500000000000 : ℝ)*(sp1) + (1228867299775077/20000000000000 : ℝ)*(sp2) + (5709684671533/200000000000 : ℝ)*(sp3) + (27844093647/100000000000000 : ℝ)*(sp4) + (376277061/12500000000000 : ℝ)*(sp6) + (156058233/1250000000000 : ℝ)*(sp7) + (142742741021257/5000000000000 : ℝ)*(f.failure) + (6144340569671947/100000000000000 : ℝ)*(f.sum) + (1253247311981/1945000000000000000000000000 : ℝ)*base66 + (240523327263025739/48625000000000000000000000000000 : ℝ)*base68 + (126726278954775739/48625000000000000000000000000000 : ℝ)*base70 + (529318748755525739/48625000000000000000000000000000 : ℝ)*base72 + (724575491739/486250000000000000000000000 : ℝ)*base74 + (235510996133025739/48625000000000000000000000000000 : ℝ)*base76 + (735520373628900739/48625000000000000000000000000000 : ℝ)*base78 + (698900315368650739/48625000000000000000000000000000 : ℝ)*base80 + (552402832843/243125000000000000000000000 : ℝ)*base81 + (2281237/500000000000000000000 : ℝ)*base89 + (2281237/500000000000000000000 : ℝ)*base91 + (2281237/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3220934683511000114012399/500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1099608147/100000000000000 : ℝ)*(base19) + (1188246929/100000000000000 : ℝ)*(base23) + (8279431/6250000000000 : ℝ)*(upper3) + (41229819/100000000000000 : ℝ)*(lower4) + (132656711/100000000000000 : ℝ)*(upper5) + (4532379175195057/100000000000000 : ℝ)*(major0) + (4532379175195057/100000000000000 : ℝ)*(major1) + (4532379175195057/100000000000000 : ℝ)*(major2) + (4593047213/20000000000000 : ℝ)*(sp1) + (12315032439/50000000000000 : ℝ)*(sp2) + (3094552277826153/50000000000000 : ℝ)*(sp4) + (3094540245404047/50000000000000 : ℝ)*(sp5) + (6189078737340499/100000000000000 : ℝ)*(sp6) + (115026143200353/4000000000000 : ℝ)*(sp7) + (115026143200353/4000000000000 : ℝ)*(f.failure) + (3094552277826153/50000000000000 : ℝ)*(f.sum) + (462142214999/182343750000000000000000000 : ℝ)*base65 + (12188815161589123211/1167000000000000000000000000000000 : ℝ)*base67 + (9854116040011876789/1167000000000000000000000000000000 : ℝ)*base70 + (325806260440123211/1167000000000000000000000000000000 : ℝ)*base71 + (8353948059643/5835000000000000000000000000 : ℝ)*base73 + (5776163649889876789/1167000000000000000000000000000000 : ℝ)*base76 + (4453478426602876789/1167000000000000000000000000000000 : ℝ)*base78 + (6543975616576876789/1167000000000000000000000000000000 : ℝ)*base80 + (16169221203827/5835000000000000000000000000 : ℝ)*base82 + (285773/400000000000000000000 : ℝ)*base89 + (285773/400000000000000000000 : ℝ)*base91 + (285773/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1415_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7391/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1415_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1415_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15843/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10291/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1415_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1415_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1415_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2187/512 : ℝ) ≤ p) (hpb : p ≤ (4375/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157612141/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15843/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10291/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1415_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
