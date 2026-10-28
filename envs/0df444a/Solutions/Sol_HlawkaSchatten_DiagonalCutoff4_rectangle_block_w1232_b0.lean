-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1232_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:15:37.160994+00:00
-- url     : https://prove2.me/submissions/442c7650-6fdd-4ee4-aaad-cebcca523a7b

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
theorem support_rectangle_w1232_s0_0 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-465912397/2500000000 : ℝ)*x 0 + (6033761977/10000000000 : ℝ)*x 1 + (958349639/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (465912397/2500000000 : ℝ)^8425 ≤ (10865224710323/100000000000000 : ℝ)^6377 := by
    have hnat : (465912397 : ℕ)^8425*100000000000000^6377 ≤ 10865224710323^6377*2500000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465912397 2500000000 10865224710323 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6033761977/10000000000 : ℝ)^8425 ≤ (51300684026507/100000000000000 : ℝ)^6377 := by
    have hnat : (6033761977 : ℕ)^8425*100000000000000^6377 ≤ 51300684026507^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6033761977 10000000000 51300684026507 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (958349639/2000000000 : ℝ)^8425 ≤ (37834091247527/100000000000000 : ℝ)^6377 := by
    have hnat : (958349639 : ℕ)^8425*100000000000000^6377 ≤ 37834091247527^6377*2000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958349639 2000000000 37834091247527 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-465912397/2500000000 : ℝ), (6033761977/10000000000 : ℝ), (958349639/2000000000 : ℝ)] ![(10865224710323/100000000000000 : ℝ), (51300684026507/100000000000000 : ℝ), (37834091247527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-465912397/2500000000 : ℝ)|^8425 ≤ (10865224710323/100000000000000 : ℝ)^6377
        have hw : |(-465912397/2500000000 : ℝ)|=(465912397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6033761977/10000000000 : ℝ)|^8425 ≤ (51300684026507/100000000000000 : ℝ)^6377
        have hw : |(6033761977/10000000000 : ℝ)|=(6033761977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(958349639/2000000000 : ℝ)|^8425 ≤ (37834091247527/100000000000000 : ℝ)^6377
        have hw : |(958349639/2000000000 : ℝ)|=(958349639/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s0_1 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2755861439/5000000000 : ℝ)*x 0 + (-514789797/2000000000 : ℝ)*x 1 + (958349629/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2755861439/5000000000 : ℝ)^8425 ≤ (355623761333/781250000000 : ℝ)^6377 := by
    have hnat : (2755861439 : ℕ)^8425*781250000000^6377 ≤ 355623761333^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755861439 5000000000 355623761333 781250000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (514789797/2000000000 : ℝ)^8425 ≤ (1664606781261/10000000000000 : ℝ)^6377 := by
    have hnat : (514789797 : ℕ)^8425*10000000000000^6377 ≤ 1664606781261^6377*2000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514789797 2000000000 1664606781261 10000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (958349629/2000000000 : ℝ)^8425 ≤ (37834090725957/100000000000000 : ℝ)^6377 := by
    have hnat : (958349629 : ℕ)^8425*100000000000000^6377 ≤ 37834090725957^6377*2000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958349629 2000000000 37834090725957 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2755861439/5000000000 : ℝ), (-514789797/2000000000 : ℝ), (958349629/2000000000 : ℝ)] ![(355623761333/781250000000 : ℝ), (1664606781261/10000000000000 : ℝ), (37834090725957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2755861439/5000000000 : ℝ)|^8425 ≤ (355623761333/781250000000 : ℝ)^6377
        have hw : |(2755861439/5000000000 : ℝ)|=(2755861439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-514789797/2000000000 : ℝ)|^8425 ≤ (1664606781261/10000000000000 : ℝ)^6377
        have hw : |(-514789797/2000000000 : ℝ)|=(514789797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(958349629/2000000000 : ℝ)|^8425 ≤ (37834090725957/100000000000000 : ℝ)^6377
        have hw : |(958349629/2000000000 : ℝ)|=(958349629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s0_2 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1102344563/2000000000 : ℝ)*x 0 + (4791748213/10000000000 : ℝ)*x 1 + (-1286974491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102344563/2000000000 : ℝ)^8425 ≤ (45519840763227/100000000000000 : ℝ)^6377 := by
    have hnat : (1102344563 : ℕ)^8425*100000000000000^6377 ≤ 45519840763227^6377*2000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102344563 2000000000 45519840763227 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4791748213/10000000000 : ℝ)^8425 ≤ (9458522858823/25000000000000 : ℝ)^6377 := by
    have hnat : (4791748213 : ℕ)^8425*25000000000000^6377 ≤ 9458522858823^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4791748213 10000000000 9458522858823 25000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1286974491/5000000000 : ℝ)^8425 ≤ (8323033893489/50000000000000 : ℝ)^6377 := by
    have hnat : (1286974491 : ℕ)^8425*50000000000000^6377 ≤ 8323033893489^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1286974491 5000000000 8323033893489 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1102344563/2000000000 : ℝ), (4791748213/10000000000 : ℝ), (-1286974491/5000000000 : ℝ)] ![(45519840763227/100000000000000 : ℝ), (9458522858823/25000000000000 : ℝ), (8323033893489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1102344563/2000000000 : ℝ)|^8425 ≤ (45519840763227/100000000000000 : ℝ)^6377
        have hw : |(1102344563/2000000000 : ℝ)|=(1102344563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4791748213/10000000000 : ℝ)|^8425 ≤ (9458522858823/25000000000000 : ℝ)^6377
        have hw : |(4791748213/10000000000 : ℝ)|=(4791748213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1286974491/5000000000 : ℝ)|^8425 ≤ (8323033893489/50000000000000 : ℝ)^6377
        have hw : |(-1286974491/5000000000 : ℝ)|=(1286974491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s0_3 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2096904031/5000000000 : ℝ)*x 0 + (1558635157/5000000000 : ℝ)*x 1 + (901107/1600000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096904031/5000000000 : ℝ)^8425 ≤ (991420152461/3125000000000 : ℝ)^6377 := by
    have hnat : (2096904031 : ℕ)^8425*3125000000000^6377 ≤ 991420152461^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096904031 5000000000 991420152461 3125000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1558635157/5000000000 : ℝ)^8425 ≤ (1339917472771/6250000000000 : ℝ)^6377 := by
    have hnat : (1558635157 : ℕ)^8425*6250000000000^6377 ≤ 1339917472771^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1558635157 5000000000 1339917472771 6250000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901107/1600000 : ℝ)^8425 ≤ (11708968883927/25000000000000 : ℝ)^6377 := by
    have hnat : (901107 : ℕ)^8425*25000000000000^6377 ≤ 11708968883927^6377*1600000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901107 1600000 11708968883927 25000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2096904031/5000000000 : ℝ), (1558635157/5000000000 : ℝ), (901107/1600000 : ℝ)] ![(991420152461/3125000000000 : ℝ), (1339917472771/6250000000000 : ℝ), (11708968883927/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2096904031/5000000000 : ℝ)|^8425 ≤ (991420152461/3125000000000 : ℝ)^6377
        have hw : |(2096904031/5000000000 : ℝ)|=(2096904031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1558635157/5000000000 : ℝ)|^8425 ≤ (1339917472771/6250000000000 : ℝ)^6377
        have hw : |(1558635157/5000000000 : ℝ)|=(1558635157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(901107/1600000 : ℝ)|^8425 ≤ (11708968883927/25000000000000 : ℝ)^6377
        have hw : |(901107/1600000 : ℝ)|=(901107/1600000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s0_4 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1868535571/10000000000 : ℝ)*x 0 + (964747841/2000000000 : ℝ)*x 1 + (6000640567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1868535571/10000000000 : ℝ)^8425 ≤ (10902874502717/100000000000000 : ℝ)^6377 := by
    have hnat : (1868535571 : ℕ)^8425*100000000000000^6377 ≤ 10902874502717^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868535571 10000000000 10902874502717 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (964747841/2000000000 : ℝ)^8425 ≤ (7633631930131/20000000000000 : ℝ)^6377 := by
    have hnat : (964747841 : ℕ)^8425*20000000000000^6377 ≤ 7633631930131^6377*2000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964747841 2000000000 7633631930131 20000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6000640567/10000000000 : ℝ)^8425 ≤ (50928965821937/100000000000000 : ℝ)^6377 := by
    have hnat : (6000640567 : ℕ)^8425*100000000000000^6377 ≤ 50928965821937^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6000640567 10000000000 50928965821937 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1868535571/10000000000 : ℝ), (964747841/2000000000 : ℝ), (6000640567/10000000000 : ℝ)] ![(10902874502717/100000000000000 : ℝ), (7633631930131/20000000000000 : ℝ), (50928965821937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1868535571/10000000000 : ℝ)|^8425 ≤ (10902874502717/100000000000000 : ℝ)^6377
        have hw : |(-1868535571/10000000000 : ℝ)|=(1868535571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(964747841/2000000000 : ℝ)|^8425 ≤ (7633631930131/20000000000000 : ℝ)^6377
        have hw : |(964747841/2000000000 : ℝ)|=(964747841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6000640567/10000000000 : ℝ)|^8425 ≤ (50928965821937/100000000000000 : ℝ)^6377
        have hw : |(6000640567/10000000000 : ℝ)|=(6000640567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s0_5 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2586915527/5000000000 : ℝ)*x 0 + (-273010899/2000000000 : ℝ)*x 1 + (6000642729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586915527/5000000000 : ℝ)^8425 ≤ (20934946838299/50000000000000 : ℝ)^6377 := by
    have hnat : (2586915527 : ℕ)^8425*50000000000000^6377 ≤ 20934946838299^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586915527 5000000000 20934946838299 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273010899/2000000000 : ℝ)^8425 ≤ (1800279060047/25000000000000 : ℝ)^6377 := by
    have hnat : (273010899 : ℕ)^8425*25000000000000^6377 ≤ 1800279060047^6377*2000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273010899 2000000000 1800279060047 25000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6000642729/10000000000 : ℝ)^8425 ≤ (198941367439/390625000000 : ℝ)^6377 := by
    have hnat : (6000642729 : ℕ)^8425*390625000000^6377 ≤ 198941367439^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6000642729 10000000000 198941367439 390625000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586915527/5000000000 : ℝ), (-273010899/2000000000 : ℝ), (6000642729/10000000000 : ℝ)] ![(20934946838299/50000000000000 : ℝ), (1800279060047/25000000000000 : ℝ), (198941367439/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586915527/5000000000 : ℝ)|^8425 ≤ (20934946838299/50000000000000 : ℝ)^6377
        have hw : |(2586915527/5000000000 : ℝ)|=(2586915527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-273010899/2000000000 : ℝ)|^8425 ≤ (1800279060047/25000000000000 : ℝ)^6377
        have hw : |(-273010899/2000000000 : ℝ)|=(273010899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6000642729/10000000000 : ℝ)|^8425 ≤ (198941367439/390625000000 : ℝ)^6377
        have hw : |(6000642729/10000000000 : ℝ)|=(6000642729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s0_6 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5173831863/10000000000 : ℝ)*x 0 + (1200128213/2000000000 : ℝ)*x 1 + (-341263983/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173831863/10000000000 : ℝ)^8425 ≤ (4186990232611/10000000000000 : ℝ)^6377 := by
    have hnat : (5173831863 : ℕ)^8425*10000000000000^6377 ≤ 4186990232611^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173831863 10000000000 4186990232611 10000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1200128213/2000000000 : ℝ)^8425 ≤ (50928971405997/100000000000000 : ℝ)^6377 := by
    have hnat : (1200128213 : ℕ)^8425*100000000000000^6377 ≤ 50928971405997^6377*2000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200128213 2000000000 50928971405997 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (341263983/2500000000 : ℝ)^8425 ≤ (7201126255401/100000000000000 : ℝ)^6377 := by
    have hnat : (341263983 : ℕ)^8425*100000000000000^6377 ≤ 7201126255401^6377*2500000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341263983 2500000000 7201126255401 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173831863/10000000000 : ℝ), (1200128213/2000000000 : ℝ), (-341263983/2500000000 : ℝ)] ![(4186990232611/10000000000000 : ℝ), (50928971405997/100000000000000 : ℝ), (7201126255401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173831863/10000000000 : ℝ)|^8425 ≤ (4186990232611/10000000000000 : ℝ)^6377
        have hw : |(5173831863/10000000000 : ℝ)|=(5173831863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1200128213/2000000000 : ℝ)|^8425 ≤ (50928971405997/100000000000000 : ℝ)^6377
        have hw : |(1200128213/2000000000 : ℝ)|=(1200128213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-341263983/2500000000 : ℝ)|^8425 ≤ (7201126255401/100000000000000 : ℝ)^6377
        have hw : |(-341263983/2500000000 : ℝ)|=(341263983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s0_7 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4203700763/10000000000 : ℝ)*x 0 + (2783576447/5000000000 : ℝ)*x 1 + (1592162069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4203700763/10000000000 : ℝ)^8425 ≤ (31824352994973/100000000000000 : ℝ)^6377 := by
    have hnat : (4203700763 : ℕ)^8425*100000000000000^6377 ≤ 31824352994973^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4203700763 10000000000 31824352994973 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2783576447/5000000000 : ℝ)^8425 ≤ (23062808015921/50000000000000 : ℝ)^6377 := by
    have hnat : (2783576447 : ℕ)^8425*50000000000000^6377 ≤ 23062808015921^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2783576447 5000000000 23062808015921 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1592162069/5000000000 : ℝ)^8425 ≤ (4410006191009/20000000000000 : ℝ)^6377 := by
    have hnat : (1592162069 : ℕ)^8425*20000000000000^6377 ≤ 4410006191009^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1592162069 5000000000 4410006191009 20000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4203700763/10000000000 : ℝ), (2783576447/5000000000 : ℝ), (1592162069/5000000000 : ℝ)] ![(31824352994973/100000000000000 : ℝ), (23062808015921/50000000000000 : ℝ), (4410006191009/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4203700763/10000000000 : ℝ)|^8425 ≤ (31824352994973/100000000000000 : ℝ)^6377
        have hw : |(4203700763/10000000000 : ℝ)|=(4203700763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2783576447/5000000000 : ℝ)|^8425 ≤ (23062808015921/50000000000000 : ℝ)^6377
        have hw : |(2783576447/5000000000 : ℝ)|=(2783576447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1592162069/5000000000 : ℝ)|^8425 ≤ (4410006191009/20000000000000 : ℝ)^6377
        have hw : |(1592162069/5000000000 : ℝ)|=(1592162069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1232_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37808179/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (389/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13737/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (1053/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1053 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1053*1^256 ≤ 0^256*1^1053 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1053 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1053/256 : ℝ) ≤ (2307601559062980153/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1053 ≤ (2307601559062980153/100000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1053*100000000000000000000^256 ≤ 2307601559062980153^256*5^1053 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2307601559062980153 100000000000000000000 1053 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2307601559062980153/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1053/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1053 := by
      have hnat : (1 : ℕ)^256*1^1053 ≤ 1^1053*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1053 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (102307601559062980153/100000000000000000000 : ℝ) ≤ (251390445570163/250000000000000 : ℝ) ^ (1053/256 : ℝ) := by
    have hpowers : (102307601559062980153/100000000000000000000 : ℝ)^256 ≤ (251390445570163/250000000000000 : ℝ)^1053 := by
      have hnat : (102307601559062980153 : ℕ)^256*250000000000000^1053 ≤ 251390445570163^1053*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102307601559062980153 100000000000000000000 251390445570163 250000000000000 256 1053 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (251390445570163/250000000000000 : ℝ)) (X := (102307601559062980153/100000000000000000000 : ℝ)) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (52307601559062980153/50000000000000000000 : ℝ) ≤ (126390445570163/125000000000000 : ℝ) ^ (1053/256 : ℝ) := by
    have hpowers : (52307601559062980153/50000000000000000000 : ℝ)^256 ≤ (126390445570163/125000000000000 : ℝ)^1053 := by
      have hnat : (52307601559062980153 : ℕ)^256*125000000000000^1053 ≤ 126390445570163^1053*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52307601559062980153 50000000000000000000 126390445570163 125000000000000 256 1053 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (126390445570163/125000000000000 : ℝ)) (X := (52307601559062980153/50000000000000000000 : ℝ)) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1390445570163/100000000000000 : ℝ)*(0 : ℝ))^(1053/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(1390445570163/100000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2307601559062980153/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1390445570163/100000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1053/256 : ℝ) := by
    rw [show (1 : ℝ)+(1390445570163/100000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(251390445570163/250000000000000 : ℝ) by norm_num, show 1+(2307601559062980153/100000000000000000000 : ℝ)+(0 : ℝ)=(102307601559062980153/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2307601559062980153/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1390445570163/100000000000000 : ℝ)*(2/5 : ℝ))^(1053/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(1390445570163/100000000000000 : ℝ)*(2/5 : ℝ)=(126390445570163/125000000000000 : ℝ) by norm_num, show 1+2*(2307601559062980153/100000000000000000000 : ℝ)=(52307601559062980153/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1390445570163/100000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1053/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1390445570163/100000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1390445570163/100000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1053/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1390445570163/100000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1390445570163/100000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1053/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1390445570163/100000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-465912397/2500000000 : ℝ)*X 0 0+(6033761977/10000000000 : ℝ)*X 0 1+(958349639/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2755861439/5000000000 : ℝ)*X 1 0+(-514789797/2000000000 : ℝ)*X 1 1+(958349629/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1102344563/2000000000 : ℝ)*X 2 0+(4791748213/10000000000 : ℝ)*X 2 1+(-1286974491/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2096904031/5000000000 : ℝ)*X 0 0+(1558635157/5000000000 : ℝ)*X 0 1+(901107/1600000 : ℝ)*X 0 2+(2096904031/5000000000 : ℝ)*X 1 0+(1558635157/5000000000 : ℝ)*X 1 1+(901107/1600000 : ℝ)*X 1 2+(2096904031/5000000000 : ℝ)*X 2 0+(1558635157/5000000000 : ℝ)*X 2 1+(901107/1600000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1868535571/10000000000 : ℝ)*X 0 0+(964747841/2000000000 : ℝ)*X 0 1+(6000640567/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2586915527/5000000000 : ℝ)*X 1 0+(-273010899/2000000000 : ℝ)*X 1 1+(6000642729/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5173831863/10000000000 : ℝ)*X 2 0+(1200128213/2000000000 : ℝ)*X 2 1+(-341263983/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4203700763/10000000000 : ℝ)*X 0 0+(2783576447/5000000000 : ℝ)*X 0 1+(1592162069/5000000000 : ℝ)*X 0 2+(4203700763/10000000000 : ℝ)*X 1 0+(2783576447/5000000000 : ℝ)*X 1 1+(1592162069/5000000000 : ℝ)*X 1 2+(4203700763/10000000000 : ℝ)*X 2 0+(2783576447/5000000000 : ℝ)*X 2 1+(1592162069/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (400568019647686276977/62500000000000000000000000 : ℝ) := by norm_num
    linear_combination (7737047/10000000000000 : ℝ)*(base1) + (156413743/10000000000000 : ℝ)*(base19) + (724877709/50000000000000 : ℝ)*(base23) + (105178987/100000000000000 : ℝ)*(base24) + (176502817/50000000000000 : ℝ)*(upper3) + (15035340508939/2500000000000 : ℝ)*(major0) + (15035340508939/2500000000000 : ℝ)*(major1) + (15035340508939/2500000000000 : ℝ)*(major2) + (161029868373231/20000000000000 : ℝ)*(sp0) + (805151179053287/100000000000000 : ℝ)*(sp1) + (100643898532039/12500000000000 : ℝ)*(sp2) + (15906859809351/4000000000000 : ℝ)*(sp3) + (434836879/12500000000000 : ℝ)*(sp4) + (2711283879/100000000000000 : ℝ)*(sp7) + (99418570972031/25000000000000 : ℝ)*(f.failure) + (805152743190717/100000000000000 : ℝ)*(f.sum) + (9119323841/62500000000000000000000000 : ℝ)*base65 + (266610894307/250000000000000000000000000 : ℝ)*base67 + (791335793193/250000000000000000000000000 : ℝ)*base70 + (304195241193/250000000000000000000000000 : ℝ)*base72 + (28566812983/31250000000000000000000000 : ℝ)*base73 + (347414395307/250000000000000000000000000 : ℝ)*base75 + (51015185307/250000000000000000000000000 : ℝ)*base77 + (46552220943/250000000000000000000000000 : ℝ)*base80 + (873831583943/125000000000000000000000000 : ℝ)*base82 + (2041549/625000000000000000000 : ℝ)*base89 + (2041549/625000000000000000000 : ℝ)*base91 + (2041549/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4764492042355234371657/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26926919/25000000000000 : ℝ)*(base1) + (1922687633/100000000000000 : ℝ)*(base19) + (2052372249/100000000000000 : ℝ)*(base23) + (384140437/100000000000000 : ℝ)*(upper3) + (16106503/20000000000000 : ℝ)*(upper5) + (19833709277397/3125000000000 : ℝ)*(major0) + (19833709277397/3125000000000 : ℝ)*(major1) + (19833709277397/3125000000000 : ℝ)*(major2) + (4168120607/100000000000000 : ℝ)*(sp1) + (2059754949/50000000000000 : ℝ)*(sp2) + (849687010871941/100000000000000 : ℝ)*(sp4) + (106210101544503/12500000000000 : ℝ)*(sp5) + (424840365641059/50000000000000 : ℝ)*(sp6) + (209835064387609/50000000000000 : ℝ)*(sp7) + (83934047296579/20000000000000 : ℝ)*(f.failure) + (169937380632853/20000000000000 : ℝ)*(f.sum) + (643962758469/625000000000000000000000000 : ℝ)*base65 + (5466417861703/625000000000000000000000000 : ℝ)*base68 + (253864632953/625000000000000000000000000 : ℝ)*base70 + (15108861789/312500000000000000000000000 : ℝ)*base72 + (1255812925281/625000000000000000000000000 : ℝ)*base74 + (2060608514547/625000000000000000000000000 : ℝ)*base75 + (209646939041/78125000000000000000000000 : ℝ)*base78 + (1643253005539/312500000000000000000000000 : ℝ)*base80 + (639367838211/156250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (4919641/500000000000000000000 : ℝ)*base89 + (4919641/500000000000000000000 : ℝ)*base91 + (4919641/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1232_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37808179/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (389/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13737/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1232_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1232_s1_0 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2061784511/10000000000 : ℝ)*x 0 + (354883263/625000000 : ℝ)*x 1 + (1255137323/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2061784511/10000000000 : ℝ)^8425 ≤ (2483359825553/20000000000000 : ℝ)^6377 := by
    have hnat : (2061784511 : ℕ)^8425*20000000000000^6377 ≤ 2483359825553^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061784511 10000000000 2483359825553 20000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (354883263/625000000 : ℝ)^8425 ≤ (47344286642571/100000000000000 : ℝ)^6377 := by
    have hnat : (354883263 : ℕ)^8425*100000000000000^6377 ≤ 47344286642571^6377*625000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354883263 625000000 47344286642571 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1255137323/2500000000 : ℝ)^8425 ≤ (40238914210859/100000000000000 : ℝ)^6377 := by
    have hnat : (1255137323 : ℕ)^8425*100000000000000^6377 ≤ 40238914210859^6377*2500000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255137323 2500000000 40238914210859 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2061784511/10000000000 : ℝ), (354883263/625000000 : ℝ), (1255137323/2500000000 : ℝ)] ![(2483359825553/20000000000000 : ℝ), (47344286642571/100000000000000 : ℝ), (40238914210859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2061784511/10000000000 : ℝ)|^8425 ≤ (2483359825553/20000000000000 : ℝ)^6377
        have hw : |(-2061784511/10000000000 : ℝ)|=(2061784511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(354883263/625000000 : ℝ)|^8425 ≤ (47344286642571/100000000000000 : ℝ)^6377
        have hw : |(354883263/625000000 : ℝ)|=(354883263/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1255137323/2500000000 : ℝ)|^8425 ≤ (40238914210859/100000000000000 : ℝ)^6377
        have hw : |(1255137323/2500000000 : ℝ)|=(1255137323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s1_1 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (338387753/625000000 : ℝ)*x 0 + (-1207535039/5000000000 : ℝ)*x 1 + (5020549369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338387753/625000000 : ℝ)^8425 ≤ (86833677849/195312500000 : ℝ)^6377 := by
    have hnat : (338387753 : ℕ)^8425*195312500000^6377 ≤ 86833677849^6377*625000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338387753 625000000 86833677849 195312500000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1207535039/5000000000 : ℝ)^8425 ≤ (15302241891813/100000000000000 : ℝ)^6377 := by
    have hnat : (1207535039 : ℕ)^8425*100000000000000^6377 ≤ 15302241891813^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207535039 5000000000 15302241891813 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5020549369/10000000000 : ℝ)^8425 ≤ (201194575131/500000000000 : ℝ)^6377 := by
    have hnat : (5020549369 : ℕ)^8425*500000000000^6377 ≤ 201194575131^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5020549369 10000000000 201194575131 500000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(338387753/625000000 : ℝ), (-1207535039/5000000000 : ℝ), (5020549369/10000000000 : ℝ)] ![(86833677849/195312500000 : ℝ), (15302241891813/100000000000000 : ℝ), (201194575131/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(338387753/625000000 : ℝ)|^8425 ≤ (86833677849/195312500000 : ℝ)^6377
        have hw : |(338387753/625000000 : ℝ)|=(338387753/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1207535039/5000000000 : ℝ)|^8425 ≤ (15302241891813/100000000000000 : ℝ)^6377
        have hw : |(-1207535039/5000000000 : ℝ)|=(1207535039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5020549369/10000000000 : ℝ)|^8425 ≤ (201194575131/500000000000 : ℝ)^6377
        have hw : |(5020549369/10000000000 : ℝ)|=(5020549369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s1_2 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (43313633/80000000 : ℝ)*x 0 + (5020549323/10000000000 : ℝ)*x 1 + (-2415070037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43313633/80000000 : ℝ)^8425 ≤ (44458843894037/100000000000000 : ℝ)^6377 := by
    have hnat : (43313633 : ℕ)^8425*100000000000000^6377 ≤ 44458843894037^6377*80000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43313633 80000000 44458843894037 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5020549323/10000000000 : ℝ)^8425 ≤ (20119457269557/50000000000000 : ℝ)^6377 := by
    have hnat : (5020549323 : ℕ)^8425*50000000000000^6377 ≤ 20119457269557^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5020549323 10000000000 20119457269557 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2415070037/10000000000 : ℝ)^8425 ≤ (15302241548601/100000000000000 : ℝ)^6377 := by
    have hnat : (2415070037 : ℕ)^8425*100000000000000^6377 ≤ 15302241548601^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2415070037 10000000000 15302241548601 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43313633/80000000 : ℝ), (5020549323/10000000000 : ℝ), (-2415070037/10000000000 : ℝ)] ![(44458843894037/100000000000000 : ℝ), (20119457269557/50000000000000 : ℝ), (15302241548601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43313633/80000000 : ℝ)|^8425 ≤ (44458843894037/100000000000000 : ℝ)^6377
        have hw : |(43313633/80000000 : ℝ)|=(43313633/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5020549323/10000000000 : ℝ)|^8425 ≤ (20119457269557/50000000000000 : ℝ)^6377
        have hw : |(5020549323/10000000000 : ℝ)|=(5020549323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2415070037/10000000000 : ℝ)|^8425 ≤ (15302241548601/100000000000000 : ℝ)^6377
        have hw : |(-2415070037/10000000000 : ℝ)|=(2415070037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s1_3 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5387151/12500000 : ℝ)*x 0 + (3693623471/10000000000 : ℝ)*x 1 + (5025002029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5387151/12500000 : ℝ)^8425 ≤ (16444511010243/50000000000000 : ℝ)^6377 := by
    have hnat : (5387151 : ℕ)^8425*50000000000000^6377 ≤ 16444511010243^6377*12500000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387151 12500000 16444511010243 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3693623471/10000000000 : ℝ)^8425 ≤ (67062269279/250000000000 : ℝ)^6377 := by
    have hnat : (3693623471 : ℕ)^8425*250000000000^6377 ≤ 67062269279^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3693623471 10000000000 67062269279 250000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5025002029/10000000000 : ℝ)^8425 ≤ (10071517564379/25000000000000 : ℝ)^6377 := by
    have hnat : (5025002029 : ℕ)^8425*25000000000000^6377 ≤ 10071517564379^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5025002029 10000000000 10071517564379 25000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5387151/12500000 : ℝ), (3693623471/10000000000 : ℝ), (5025002029/10000000000 : ℝ)] ![(16444511010243/50000000000000 : ℝ), (67062269279/250000000000 : ℝ), (10071517564379/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5387151/12500000 : ℝ)|^8425 ≤ (16444511010243/50000000000000 : ℝ)^6377
        have hw : |(5387151/12500000 : ℝ)|=(5387151/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3693623471/10000000000 : ℝ)|^8425 ≤ (67062269279/250000000000 : ℝ)^6377
        have hw : |(3693623471/10000000000 : ℝ)|=(3693623471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5025002029/10000000000 : ℝ)|^8425 ≤ (10071517564379/25000000000000 : ℝ)^6377
        have hw : |(5025002029/10000000000 : ℝ)|=(5025002029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s1_4 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1031236771/5000000000 : ℝ)*x 0 + (5029221587/10000000000 : ℝ)*x 1 + (5669293811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1031236771/5000000000 : ℝ)^8425 ≤ (12422281669423/100000000000000 : ℝ)^6377 := by
    have hnat : (1031236771 : ℕ)^8425*100000000000000^6377 ≤ 12422281669423^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031236771 5000000000 12422281669423 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5029221587/10000000000 : ℝ)^8425 ≤ (40330769242601/100000000000000 : ℝ)^6377 := by
    have hnat : (5029221587 : ℕ)^8425*100000000000000^6377 ≤ 40330769242601^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5029221587 10000000000 40330769242601 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5669293811/10000000000 : ℝ)^8425 ≤ (4724694907901/10000000000000 : ℝ)^6377 := by
    have hnat : (5669293811 : ℕ)^8425*10000000000000^6377 ≤ 4724694907901^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5669293811 10000000000 4724694907901 10000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1031236771/5000000000 : ℝ), (5029221587/10000000000 : ℝ), (5669293811/10000000000 : ℝ)] ![(12422281669423/100000000000000 : ℝ), (40330769242601/100000000000000 : ℝ), (4724694907901/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1031236771/5000000000 : ℝ)|^8425 ≤ (12422281669423/100000000000000 : ℝ)^6377
        have hw : |(-1031236771/5000000000 : ℝ)|=(1031236771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5029221587/10000000000 : ℝ)|^8425 ≤ (40330769242601/100000000000000 : ℝ)^6377
        have hw : |(5029221587/10000000000 : ℝ)|=(5029221587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5669293811/10000000000 : ℝ)|^8425 ≤ (4724694907901/10000000000000 : ℝ)^6377
        have hw : |(5669293811/10000000000 : ℝ)|=(5669293811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s1_5 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5244871237/10000000000 : ℝ)*x 0 + (-883162499/5000000000 : ℝ)*x 1 + (566929409/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5244871237/10000000000 : ℝ)^8425 ≤ (5328887134559/12500000000000 : ℝ)^6377 := by
    have hnat : (5244871237 : ℕ)^8425*12500000000000^6377 ≤ 5328887134559^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244871237 10000000000 5328887134559 12500000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (883162499/5000000000 : ℝ)^8425 ≤ (2024390153201/20000000000000 : ℝ)^6377 := by
    have hnat : (883162499 : ℕ)^8425*20000000000000^6377 ≤ 2024390153201^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883162499 5000000000 2024390153201 20000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (566929409/1000000000 : ℝ)^8425 ≤ (23623476075439/50000000000000 : ℝ)^6377 := by
    have hnat : (566929409 : ℕ)^8425*50000000000000^6377 ≤ 23623476075439^6377*1000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566929409 1000000000 23623476075439 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5244871237/10000000000 : ℝ), (-883162499/5000000000 : ℝ), (566929409/1000000000 : ℝ)] ![(5328887134559/12500000000000 : ℝ), (2024390153201/20000000000000 : ℝ), (23623476075439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5244871237/10000000000 : ℝ)|^8425 ≤ (5328887134559/12500000000000 : ℝ)^6377
        have hw : |(5244871237/10000000000 : ℝ)|=(5244871237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-883162499/5000000000 : ℝ)|^8425 ≤ (2024390153201/20000000000000 : ℝ)^6377
        have hw : |(-883162499/5000000000 : ℝ)|=(883162499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(566929409/1000000000 : ℝ)|^8425 ≤ (23623476075439/50000000000000 : ℝ)^6377
        have hw : |(566929409/1000000000 : ℝ)|=(566929409/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s1_6 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5244871553/10000000000 : ℝ)*x 0 + (5669294843/10000000000 : ℝ)*x 1 + (-883161727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5244871553/10000000000 : ℝ)^8425 ≤ (852622009397/2000000000000 : ℝ)^6377 := by
    have hnat : (5244871553 : ℕ)^8425*2000000000000^6377 ≤ 852622009397^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244871553 10000000000 852622009397 2000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5669294843/10000000000 : ℝ)^8425 ≤ (47246960441617/100000000000000 : ℝ)^6377 := by
    have hnat : (5669294843 : ℕ)^8425*100000000000000^6377 ≤ 47246960441617^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5669294843 10000000000 47246960441617 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (883161727/5000000000 : ℝ)^8425 ≤ (2530484769137/25000000000000 : ℝ)^6377 := by
    have hnat : (883161727 : ℕ)^8425*25000000000000^6377 ≤ 2530484769137^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883161727 5000000000 2530484769137 25000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5244871553/10000000000 : ℝ), (5669294843/10000000000 : ℝ), (-883161727/5000000000 : ℝ)] ![(852622009397/2000000000000 : ℝ), (47246960441617/100000000000000 : ℝ), (2530484769137/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5244871553/10000000000 : ℝ)|^8425 ≤ (852622009397/2000000000000 : ℝ)^6377
        have hw : |(5244871553/10000000000 : ℝ)|=(5244871553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5669294843/10000000000 : ℝ)|^8425 ≤ (47246960441617/100000000000000 : ℝ)^6377
        have hw : |(5669294843/10000000000 : ℝ)|=(5669294843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-883161727/5000000000 : ℝ)|^8425 ≤ (2530484769137/25000000000000 : ℝ)^6377
        have hw : |(-883161727/5000000000 : ℝ)|=(883161727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s1_7 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2155557061/5000000000 : ℝ)*x 0 + (2503722201/5000000000 : ℝ)*x 1 + (3711516531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155557061/5000000000 : ℝ)^8425 ≤ (32903070501039/100000000000000 : ℝ)^6377 := by
    have hnat : (2155557061 : ℕ)^8425*100000000000000^6377 ≤ 32903070501039^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155557061 5000000000 32903070501039 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2503722201/5000000000 : ℝ)^8425 ≤ (2506262924071/6250000000000 : ℝ)^6377 := by
    have hnat : (2503722201 : ℕ)^8425*6250000000000^6377 ≤ 2506262924071^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2503722201 5000000000 2506262924071 6250000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3711516531/10000000000 : ℝ)^8425 ≤ (26996722703779/100000000000000 : ℝ)^6377 := by
    have hnat : (3711516531 : ℕ)^8425*100000000000000^6377 ≤ 26996722703779^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3711516531 10000000000 26996722703779 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155557061/5000000000 : ℝ), (2503722201/5000000000 : ℝ), (3711516531/10000000000 : ℝ)] ![(32903070501039/100000000000000 : ℝ), (2506262924071/6250000000000 : ℝ), (26996722703779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155557061/5000000000 : ℝ)|^8425 ≤ (32903070501039/100000000000000 : ℝ)^6377
        have hw : |(2155557061/5000000000 : ℝ)|=(2155557061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2503722201/5000000000 : ℝ)|^8425 ≤ (2506262924071/6250000000000 : ℝ)^6377
        have hw : |(2503722201/5000000000 : ℝ)|=(2503722201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3711516531/10000000000 : ℝ)|^8425 ≤ (26996722703779/100000000000000 : ℝ)^6377
        have hw : |(3711516531/10000000000 : ℝ)|=(3711516531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s1_8 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (3835001/10000000000 : ℝ)*x 0 + (686408629/1250000000 : ℝ)*x 1 + (3167012311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3835001/10000000000 : ℝ)^8425 ≤ (1533195729/50000000000000 : ℝ)^6377 := by
    have hnat : (3835001 : ℕ)^8425*50000000000000^6377 ≤ 1533195729^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3835001 10000000000 1533195729 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (686408629/1250000000 : ℝ)^8425 ≤ (45296801453077/100000000000000 : ℝ)^6377 := by
    have hnat : (686408629 : ℕ)^8425*100000000000000^6377 ≤ 45296801453077^6377*1250000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686408629 1250000000 45296801453077 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3167012311/5000000000 : ℝ)^8425 ≤ (54700132145297/100000000000000 : ℝ)^6377 := by
    have hnat : (3167012311 : ℕ)^8425*100000000000000^6377 ≤ 54700132145297^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3167012311 5000000000 54700132145297 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3835001/10000000000 : ℝ), (686408629/1250000000 : ℝ), (3167012311/5000000000 : ℝ)] ![(1533195729/50000000000000 : ℝ), (45296801453077/100000000000000 : ℝ), (54700132145297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3835001/10000000000 : ℝ)|^8425 ≤ (1533195729/50000000000000 : ℝ)^6377
        have hw : |(3835001/10000000000 : ℝ)|=(3835001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(686408629/1250000000 : ℝ)|^8425 ≤ (45296801453077/100000000000000 : ℝ)^6377
        have hw : |(686408629/1250000000 : ℝ)|=(686408629/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3167012311/5000000000 : ℝ)|^8425 ≤ (54700132145297/100000000000000 : ℝ)^6377
        have hw : |(3167012311/5000000000 : ℝ)|=(3167012311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s1_9 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (998340321/10000000000 : ℝ)*x 0 + (-4351485933/10000000000 : ℝ)*x 1 + (6957710499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (998340321/10000000000 : ℝ)^8425 ≤ (2381566932267/50000000000000 : ℝ)^6377 := by
    have hnat : (998340321 : ℕ)^8425*50000000000000^6377 ≤ 2381566932267^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998340321 10000000000 2381566932267 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4351485933/10000000000 : ℝ)^8425 ≤ (33310760286869/100000000000000 : ℝ)^6377 := by
    have hnat : (4351485933 : ℕ)^8425*100000000000000^6377 ≤ 33310760286869^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351485933 10000000000 33310760286869 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6957710499/10000000000 : ℝ)^8425 ≤ (30963052918353/50000000000000 : ℝ)^6377 := by
    have hnat : (6957710499 : ℕ)^8425*50000000000000^6377 ≤ 30963052918353^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6957710499 10000000000 30963052918353 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(998340321/10000000000 : ℝ), (-4351485933/10000000000 : ℝ), (6957710499/10000000000 : ℝ)] ![(2381566932267/50000000000000 : ℝ), (33310760286869/100000000000000 : ℝ), (30963052918353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(998340321/10000000000 : ℝ)|^8425 ≤ (2381566932267/50000000000000 : ℝ)^6377
        have hw : |(998340321/10000000000 : ℝ)|=(998340321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4351485933/10000000000 : ℝ)|^8425 ≤ (33310760286869/100000000000000 : ℝ)^6377
        have hw : |(-4351485933/10000000000 : ℝ)|=(4351485933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6957710499/10000000000 : ℝ)|^8425 ≤ (30963052918353/50000000000000 : ℝ)^6377
        have hw : |(6957710499/10000000000 : ℝ)|=(6957710499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s1_10 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (998342709/10000000000 : ℝ)*x 0 + (1391543061/2000000000 : ℝ)*x 1 + (-4351478857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (998342709/10000000000 : ℝ)^8425 ≤ (476314891681/10000000000000 : ℝ)^6377 := by
    have hnat : (998342709 : ℕ)^8425*10000000000000^6377 ≤ 476314891681^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998342709 10000000000 476314891681 10000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1391543061/2000000000 : ℝ)^8425 ≤ (61926162349233/100000000000000 : ℝ)^6377 := by
    have hnat : (1391543061 : ℕ)^8425*100000000000000^6377 ≤ 61926162349233^6377*2000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1391543061 2000000000 61926162349233 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4351478857/10000000000 : ℝ)^8425 ≤ (3331068872393/10000000000000 : ℝ)^6377 := by
    have hnat : (4351478857 : ℕ)^8425*10000000000000^6377 ≤ 3331068872393^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351478857 10000000000 3331068872393 10000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(998342709/10000000000 : ℝ), (1391543061/2000000000 : ℝ), (-4351478857/10000000000 : ℝ)] ![(476314891681/10000000000000 : ℝ), (61926162349233/100000000000000 : ℝ), (3331068872393/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(998342709/10000000000 : ℝ)|^8425 ≤ (476314891681/10000000000000 : ℝ)^6377
        have hw : |(998342709/10000000000 : ℝ)|=(998342709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1391543061/2000000000 : ℝ)|^8425 ≤ (61926162349233/100000000000000 : ℝ)^6377
        have hw : |(1391543061/2000000000 : ℝ)|=(1391543061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4351478857/10000000000 : ℝ)|^8425 ≤ (3331068872393/10000000000000 : ℝ)^6377
        have hw : |(-4351478857/10000000000 : ℝ)|=(4351478857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s1_11 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (381116039/2000000000 : ℝ)*x 0 + (723756457/1250000000 : ℝ)*x 1 + (1254917273/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (381116039/2000000000 : ℝ)^8425 ≤ (5594676682551/50000000000000 : ℝ)^6377 := by
    have hnat : (381116039 : ℕ)^8425*50000000000000^6377 ≤ 5594676682551^6377*2000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381116039 2000000000 5594676682551 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (723756457/1250000000 : ℝ)^8425 ≤ (48581052450547/100000000000000 : ℝ)^6377 := by
    have hnat : (723756457 : ℕ)^8425*100000000000000^6377 ≤ 48581052450547^6377*1250000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      723756457 1250000000 48581052450547 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1254917273/2500000000 : ℝ)^8425 ≤ (40229594173617/100000000000000 : ℝ)^6377 := by
    have hnat : (1254917273 : ℕ)^8425*100000000000000^6377 ≤ 40229594173617^6377*2500000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1254917273 2500000000 40229594173617 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(381116039/2000000000 : ℝ), (723756457/1250000000 : ℝ), (1254917273/2500000000 : ℝ)] ![(5594676682551/50000000000000 : ℝ), (48581052450547/100000000000000 : ℝ), (40229594173617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(381116039/2000000000 : ℝ)|^8425 ≤ (5594676682551/50000000000000 : ℝ)^6377
        have hw : |(381116039/2000000000 : ℝ)|=(381116039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(723756457/1250000000 : ℝ)|^8425 ≤ (48581052450547/100000000000000 : ℝ)^6377
        have hw : |(723756457/1250000000 : ℝ)|=(723756457/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1254917273/2500000000 : ℝ)|^8425 ≤ (40229594173617/100000000000000 : ℝ)^6377
        have hw : |(1254917273/2500000000 : ℝ)|=(1254917273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1232_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37808179/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (389/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (3069/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20041/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13737/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (389/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13737/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (389/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13737/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (389/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13737/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (389/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13737/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (389/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13737/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (389/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (389/50000 : ℝ) ^ (1053/256 : ℝ) ≤ (105675892587/50000000000000000000 : ℝ) := by
    have hpowers : (389/50000 : ℝ)^1053 ≤ (105675892587/50000000000000000000 : ℝ)^256 := by
      have hnat : (389 : ℕ)^1053*50000000000000000000^256 ≤ 105675892587^256*50000^1053 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        389 50000 105675892587 50000000000000000000 1053 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (389/50000 : ℝ)) (X := (105675892587/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hpowhi : (13737/50000 : ℝ) ^ (1053/256 : ℝ) ≤ (123046128901553211/25000000000000000000 : ℝ) := by
    have hpowers : (13737/50000 : ℝ)^1053 ≤ (123046128901553211/25000000000000000000 : ℝ)^256 := by
      have hnat : (13737 : ℕ)^1053*25000000000000000000^256 ≤ 123046128901553211^256*50000^1053 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13737 50000 123046128901553211 25000000000000000000 1053 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13737/50000 : ℝ)) (X := (123046128901553211/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000105675892587/25000000000000000000 : ℝ) ≤ (2000000002055311/2000000000000000 : ℝ) ^ (1053/256 : ℝ) := by
    have hpowers : (25000000105675892587/25000000000000000000 : ℝ)^256 ≤ (2000000002055311/2000000000000000 : ℝ)^1053 := by
      have hnat : (25000000105675892587 : ℕ)^256*2000000000000000^1053 ≤ 2000000002055311^1053*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000105675892587 25000000000000000000 2000000002055311 2000000000000000 256 1053 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000002055311/2000000000000000 : ℝ)) (X := (25000000105675892587/25000000000000000000 : ℝ)) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50246092363478999009/50000000000000000000 : ℝ) ≤ (10011943520742319/10000000000000000 : ℝ) ^ (1053/256 : ℝ) := by
    have hpowers : (50246092363478999009/50000000000000000000 : ℝ)^256 ≤ (10011943520742319/10000000000000000 : ℝ)^1053 := by
      have hnat : (50246092363478999009 : ℕ)^256*10000000000000000^1053 ≤ 10011943520742319^1053*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50246092363478999009 50000000000000000000 10011943520742319 10000000000000000 256 1053 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011943520742319/10000000000000000 : ℝ)) (X := (50246092363478999009/50000000000000000000 : ℝ)) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12623046128901553211/12500000000000000000 : ℝ) ≤ (10023887031208083/10000000000000000 : ℝ) ^ (1053/256 : ℝ) := by
    have hpowers : (12623046128901553211/12500000000000000000 : ℝ)^256 ≤ (10023887031208083/10000000000000000 : ℝ)^1053 := by
      have hnat : (12623046128901553211 : ℕ)^256*10000000000000000^1053 ≤ 10023887031208083^1053*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12623046128901553211 12500000000000000000 10023887031208083 10000000000000000 256 1053 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10023887031208083/10000000000000000 : ℝ)) (X := (12623046128901553211/12500000000000000000 : ℝ)) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(105675892587/50000000000000000000 : ℝ) ≤ ((33367677021507272937/33370000000000000000 : ℝ)+2*(2985877616441/667400000000000 : ℝ)*(389/50000 : ℝ))^(1053/256 : ℝ) := by
    rw [show (33367677021507272937/33370000000000000000 : ℝ)+2*(2985877616441/667400000000000 : ℝ)*(389/50000 : ℝ)=(2000000002055311/2000000000000000 : ℝ) by norm_num, show 1+2*(105675892587/50000000000000000000 : ℝ)=(25000000105675892587/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(123046128901553211/25000000000000000000 : ℝ)+(105675892587/50000000000000000000 : ℝ) ≤ ((33367677021507272937/33370000000000000000 : ℝ)+(2985877616441/667400000000000 : ℝ)*((13737/50000 : ℝ)+(389/50000 : ℝ)))^(1053/256 : ℝ) := by
    rw [show (33367677021507272937/33370000000000000000 : ℝ)+(2985877616441/667400000000000 : ℝ)*((13737/50000 : ℝ)+(389/50000 : ℝ))=(10011943520742319/10000000000000000 : ℝ) by norm_num, show 1+(123046128901553211/25000000000000000000 : ℝ)+(105675892587/50000000000000000000 : ℝ)=(50246092363478999009/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(123046128901553211/25000000000000000000 : ℝ) ≤ ((33367677021507272937/33370000000000000000 : ℝ)+2*(2985877616441/667400000000000 : ℝ)*(13737/50000 : ℝ))^(1053/256 : ℝ) := by
    rw [show (33367677021507272937/33370000000000000000 : ℝ)+2*(2985877616441/667400000000000 : ℝ)*(13737/50000 : ℝ)=(10023887031208083/10000000000000000 : ℝ) by norm_num, show 1+2*(123046128901553211/25000000000000000000 : ℝ)=(12623046128901553211/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33367677021507272937/33370000000000000000 : ℝ)*(X 1 0+X 2 0)+(2985877616441/667400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1053/256 : ℝ)) (lo := (389/50000 : ℝ)) (hi := (13737/50000 : ℝ)) (c := (33367677021507272937/33370000000000000000 : ℝ)) (alpha := (2985877616441/667400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33367677021507272937/33370000000000000000 : ℝ)*(X 0 1+X 2 1)+(2985877616441/667400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1053/256 : ℝ)) (lo := (389/50000 : ℝ)) (hi := (13737/50000 : ℝ)) (c := (33367677021507272937/33370000000000000000 : ℝ)) (alpha := (2985877616441/667400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33367677021507272937/33370000000000000000 : ℝ)*(X 0 2+X 1 2)+(2985877616441/667400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1053/256 : ℝ)) (lo := (389/50000 : ℝ)) (hi := (13737/50000 : ℝ)) (c := (33367677021507272937/33370000000000000000 : ℝ)) (alpha := (2985877616441/667400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2061784511/10000000000 : ℝ)*X 0 0+(354883263/625000000 : ℝ)*X 0 1+(1255137323/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((338387753/625000000 : ℝ)*X 1 0+(-1207535039/5000000000 : ℝ)*X 1 1+(5020549369/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((43313633/80000000 : ℝ)*X 2 0+(5020549323/10000000000 : ℝ)*X 2 1+(-2415070037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5387151/12500000 : ℝ)*X 0 0+(3693623471/10000000000 : ℝ)*X 0 1+(5025002029/10000000000 : ℝ)*X 0 2+(5387151/12500000 : ℝ)*X 1 0+(3693623471/10000000000 : ℝ)*X 1 1+(5025002029/10000000000 : ℝ)*X 1 2+(5387151/12500000 : ℝ)*X 2 0+(3693623471/10000000000 : ℝ)*X 2 1+(5025002029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1031236771/5000000000 : ℝ)*X 0 0+(5029221587/10000000000 : ℝ)*X 0 1+(5669293811/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5244871237/10000000000 : ℝ)*X 1 0+(-883162499/5000000000 : ℝ)*X 1 1+(566929409/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5244871553/10000000000 : ℝ)*X 2 0+(5669294843/10000000000 : ℝ)*X 2 1+(-883161727/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2155557061/5000000000 : ℝ)*X 0 0+(2503722201/5000000000 : ℝ)*X 0 1+(3711516531/10000000000 : ℝ)*X 0 2+(2155557061/5000000000 : ℝ)*X 1 0+(2503722201/5000000000 : ℝ)*X 1 1+(3711516531/10000000000 : ℝ)*X 1 2+(2155557061/5000000000 : ℝ)*X 2 0+(2503722201/5000000000 : ℝ)*X 2 1+(3711516531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((3835001/10000000000 : ℝ)*X 0 0+(686408629/1250000000 : ℝ)*X 0 1+(3167012311/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((998340321/10000000000 : ℝ)*X 1 0+(-4351485933/10000000000 : ℝ)*X 1 1+(6957710499/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((998342709/10000000000 : ℝ)*X 2 0+(1391543061/2000000000 : ℝ)*X 2 1+(-4351478857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((381116039/2000000000 : ℝ)*X 0 0+(723756457/1250000000 : ℝ)*X 0 1+(1254917273/2500000000 : ℝ)*X 0 2+(381116039/2000000000 : ℝ)*X 1 0+(723756457/1250000000 : ℝ)*X 1 1+(1254917273/2500000000 : ℝ)*X 1 2+(381116039/2000000000 : ℝ)*X 2 0+(723756457/1250000000 : ℝ)*X 2 1+(1254917273/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (491877428036424746678398047/35500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1135914685617181/100000000000000 : ℝ)*(major0) + (1135914685617181/100000000000000 : ℝ)*(major1) + (1135914685617181/100000000000000 : ℝ)*(major2) + (1520723128126663/100000000000000 : ℝ)*(sp0) + (95045219216501/6250000000000 : ℝ)*(sp1) + (1520723475334511/100000000000000 : ℝ)*(sp2) + (751102132423767/100000000000000 : ℝ)*(sp3) + (1936951/390625000000 : ℝ)*(sp4) + (366294569/50000000000000 : ℝ)*(sp5) + (738424831/100000000000000 : ℝ)*(sp6) + (1479507869/100000000000000 : ℝ)*(sp8) + (172688167/20000000000000 : ℝ)*(sp9) + (889734647/100000000000000 : ℝ)*(sp10) + (1673459863/100000000000000 : ℝ)*(sp11) + (75110380588363/10000000000000 : ℝ)*(f.failure) + (380181275873497/25000000000000 : ℝ)*(f.sum) + (1151654747947/710000000000000000000000000 : ℝ)*base66 + (179574317543650651/71000000000000000000000000000000 : ℝ)*base67 + (242511713743650651/71000000000000000000000000000000 : ℝ)*base69 + (116386758168650651/71000000000000000000000000000000 : ℝ)*base71 + (103907427737/710000000000000000000000000 : ℝ)*base74 + (240222757445349349/71000000000000000000000000000000 : ℝ)*base76 + (68521353296650651/71000000000000000000000000000000 : ℝ)*base77 + (89838983583349349/71000000000000000000000000000000 : ℝ)*base80 + (814139328647/710000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1120977/250000000000000000000 : ℝ)*base89 + (1120977/250000000000000000000 : ℝ)*base91 + (1120977/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1659251310958289373444772569/834250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1166986709653421/100000000000000 : ℝ)*(major0) + (1166986709653421/100000000000000 : ℝ)*(major1) + (1166986709653421/100000000000000 : ℝ)*(major2) + (10416531/3125000000000 : ℝ)*(sp1) + (576286761/20000000000000 : ℝ)*(sp2) + (367512919/50000000000000 : ℝ)*(sp3) + (781161405197981/50000000000000 : ℝ)*(sp4) + (781161542063401/50000000000000 : ℝ)*(sp5) + (1562320318156527/100000000000000 : ℝ)*(sp6) + (771648622229451/100000000000000 : ℝ)*(sp7) + (901901469/100000000000000 : ℝ)*(sp8) + (147420819/50000000000000 : ℝ)*(sp9) + (512707099/100000000000000 : ℝ)*(sp10) + (28345699/10000000000000 : ℝ)*(sp11) + (771649640712279/100000000000000 : ℝ)*(f.failure) + (195290464037179/12500000000000 : ℝ)*(f.sum) + (52058496155029/33370000000000000000000000000 : ℝ)*base66 + (15562863145001817477/3337000000000000000000000000000000 : ℝ)*base67 + (14934667485724817477/3337000000000000000000000000000000 : ℝ)*base69 + (11299686076335817477/3337000000000000000000000000000000 : ℝ)*base71 + (25602655940519/33370000000000000000000000000 : ℝ)*base74 + (8455041890805182523/3337000000000000000000000000000000 : ℝ)*base76 + (22811088842552817477/3337000000000000000000000000000000 : ℝ)*base77 + (16559408910848817477/3337000000000000000000000000000000 : ℝ)*base79 + (68133240277829/33370000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (6929941/2500000000000000000000 : ℝ)*base89 + (6929941/2500000000000000000000 : ℝ)*base91 + (6929941/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1232_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37808179/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (389/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3069/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20041/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1232_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1232_s2_0 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2110335411/10000000000 : ℝ)*x 0 + (5494502957/10000000000 : ℝ)*x 1 + (1293306069/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2110335411/10000000000 : ℝ)^8425 ≤ (512181815421/4000000000000 : ℝ)^6377 := by
    have hnat : (2110335411 : ℕ)^8425*4000000000000^6377 ≤ 512181815421^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110335411 10000000000 512181815421 4000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5494502957/10000000000 : ℝ)^8425 ≤ (45332048222187/100000000000000 : ℝ)^6377 := by
    have hnat : (5494502957 : ℕ)^8425*100000000000000^6377 ≤ 45332048222187^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494502957 10000000000 45332048222187 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1293306069/2500000000 : ℝ)^8425 ≤ (41863406365057/100000000000000 : ℝ)^6377 := by
    have hnat : (1293306069 : ℕ)^8425*100000000000000^6377 ≤ 41863406365057^6377*2500000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293306069 2500000000 41863406365057 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2110335411/10000000000 : ℝ), (5494502957/10000000000 : ℝ), (1293306069/2500000000 : ℝ)] ![(512181815421/4000000000000 : ℝ), (45332048222187/100000000000000 : ℝ), (41863406365057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2110335411/10000000000 : ℝ)|^8425 ≤ (512181815421/4000000000000 : ℝ)^6377
        have hw : |(-2110335411/10000000000 : ℝ)|=(2110335411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5494502957/10000000000 : ℝ)|^8425 ≤ (45332048222187/100000000000000 : ℝ)^6377
        have hw : |(5494502957/10000000000 : ℝ)|=(5494502957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1293306069/2500000000 : ℝ)|^8425 ≤ (41863406365057/100000000000000 : ℝ)^6377
        have hw : |(1293306069/2500000000 : ℝ)|=(1293306069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s2_1 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2685046321/5000000000 : ℝ)*x 0 + (-2276813749/10000000000 : ℝ)*x 1 + (1293306057/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685046321/5000000000 : ℝ)^8425 ≤ (21990459810663/50000000000000 : ℝ)^6377 := by
    have hnat : (2685046321 : ℕ)^8425*50000000000000^6377 ≤ 21990459810663^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685046321 5000000000 21990459810663 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2276813749/10000000000 : ℝ)^8425 ≤ (7077837254169/50000000000000 : ℝ)^6377 := by
    have hnat : (2276813749 : ℕ)^8425*50000000000000^6377 ≤ 7077837254169^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276813749 10000000000 7077837254169 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1293306057/2500000000 : ℝ)^8425 ≤ (41863405851879/100000000000000 : ℝ)^6377 := by
    have hnat : (1293306057 : ℕ)^8425*100000000000000^6377 ≤ 41863405851879^6377*2500000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293306057 2500000000 41863405851879 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685046321/5000000000 : ℝ), (-2276813749/10000000000 : ℝ), (1293306057/2500000000 : ℝ)] ![(21990459810663/50000000000000 : ℝ), (7077837254169/50000000000000 : ℝ), (41863405851879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685046321/5000000000 : ℝ)|^8425 ≤ (21990459810663/50000000000000 : ℝ)^6377
        have hw : |(2685046321/5000000000 : ℝ)|=(2685046321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2276813749/10000000000 : ℝ)|^8425 ≤ (7077837254169/50000000000000 : ℝ)^6377
        have hw : |(-2276813749/10000000000 : ℝ)|=(2276813749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1293306057/2500000000 : ℝ)|^8425 ≤ (41863405851879/100000000000000 : ℝ)^6377
        have hw : |(1293306057/2500000000 : ℝ)|=(1293306057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s2_2 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (268504623/500000000 : ℝ)*x 0 + (2586612193/5000000000 : ℝ)*x 1 + (-284601723/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268504623/500000000 : ℝ)^8425 ≤ (43980917652047/100000000000000 : ℝ)^6377 := by
    have hnat : (268504623 : ℕ)^8425*100000000000000^6377 ≤ 43980917652047^6377*500000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268504623 500000000 43980917652047 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2586612193/5000000000 : ℝ)^8425 ≤ (4186340754109/10000000000000 : ℝ)^6377 := by
    have hnat : (2586612193 : ℕ)^8425*10000000000000^6377 ≤ 4186340754109^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586612193 5000000000 4186340754109 10000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (284601723/1250000000 : ℝ)^8425 ≤ (14155674795829/100000000000000 : ℝ)^6377 := by
    have hnat : (284601723 : ℕ)^8425*100000000000000^6377 ≤ 14155674795829^6377*1250000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284601723 1250000000 14155674795829 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268504623/500000000 : ℝ), (2586612193/5000000000 : ℝ), (-284601723/1250000000 : ℝ)] ![(43980917652047/100000000000000 : ℝ), (4186340754109/10000000000000 : ℝ), (14155674795829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268504623/500000000 : ℝ)|^8425 ≤ (43980917652047/100000000000000 : ℝ)^6377
        have hw : |(268504623/500000000 : ℝ)|=(268504623/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2586612193/5000000000 : ℝ)|^8425 ≤ (4186340754109/10000000000000 : ℝ)^6377
        have hw : |(2586612193/5000000000 : ℝ)|=(2586612193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-284601723/1250000000 : ℝ)|^8425 ≤ (14155674795829/100000000000000 : ℝ)^6377
        have hw : |(-284601723/1250000000 : ℝ)|=(284601723/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s2_3 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4343233337/10000000000 : ℝ)*x 0 + (2014907933/5000000000 : ℝ)*x 1 + (4680294317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4343233337/10000000000 : ℝ)^8425 ≤ (6645464656463/20000000000000 : ℝ)^6377 := by
    have hnat : (4343233337 : ℕ)^8425*20000000000000^6377 ≤ 6645464656463^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343233337 10000000000 6645464656463 20000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2014907933/5000000000 : ℝ)^8425 ≤ (3009684059001/10000000000000 : ℝ)^6377 := by
    have hnat : (2014907933 : ℕ)^8425*10000000000000^6377 ≤ 3009684059001^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014907933 5000000000 3009684059001 10000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4680294317/10000000000 : ℝ)^8425 ≤ (18337918052673/50000000000000 : ℝ)^6377 := by
    have hnat : (4680294317 : ℕ)^8425*50000000000000^6377 ≤ 18337918052673^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4680294317 10000000000 18337918052673 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4343233337/10000000000 : ℝ), (2014907933/5000000000 : ℝ), (4680294317/10000000000 : ℝ)] ![(6645464656463/20000000000000 : ℝ), (3009684059001/10000000000000 : ℝ), (18337918052673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4343233337/10000000000 : ℝ)|^8425 ≤ (6645464656463/20000000000000 : ℝ)^6377
        have hw : |(4343233337/10000000000 : ℝ)|=(4343233337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2014907933/5000000000 : ℝ)|^8425 ≤ (3009684059001/10000000000000 : ℝ)^6377
        have hw : |(2014907933/5000000000 : ℝ)|=(2014907933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4680294317/10000000000 : ℝ)|^8425 ≤ (18337918052673/50000000000000 : ℝ)^6377
        have hw : |(4680294317/10000000000 : ℝ)|=(4680294317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s2_4 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2110415939/10000000000 : ℝ)*x 0 + (5175303997/10000000000 : ℝ)*x 1 + (549240361/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2110415939/10000000000 : ℝ)^8425 ≤ (2561038182901/20000000000000 : ℝ)^6377 := by
    have hnat : (2110415939 : ℕ)^8425*20000000000000^6377 ≤ 2561038182901^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110415939 10000000000 2561038182901 20000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5175303997/10000000000 : ℝ)^8425 ≤ (41885642528543/100000000000000 : ℝ)^6377 := by
    have hnat : (5175303997 : ℕ)^8425*100000000000000^6377 ≤ 41885642528543^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175303997 10000000000 41885642528543 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (549240361/1000000000 : ℝ)^8425 ≤ (9061833307429/20000000000000 : ℝ)^6377 := by
    have hnat : (549240361 : ℕ)^8425*20000000000000^6377 ≤ 9061833307429^6377*1000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549240361 1000000000 9061833307429 20000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2110415939/10000000000 : ℝ), (5175303997/10000000000 : ℝ), (549240361/1000000000 : ℝ)] ![(2561038182901/20000000000000 : ℝ), (41885642528543/100000000000000 : ℝ), (9061833307429/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2110415939/10000000000 : ℝ)|^8425 ≤ (2561038182901/20000000000000 : ℝ)^6377
        have hw : |(-2110415939/10000000000 : ℝ)|=(2110415939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5175303997/10000000000 : ℝ)|^8425 ≤ (41885642528543/100000000000000 : ℝ)^6377
        have hw : |(5175303997/10000000000 : ℝ)|=(5175303997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(549240361/1000000000 : ℝ)|^8425 ≤ (9061833307429/20000000000000 : ℝ)^6377
        have hw : |(549240361/1000000000 : ℝ)|=(549240361/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s2_5 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288097913/10000000000 : ℝ)*x 0 + (-978817089/5000000000 : ℝ)*x 1 + (5492403651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288097913/10000000000 : ℝ)^8425 ≤ (43095901575209/100000000000000 : ℝ)^6377 := by
    have hnat : (5288097913 : ℕ)^8425*100000000000000^6377 ≤ 43095901575209^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288097913 10000000000 43095901575209 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (978817089/5000000000 : ℝ)^8425 ≤ (5797465714707/50000000000000 : ℝ)^6377 := by
    have hnat : (978817089 : ℕ)^8425*50000000000000^6377 ≤ 5797465714707^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978817089 5000000000 5797465714707 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5492403651/10000000000 : ℝ)^8425 ≤ (22654583491997/50000000000000 : ℝ)^6377 := by
    have hnat : (5492403651 : ℕ)^8425*50000000000000^6377 ≤ 22654583491997^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492403651 10000000000 22654583491997 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288097913/10000000000 : ℝ), (-978817089/5000000000 : ℝ), (5492403651/10000000000 : ℝ)] ![(43095901575209/100000000000000 : ℝ), (5797465714707/50000000000000 : ℝ), (22654583491997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288097913/10000000000 : ℝ)|^8425 ≤ (43095901575209/100000000000000 : ℝ)^6377
        have hw : |(5288097913/10000000000 : ℝ)|=(5288097913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-978817089/5000000000 : ℝ)|^8425 ≤ (5797465714707/50000000000000 : ℝ)^6377
        have hw : |(-978817089/5000000000 : ℝ)|=(978817089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5492403651/10000000000 : ℝ)|^8425 ≤ (22654583491997/50000000000000 : ℝ)^6377
        have hw : |(5492403651/10000000000 : ℝ)|=(5492403651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s2_6 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288098089/10000000000 : ℝ)*x 0 + (1373100929/2500000000 : ℝ)*x 1 + (-489408461/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288098089/10000000000 : ℝ)^8425 ≤ (2154795173509/5000000000000 : ℝ)^6377 := by
    have hnat : (5288098089 : ℕ)^8425*5000000000000^6377 ≤ 2154795173509^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288098089 10000000000 2154795173509 5000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1373100929/2500000000 : ℝ)^8425 ≤ (45309167692413/100000000000000 : ℝ)^6377 := by
    have hnat : (1373100929 : ℕ)^8425*100000000000000^6377 ≤ 45309167692413^6377*2500000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373100929 2500000000 45309167692413 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (489408461/2500000000 : ℝ)^8425 ≤ (11594928815829/100000000000000 : ℝ)^6377 := by
    have hnat : (489408461 : ℕ)^8425*100000000000000^6377 ≤ 11594928815829^6377*2500000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489408461 2500000000 11594928815829 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288098089/10000000000 : ℝ), (1373100929/2500000000 : ℝ), (-489408461/2500000000 : ℝ)] ![(2154795173509/5000000000000 : ℝ), (45309167692413/100000000000000 : ℝ), (11594928815829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288098089/10000000000 : ℝ)|^8425 ≤ (2154795173509/5000000000000 : ℝ)^6377
        have hw : |(5288098089/10000000000 : ℝ)|=(5288098089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1373100929/2500000000 : ℝ)|^8425 ≤ (45309167692413/100000000000000 : ℝ)^6377
        have hw : |(1373100929/2500000000 : ℝ)|=(1373100929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-489408461/2500000000 : ℝ)|^8425 ≤ (11594928815829/100000000000000 : ℝ)^6377
        have hw : |(-489408461/2500000000 : ℝ)|=(489408461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s2_7 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4343395831/10000000000 : ℝ)*x 0 + (2338041887/5000000000 : ℝ)*x 1 + (403406589/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4343395831/10000000000 : ℝ)^8425 ≤ (8307241417449/25000000000000 : ℝ)^6377 := by
    have hnat : (4343395831 : ℕ)^8425*25000000000000^6377 ≤ 8307241417449^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343395831 10000000000 8307241417449 25000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2338041887/5000000000 : ℝ)^8425 ≤ (18316125620283/50000000000000 : ℝ)^6377 := by
    have hnat : (2338041887 : ℕ)^8425*50000000000000^6377 ≤ 18316125620283^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2338041887 5000000000 18316125620283 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403406589/1000000000 : ℝ)^8425 ≤ (6027756613989/20000000000000 : ℝ)^6377 := by
    have hnat : (403406589 : ℕ)^8425*20000000000000^6377 ≤ 6027756613989^6377*1000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403406589 1000000000 6027756613989 20000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4343395831/10000000000 : ℝ), (2338041887/5000000000 : ℝ), (403406589/1000000000 : ℝ)] ![(8307241417449/25000000000000 : ℝ), (18316125620283/50000000000000 : ℝ), (6027756613989/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4343395831/10000000000 : ℝ)|^8425 ≤ (8307241417449/25000000000000 : ℝ)^6377
        have hw : |(4343395831/10000000000 : ℝ)|=(4343395831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2338041887/5000000000 : ℝ)|^8425 ≤ (18316125620283/50000000000000 : ℝ)^6377
        have hw : |(2338041887/5000000000 : ℝ)|=(2338041887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(403406589/1000000000 : ℝ)|^8425 ≤ (6027756613989/20000000000000 : ℝ)^6377
        have hw : |(403406589/1000000000 : ℝ)|=(403406589/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1232_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37808179/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20041/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3069/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4729/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16249/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20041/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3069/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20041/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3069/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20041/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3069/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20041/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3069/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20041/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3069/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20041/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3069/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3069/50000 : ℝ) ^ (1053/256 : ℝ) ≤ (103469823162633/10000000000000000000 : ℝ) := by
    have hpowers : (3069/50000 : ℝ)^1053 ≤ (103469823162633/10000000000000000000 : ℝ)^256 := by
      have hnat : (3069 : ℕ)^1053*10000000000000000000^256 ≤ 103469823162633^256*50000^1053 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3069 50000 103469823162633 10000000000000000000 1053 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3069/50000 : ℝ)) (X := (103469823162633/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hpowhi : (20041/100000 : ℝ) ^ (1053/256 : ℝ) ≤ (2100961692433123/1562500000000000000 : ℝ) := by
    have hpowers : (20041/100000 : ℝ)^1053 ≤ (2100961692433123/1562500000000000000 : ℝ)^256 := by
      have hnat : (20041 : ℕ)^1053*1562500000000000000^256 ≤ 2100961692433123^256*100000^1053 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20041 100000 2100961692433123 1562500000000000000 1053 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20041/100000 : ℝ)) (X := (2100961692433123/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000103469823162633/5000000000000000000 : ℝ) ≤ (10000050309719449/10000000000000000 : ℝ) ^ (1053/256 : ℝ) := by
    have hpowers : (5000103469823162633/5000000000000000000 : ℝ)^256 ≤ (10000050309719449/10000000000000000 : ℝ)^1053 := by
      have hnat : (5000103469823162633 : ℕ)^256*10000000000000000^1053 ≤ 10000050309719449^1053*5000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000103469823162633 5000000000000000000 10000050309719449 10000000000000000 256 1053 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000050309719449/10000000000000000 : ℝ)) (X := (5000103469823162633/5000000000000000000 : ℝ)) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50067748123273673101/50000000000000000000 : ℝ) ≤ (5001646213986461/5000000000000000 : ℝ) ^ (1053/256 : ℝ) := by
    have hpowers : (50067748123273673101/50000000000000000000 : ℝ)^256 ≤ (5001646213986461/5000000000000000 : ℝ)^1053 := by
      have hnat : (50067748123273673101 : ℕ)^256*5000000000000000^1053 ≤ 5001646213986461^1053*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50067748123273673101 50000000000000000000 5001646213986461 5000000000000000 256 1053 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001646213986461/5000000000000000 : ℝ)) (X := (50067748123273673101/50000000000000000000 : ℝ)) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (783350961692433123/781250000000000000 : ℝ) ≤ (2001306909245279/2000000000000000 : ℝ) ^ (1053/256 : ℝ) := by
    have hpowers : (783350961692433123/781250000000000000 : ℝ)^256 ≤ (2001306909245279/2000000000000000 : ℝ)^1053 := by
      have hnat : (783350961692433123 : ℕ)^256*2000000000000000^1053 ≤ 2001306909245279^1053*781250000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        783350961692433123 781250000000000000 2001306909245279 2000000000000000 256 1053 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001306909245279/2000000000000000 : ℝ)) (X := (783350961692433123/781250000000000000 : ℝ)) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(103469823162633/10000000000000000000 : ℝ) ≤ ((138990899212349864899/139030000000000000000 : ℝ)+2*(3242118253473/1390300000000000 : ℝ)*(3069/50000 : ℝ))^(1053/256 : ℝ) := by
    rw [show (138990899212349864899/139030000000000000000 : ℝ)+2*(3242118253473/1390300000000000 : ℝ)*(3069/50000 : ℝ)=(10000050309719449/10000000000000000 : ℝ) by norm_num, show 1+2*(103469823162633/10000000000000000000 : ℝ)=(5000103469823162633/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2100961692433123/1562500000000000000 : ℝ)+(103469823162633/10000000000000000000 : ℝ) ≤ ((138990899212349864899/139030000000000000000 : ℝ)+(3242118253473/1390300000000000 : ℝ)*((20041/100000 : ℝ)+(3069/50000 : ℝ)))^(1053/256 : ℝ) := by
    rw [show (138990899212349864899/139030000000000000000 : ℝ)+(3242118253473/1390300000000000 : ℝ)*((20041/100000 : ℝ)+(3069/50000 : ℝ))=(5001646213986461/5000000000000000 : ℝ) by norm_num, show 1+(2100961692433123/1562500000000000000 : ℝ)+(103469823162633/10000000000000000000 : ℝ)=(50067748123273673101/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2100961692433123/1562500000000000000 : ℝ) ≤ ((138990899212349864899/139030000000000000000 : ℝ)+2*(3242118253473/1390300000000000 : ℝ)*(20041/100000 : ℝ))^(1053/256 : ℝ) := by
    rw [show (138990899212349864899/139030000000000000000 : ℝ)+2*(3242118253473/1390300000000000 : ℝ)*(20041/100000 : ℝ)=(2001306909245279/2000000000000000 : ℝ) by norm_num, show 1+2*(2100961692433123/1562500000000000000 : ℝ)=(783350961692433123/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (138990899212349864899/139030000000000000000 : ℝ)*(X 1 0+X 2 0)+(3242118253473/1390300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1053/256 : ℝ)) (lo := (3069/50000 : ℝ)) (hi := (20041/100000 : ℝ)) (c := (138990899212349864899/139030000000000000000 : ℝ)) (alpha := (3242118253473/1390300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (138990899212349864899/139030000000000000000 : ℝ)*(X 0 1+X 2 1)+(3242118253473/1390300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1053/256 : ℝ)) (lo := (3069/50000 : ℝ)) (hi := (20041/100000 : ℝ)) (c := (138990899212349864899/139030000000000000000 : ℝ)) (alpha := (3242118253473/1390300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (138990899212349864899/139030000000000000000 : ℝ)*(X 0 2+X 1 2)+(3242118253473/1390300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1053/256 : ℝ)) (lo := (3069/50000 : ℝ)) (hi := (20041/100000 : ℝ)) (c := (138990899212349864899/139030000000000000000 : ℝ)) (alpha := (3242118253473/1390300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2110335411/10000000000 : ℝ)*X 0 0+(5494502957/10000000000 : ℝ)*X 0 1+(1293306069/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2685046321/5000000000 : ℝ)*X 1 0+(-2276813749/10000000000 : ℝ)*X 1 1+(1293306057/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((268504623/500000000 : ℝ)*X 2 0+(2586612193/5000000000 : ℝ)*X 2 1+(-284601723/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4343233337/10000000000 : ℝ)*X 0 0+(2014907933/5000000000 : ℝ)*X 0 1+(4680294317/10000000000 : ℝ)*X 0 2+(4343233337/10000000000 : ℝ)*X 1 0+(2014907933/5000000000 : ℝ)*X 1 1+(4680294317/10000000000 : ℝ)*X 1 2+(4343233337/10000000000 : ℝ)*X 2 0+(2014907933/5000000000 : ℝ)*X 2 1+(4680294317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2110415939/10000000000 : ℝ)*X 0 0+(5175303997/10000000000 : ℝ)*X 0 1+(549240361/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5288097913/10000000000 : ℝ)*X 1 0+(-978817089/5000000000 : ℝ)*X 1 1+(5492403651/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5288098089/10000000000 : ℝ)*X 2 0+(1373100929/2500000000 : ℝ)*X 2 1+(-489408461/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4343395831/10000000000 : ℝ)*X 0 0+(2338041887/5000000000 : ℝ)*X 0 1+(403406589/1000000000 : ℝ)*X 0 2+(4343395831/10000000000 : ℝ)*X 1 0+(2338041887/5000000000 : ℝ)*X 1 1+(403406589/1000000000 : ℝ)*X 1 2+(4343395831/10000000000 : ℝ)*X 2 0+(2338041887/5000000000 : ℝ)*X 2 1+(403406589/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8614077064819981557063440889/868937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (992194271/50000000000000 : ℝ)*(base19) + (870722543/50000000000000 : ℝ)*(base23) + (73813503/100000000000000 : ℝ)*(lower2) + (304361957/100000000000000 : ℝ)*(upper3) + (35519271/25000000000000 : ℝ)*(upper5) + (581244650988163/25000000000000 : ℝ)*(major0) + (581244650988163/25000000000000 : ℝ)*(major1) + (581244650988163/25000000000000 : ℝ)*(major2) + (1556292628043467/50000000000000 : ℝ)*(sp0) + (1556301638335623/50000000000000 : ℝ)*(sp1) + (1556301759807351/50000000000000 : ℝ)*(sp2) + (768669982710217/50000000000000 : ℝ)*(sp3) + (20004972853/100000000000000 : ℝ)*(sp4) + (11650980247/100000000000000 : ℝ)*(sp7) + (768675808200341/50000000000000 : ℝ)*(f.failure) + (778151315264947/25000000000000 : ℝ)*(f.sum) + (199722522098643/34757500000000000000000000000 : ℝ)*base65 + (12773204681457340537/3475750000000000000000000000000000 : ℝ)*base67 + (9331578826816590537/3475750000000000000000000000000000 : ℝ)*base69 + (17193124282747840537/3475750000000000000000000000000000 : ℝ)*base71 + (20650326916781/17378750000000000000000000000 : ℝ)*base74 + (16714784412063909463/3475750000000000000000000000000000 : ℝ)*base76 + (34857667868206840537/3475750000000000000000000000000000 : ℝ)*base77 + (17670308099012590537/3475750000000000000000000000000000 : ℝ)*base79 + (1413051584949/17378750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (10389039/1250000000000000000000 : ℝ)*base89 + (10389039/1250000000000000000000 : ℝ)*base91 + (10389039/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6632118252642039101726511861/3475750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (376596017/50000000000000 : ℝ)*(base19) + (1083168623/100000000000000 : ℝ)*(base23) + (1693251/2500000000000 : ℝ)*(upper2) + (127403367/100000000000000 : ℝ)*(upper3) + (17737859/50000000000000 : ℝ)*(upper5) + (1177792815405471/50000000000000 : ℝ)*(major0) + (1177792815405471/50000000000000 : ℝ)*(major1) + (1177792815405471/50000000000000 : ℝ)*(major2) + (176260487/2500000000000 : ℝ)*(sp1) + (831394913/6250000000000 : ℝ)*(sp2) + (197098826129727/6250000000000 : ℝ)*(sp4) + (3153573414464119/100000000000000 : ℝ)*(sp5) + (3153566832588401/100000000000000 : ℝ)*(sp6) + (155758997994253/10000000000000 : ℝ)*(sp7) + (155758997994253/10000000000000 : ℝ)*(f.failure) + (197098826129727/6250000000000 : ℝ)*(f.sum) + (36353088314291/17378750000000000000000000000 : ℝ)*base66 + (6807683357952237571/6951500000000000000000000000000000 : ℝ)*base68 + (79691546370996237571/6951500000000000000000000000000000 : ℝ)*base70 + (53560920552671737571/6951500000000000000000000000000000 : ℝ)*base72 + (84364496405699/17378750000000000000000000000 : ℝ)*base73 + (124552553817129737571/6951500000000000000000000000000000 : ℝ)*base76 + (48913228025914737571/6951500000000000000000000000000000 : ℝ)*base78 + (5835666930502237571/6951500000000000000000000000000000 : ℝ)*base80 + (174144953335097/34757500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3395287/250000000000000000000 : ℝ)*base89 + (3395287/250000000000000000000 : ℝ)*base91 + (3395287/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1232_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37808179/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20041/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3069/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4729/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16249/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1232_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1232_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37808179/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4729/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16249/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1232_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1232_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1232_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37808179/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4729/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16249/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1232_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
