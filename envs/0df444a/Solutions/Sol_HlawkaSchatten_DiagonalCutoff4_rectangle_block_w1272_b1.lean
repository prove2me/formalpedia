-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1272_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:20.945053+00:00
-- url     : https://prove2.me/submissions/ee71ff50-9b87-4c0d-b366-ff3a44f1b53c

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
theorem support_rectangle_w1272_s3_0 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2103171819/10000000000 : ℝ)*x 0 + (5417011887/10000000000 : ℝ)*x 1 + (5242927427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103171819/10000000000 : ℝ)^4233 ≤ (12787992671191/100000000000000 : ℝ)^3209 := by
    have hnat : (2103171819 : ℕ)^4233*100000000000000^3209 ≤ 12787992671191^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103171819 10000000000 12787992671191 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417011887/10000000000 : ℝ)^4233 ≤ (44545297638427/100000000000000 : ℝ)^3209 := by
    have hnat : (5417011887 : ℕ)^4233*100000000000000^3209 ≤ 44545297638427^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417011887 10000000000 44545297638427 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242927427/10000000000 : ℝ)^4233 ≤ (42666709675803/100000000000000 : ℝ)^3209 := by
    have hnat : (5242927427 : ℕ)^4233*100000000000000^3209 ≤ 42666709675803^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242927427 10000000000 42666709675803 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2103171819/10000000000 : ℝ), (5417011887/10000000000 : ℝ), (5242927427/10000000000 : ℝ)] ![(12787992671191/100000000000000 : ℝ), (44545297638427/100000000000000 : ℝ), (42666709675803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2103171819/10000000000 : ℝ)|^4233 ≤ (12787992671191/100000000000000 : ℝ)^3209
        have hw : |(-2103171819/10000000000 : ℝ)|=(2103171819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417011887/10000000000 : ℝ)|^4233 ≤ (44545297638427/100000000000000 : ℝ)^3209
        have hw : |(5417011887/10000000000 : ℝ)|=(5417011887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242927427/10000000000 : ℝ)|^4233 ≤ (42666709675803/100000000000000 : ℝ)^3209
        have hw : |(5242927427/10000000000 : ℝ)|=(5242927427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s3_1 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070163227/2000000000 : ℝ)*x 0 + (-219192987/1000000000 : ℝ)*x 1 + (1310731847/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070163227/2000000000 : ℝ)^4233 ≤ (21914329015687/50000000000000 : ℝ)^3209 := by
    have hnat : (1070163227 : ℕ)^4233*50000000000000^3209 ≤ 21914329015687^3209*2000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070163227 2000000000 21914329015687 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219192987/1000000000 : ℝ)^4233 ≤ (1688079087377/12500000000000 : ℝ)^3209 := by
    have hnat : (219192987 : ℕ)^4233*12500000000000^3209 ≤ 1688079087377^3209*1000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219192987 1000000000 1688079087377 12500000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310731847/2500000000 : ℝ)^4233 ≤ (21333354628573/50000000000000 : ℝ)^3209 := by
    have hnat : (1310731847 : ℕ)^4233*50000000000000^3209 ≤ 21333354628573^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310731847 2500000000 21333354628573 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070163227/2000000000 : ℝ), (-219192987/1000000000 : ℝ), (1310731847/2500000000 : ℝ)] ![(21914329015687/50000000000000 : ℝ), (1688079087377/12500000000000 : ℝ), (21333354628573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070163227/2000000000 : ℝ)|^4233 ≤ (21914329015687/50000000000000 : ℝ)^3209
        have hw : |(1070163227/2000000000 : ℝ)|=(1070163227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-219192987/1000000000 : ℝ)|^4233 ≤ (1688079087377/12500000000000 : ℝ)^3209
        have hw : |(-219192987/1000000000 : ℝ)|=(219192987/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310731847/2500000000 : ℝ)|^4233 ≤ (21333354628573/50000000000000 : ℝ)^3209
        have hw : |(1310731847/2500000000 : ℝ)|=(1310731847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s3_2 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334426007/625000000 : ℝ)*x 0 + (2621463767/5000000000 : ℝ)*x 1 + (-547982427/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334426007/625000000 : ℝ)^4233 ≤ (2739291111429/6250000000000 : ℝ)^3209 := by
    have hnat : (334426007 : ℕ)^4233*6250000000000^3209 ≤ 2739291111429^3209*625000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334426007 625000000 2739291111429 6250000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621463767/5000000000 : ℝ)^4233 ≤ (21333355412213/50000000000000 : ℝ)^3209 := by
    have hnat : (2621463767 : ℕ)^4233*50000000000000^3209 ≤ 21333355412213^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621463767 5000000000 21333355412213 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547982427/2500000000 : ℝ)^4233 ≤ (3376157845607/25000000000000 : ℝ)^3209 := by
    have hnat : (547982427 : ℕ)^4233*25000000000000^3209 ≤ 3376157845607^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547982427 2500000000 3376157845607 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334426007/625000000 : ℝ), (2621463767/5000000000 : ℝ), (-547982427/2500000000 : ℝ)] ![(2739291111429/6250000000000 : ℝ), (21333355412213/50000000000000 : ℝ), (3376157845607/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334426007/625000000 : ℝ)|^4233 ≤ (2739291111429/6250000000000 : ℝ)^3209
        have hw : |(334426007/625000000 : ℝ)|=(334426007/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621463767/5000000000 : ℝ)|^4233 ≤ (21333355412213/50000000000000 : ℝ)^3209
        have hw : |(2621463767/5000000000 : ℝ)|=(2621463767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-547982427/2500000000 : ℝ)|^4233 ≤ (3376157845607/25000000000000 : ℝ)^3209
        have hw : |(-547982427/2500000000 : ℝ)|=(547982427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s3_3 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4344984049/10000000000 : ℝ)*x 0 + (52135713/125000000 : ℝ)*x 1 + (1131528609/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4344984049/10000000000 : ℝ)^4233 ≤ (2081370142667/6250000000000 : ℝ)^3209 := by
    have hnat : (4344984049 : ℕ)^4233*6250000000000^3209 ≤ 2081370142667^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4344984049 10000000000 2081370142667 6250000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52135713/125000000 : ℝ)^4233 ≤ (7888206095373/25000000000000 : ℝ)^3209 := by
    have hnat : (52135713 : ℕ)^4233*25000000000000^3209 ≤ 7888206095373^3209*125000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52135713 125000000 7888206095373 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131528609/2500000000 : ℝ)^4233 ≤ (137286145771/390625000000 : ℝ)^3209 := by
    have hnat : (1131528609 : ℕ)^4233*390625000000^3209 ≤ 137286145771^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131528609 2500000000 137286145771 390625000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4344984049/10000000000 : ℝ), (52135713/125000000 : ℝ), (1131528609/2500000000 : ℝ)] ![(2081370142667/6250000000000 : ℝ), (7888206095373/25000000000000 : ℝ), (137286145771/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4344984049/10000000000 : ℝ)|^4233 ≤ (2081370142667/6250000000000 : ℝ)^3209
        have hw : |(4344984049/10000000000 : ℝ)|=(4344984049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52135713/125000000 : ℝ)|^4233 ≤ (7888206095373/25000000000000 : ℝ)^3209
        have hw : |(52135713/125000000 : ℝ)|=(52135713/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1131528609/2500000000 : ℝ)|^4233 ≤ (137286145771/390625000000 : ℝ)^3209
        have hw : |(1131528609/2500000000 : ℝ)|=(1131528609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s3_4 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-84127403/400000000 : ℝ)*x 0 + (2621774047/5000000000 : ℝ)*x 1 + (5416387831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84127403/400000000 : ℝ)^4233 ≤ (3197024748051/25000000000000 : ℝ)^3209 := by
    have hnat : (84127403 : ℕ)^4233*25000000000000^3209 ≤ 3197024748051^3209*400000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84127403 400000000 3197024748051 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621774047/5000000000 : ℝ)^4233 ≤ (10668343134057/25000000000000 : ℝ)^3209 := by
    have hnat : (2621774047 : ℕ)^4233*25000000000000^3209 ≤ 10668343134057^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621774047 5000000000 10668343134057 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416387831/10000000000 : ℝ)^4233 ≤ (44538528456161/100000000000000 : ℝ)^3209 := by
    have hnat : (5416387831 : ℕ)^4233*100000000000000^3209 ≤ 44538528456161^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416387831 10000000000 44538528456161 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-84127403/400000000 : ℝ), (2621774047/5000000000 : ℝ), (5416387831/10000000000 : ℝ)] ![(3197024748051/25000000000000 : ℝ), (10668343134057/25000000000000 : ℝ), (44538528456161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-84127403/400000000 : ℝ)|^4233 ≤ (3197024748051/25000000000000 : ℝ)^3209
        have hw : |(-84127403/400000000 : ℝ)|=(84127403/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621774047/5000000000 : ℝ)|^4233 ≤ (10668343134057/25000000000000 : ℝ)^3209
        have hw : |(2621774047/5000000000 : ℝ)|=(2621774047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416387831/10000000000 : ℝ)|^4233 ≤ (44538528456161/100000000000000 : ℝ)^3209
        have hw : |(5416387831/10000000000 : ℝ)|=(5416387831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s3_5 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5306312331/10000000000 : ℝ)*x 0 + (-2018468787/10000000000 : ℝ)*x 1 + (1083277533/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5306312331/10000000000 : ℝ)^4233 ≤ (10837110670419/25000000000000 : ℝ)^3209 := by
    have hnat : (5306312331 : ℕ)^4233*25000000000000^3209 ≤ 10837110670419^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5306312331 10000000000 10837110670419 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2018468787/10000000000 : ℝ)^4233 ≤ (6056515324457/50000000000000 : ℝ)^3209 := by
    have hnat : (2018468787 : ℕ)^4233*50000000000000^3209 ≤ 6056515324457^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018468787 10000000000 6056515324457 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083277533/2000000000 : ℝ)^4233 ≤ (2226926332779/5000000000000 : ℝ)^3209 := by
    have hnat : (1083277533 : ℕ)^4233*5000000000000^3209 ≤ 2226926332779^3209*2000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083277533 2000000000 2226926332779 5000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5306312331/10000000000 : ℝ), (-2018468787/10000000000 : ℝ), (1083277533/2000000000 : ℝ)] ![(10837110670419/25000000000000 : ℝ), (6056515324457/50000000000000 : ℝ), (2226926332779/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5306312331/10000000000 : ℝ)|^4233 ≤ (10837110670419/25000000000000 : ℝ)^3209
        have hw : |(5306312331/10000000000 : ℝ)|=(5306312331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2018468787/10000000000 : ℝ)|^4233 ≤ (6056515324457/50000000000000 : ℝ)^3209
        have hw : |(-2018468787/10000000000 : ℝ)|=(2018468787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083277533/2000000000 : ℝ)|^4233 ≤ (2226926332779/5000000000000 : ℝ)^3209
        have hw : |(1083277533/2000000000 : ℝ)|=(1083277533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s3_6 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663288951/1250000000 : ℝ)*x 0 + (1354097027/2500000000 : ℝ)*x 1 + (-504617291/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663288951/1250000000 : ℝ)^4233 ≤ (43348434890599/100000000000000 : ℝ)^3209 := by
    have hnat : (663288951 : ℕ)^4233*100000000000000^3209 ≤ 43348434890599^3209*1250000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663288951 1250000000 43348434890599 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354097027/2500000000 : ℝ)^4233 ≤ (22269265730373/50000000000000 : ℝ)^3209 := by
    have hnat : (1354097027 : ℕ)^4233*50000000000000^3209 ≤ 22269265730373^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354097027 2500000000 22269265730373 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (504617291/2500000000 : ℝ)^4233 ≤ (12113033633271/100000000000000 : ℝ)^3209 := by
    have hnat : (504617291 : ℕ)^4233*100000000000000^3209 ≤ 12113033633271^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504617291 2500000000 12113033633271 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663288951/1250000000 : ℝ), (1354097027/2500000000 : ℝ), (-504617291/2500000000 : ℝ)] ![(43348434890599/100000000000000 : ℝ), (22269265730373/50000000000000 : ℝ), (12113033633271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663288951/1250000000 : ℝ)|^4233 ≤ (43348434890599/100000000000000 : ℝ)^3209
        have hw : |(663288951/1250000000 : ℝ)|=(663288951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354097027/2500000000 : ℝ)|^4233 ≤ (22269265730373/50000000000000 : ℝ)^3209
        have hw : |(1354097027/2500000000 : ℝ)|=(1354097027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-504617291/2500000000 : ℝ)|^4233 ≤ (12113033633271/100000000000000 : ℝ)^3209
        have hw : |(-504617291/2500000000 : ℝ)|=(504617291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s3_7 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4345011223/10000000000 : ℝ)*x 0 + (1131211637/2500000000 : ℝ)*x 1 + (130379087/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4345011223/10000000000 : ℝ)^4233 ≤ (33302197017471/100000000000000 : ℝ)^3209 := by
    have hnat : (4345011223 : ℕ)^4233*100000000000000^3209 ≤ 33302197017471^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4345011223 10000000000 33302197017471 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1131211637/2500000000 : ℝ)^4233 ≤ (7026453428911/20000000000000 : ℝ)^3209 := by
    have hnat : (1131211637 : ℕ)^4233*20000000000000^3209 ≤ 7026453428911^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131211637 2500000000 7026453428911 20000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130379087/312500000 : ℝ)^4233 ≤ (31565535822839/100000000000000 : ℝ)^3209 := by
    have hnat : (130379087 : ℕ)^4233*100000000000000^3209 ≤ 31565535822839^3209*312500000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130379087 312500000 31565535822839 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4345011223/10000000000 : ℝ), (1131211637/2500000000 : ℝ), (130379087/312500000 : ℝ)] ![(33302197017471/100000000000000 : ℝ), (7026453428911/20000000000000 : ℝ), (31565535822839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4345011223/10000000000 : ℝ)|^4233 ≤ (33302197017471/100000000000000 : ℝ)^3209
        have hw : |(4345011223/10000000000 : ℝ)|=(4345011223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1131211637/2500000000 : ℝ)|^4233 ≤ (7026453428911/20000000000000 : ℝ)^3209
        have hw : |(1131211637/2500000000 : ℝ)|=(1131211637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130379087/312500000 : ℝ)|^4233 ≤ (31565535822839/100000000000000 : ℝ)^3209
        have hw : |(130379087/312500000 : ℝ)|=(130379087/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1272_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1009/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9623/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10989/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7337/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1009/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9623/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1009/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9623/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1009/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9623/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1009/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9623/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1009/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9623/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1009/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9623/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9623/100000 : ℝ) ^ (8465/2048 : ℝ) ≤ (627648415296837/10000000000000000000 : ℝ) := by
    have hpowers : (9623/100000 : ℝ)^8465 ≤ (627648415296837/10000000000000000000 : ℝ)^2048 := by
      have hnat : (9623 : ℕ)^8465*10000000000000000000^2048 ≤ 627648415296837^2048*100000^8465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9623 100000 627648415296837 10000000000000000000 8465 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9623/100000 : ℝ)) (X := (627648415296837/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1009/6250 : ℝ) ^ (8465/2048 : ℝ) ≤ (5326867115576171/10000000000000000000 : ℝ) := by
    have hpowers : (1009/6250 : ℝ)^8465 ≤ (5326867115576171/10000000000000000000 : ℝ)^2048 := by
      have hnat : (1009 : ℕ)^8465*10000000000000000000^2048 ≤ 5326867115576171^2048*6250^8465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1009 6250 5326867115576171 10000000000000000000 8465 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1009/6250 : ℝ)) (X := (5326867115576171/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000627648415296837/5000000000000000000 : ℝ) ≤ (1250037961098611/1250000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (5000627648415296837/5000000000000000000 : ℝ)^2048 ≤ (1250037961098611/1250000000000000 : ℝ)^8465 := by
      have hnat : (5000627648415296837 : ℕ)^2048*1250000000000000^8465 ≤ 1250037961098611^8465*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000627648415296837 5000000000000000000 1250037961098611 1250000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250037961098611/1250000000000000 : ℝ)) (X := (5000627648415296837/5000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (625372157220679563/625000000000000000 : ℝ) ≤ (5000720147457399/5000000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (625372157220679563/625000000000000000 : ℝ)^2048 ≤ (5000720147457399/5000000000000000 : ℝ)^8465 := by
      have hnat : (625372157220679563 : ℕ)^2048*5000000000000000^8465 ≤ 5000720147457399^8465*625000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625372157220679563 625000000000000000 5000720147457399 5000000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000720147457399/5000000000000000 : ℝ)) (X := (625372157220679563/625000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5005326867115576171/5000000000000000000 : ℝ) ≤ (2500644225260177/2500000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (5005326867115576171/5000000000000000000 : ℝ)^2048 ≤ (2500644225260177/2500000000000000 : ℝ)^8465 := by
      have hnat : (5005326867115576171 : ℕ)^2048*2500000000000000^8465 ≤ 2500644225260177^8465*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5005326867115576171 5000000000000000000 2500644225260177 2500000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500644225260177/2500000000000000 : ℝ)) (X := (5005326867115576171/5000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(627648415296837/10000000000000000000 : ℝ) ≤ ((16297526308273268697/16302500000000000000 : ℝ)+2*(113660612591/65210000000000 : ℝ)*(9623/100000 : ℝ))^(8465/2048 : ℝ) := by
    rw [show (16297526308273268697/16302500000000000000 : ℝ)+2*(113660612591/65210000000000 : ℝ)*(9623/100000 : ℝ)=(1250037961098611/1250000000000000 : ℝ) by norm_num, show 1+2*(627648415296837/10000000000000000000 : ℝ)=(5000627648415296837/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5326867115576171/10000000000000000000 : ℝ)+(627648415296837/10000000000000000000 : ℝ) ≤ ((16297526308273268697/16302500000000000000 : ℝ)+(113660612591/65210000000000 : ℝ)*((1009/6250 : ℝ)+(9623/100000 : ℝ)))^(8465/2048 : ℝ) := by
    rw [show (16297526308273268697/16302500000000000000 : ℝ)+(113660612591/65210000000000 : ℝ)*((1009/6250 : ℝ)+(9623/100000 : ℝ))=(5000720147457399/5000000000000000 : ℝ) by norm_num, show 1+(5326867115576171/10000000000000000000 : ℝ)+(627648415296837/10000000000000000000 : ℝ)=(625372157220679563/625000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5326867115576171/10000000000000000000 : ℝ) ≤ ((16297526308273268697/16302500000000000000 : ℝ)+2*(113660612591/65210000000000 : ℝ)*(1009/6250 : ℝ))^(8465/2048 : ℝ) := by
    rw [show (16297526308273268697/16302500000000000000 : ℝ)+2*(113660612591/65210000000000 : ℝ)*(1009/6250 : ℝ)=(2500644225260177/2500000000000000 : ℝ) by norm_num, show 1+2*(5326867115576171/10000000000000000000 : ℝ)=(5005326867115576171/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16297526308273268697/16302500000000000000 : ℝ)*(X 1 0+X 2 0)+(113660612591/65210000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (9623/100000 : ℝ)) (hi := (1009/6250 : ℝ)) (c := (16297526308273268697/16302500000000000000 : ℝ)) (alpha := (113660612591/65210000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16297526308273268697/16302500000000000000 : ℝ)*(X 0 1+X 2 1)+(113660612591/65210000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (9623/100000 : ℝ)) (hi := (1009/6250 : ℝ)) (c := (16297526308273268697/16302500000000000000 : ℝ)) (alpha := (113660612591/65210000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16297526308273268697/16302500000000000000 : ℝ)*(X 0 2+X 1 2)+(113660612591/65210000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (9623/100000 : ℝ)) (hi := (1009/6250 : ℝ)) (c := (16297526308273268697/16302500000000000000 : ℝ)) (alpha := (113660612591/65210000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2103171819/10000000000 : ℝ)*X 0 0+(5417011887/10000000000 : ℝ)*X 0 1+(5242927427/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070163227/2000000000 : ℝ)*X 1 0+(-219192987/1000000000 : ℝ)*X 1 1+(1310731847/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334426007/625000000 : ℝ)*X 2 0+(2621463767/5000000000 : ℝ)*X 2 1+(-547982427/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4344984049/10000000000 : ℝ)*X 0 0+(52135713/125000000 : ℝ)*X 0 1+(1131528609/2500000000 : ℝ)*X 0 2+(4344984049/10000000000 : ℝ)*X 1 0+(52135713/125000000 : ℝ)*X 1 1+(1131528609/2500000000 : ℝ)*X 1 2+(4344984049/10000000000 : ℝ)*X 2 0+(52135713/125000000 : ℝ)*X 2 1+(1131528609/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-84127403/400000000 : ℝ)*X 0 0+(2621774047/5000000000 : ℝ)*X 0 1+(5416387831/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5306312331/10000000000 : ℝ)*X 1 0+(-2018468787/10000000000 : ℝ)*X 1 1+(1083277533/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663288951/1250000000 : ℝ)*X 2 0+(1354097027/2500000000 : ℝ)*X 2 1+(-504617291/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4345011223/10000000000 : ℝ)*X 0 0+(1131211637/2500000000 : ℝ)*X 0 1+(130379087/312500000 : ℝ)*X 0 2+(4345011223/10000000000 : ℝ)*X 1 0+(1131211637/2500000000 : ℝ)*X 1 1+(130379087/312500000 : ℝ)*X 1 2+(4345011223/10000000000 : ℝ)*X 2 0+(1131211637/2500000000 : ℝ)*X 2 1+(130379087/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (470414439664186881504068361/203781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26178201/5000000000000 : ℝ)*(base19) + (482087313/100000000000000 : ℝ)*(base23) + (165093/800000000000 : ℝ)*(upper4) + (72242307/100000000000000 : ℝ)*(upper5) + (1069904860430843/25000000000000 : ℝ)*(major0) + (1069904860430843/25000000000000 : ℝ)*(major1) + (1069904860430843/25000000000000 : ℝ)*(major2) + (229774024818227/4000000000000 : ℝ)*(sp0) + (5744363163859067/100000000000000 : ℝ)*(sp1) + (5744365824268239/100000000000000 : ℝ)*(sp2) + (2814866938576357/100000000000000 : ℝ)*(sp3) + (3921474969/25000000000000 : ℝ)*(sp4) + (523786493/20000000000000 : ℝ)*(sp5) + (695195901/12500000000000 : ℝ)*(sp7) + (1407436250071783/50000000000000 : ℝ)*(f.failure) + (179511447073611/3125000000000 : ℝ)*(f.sum) + (390814262043/407562500000000000000000000 : ℝ)*base66 + (5413153674785159071/407562500000000000000000000000000 : ℝ)*base67 + (4619636997846909071/407562500000000000000000000000000 : ℝ)*base69 + (11627817267498659071/407562500000000000000000000000000 : ℝ)*base71 + (2593434305961/1304200000000000000000000000 : ℝ)*base73 + (4336640253794409071/407562500000000000000000000000000 : ℝ)*base75 + (951434402313159071/407562500000000000000000000000000 : ℝ)*base77 + (4863536261085346571/407562500000000000000000000000000 : ℝ)*base79 + (1136649839869/815125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (24783/1250000000000000000000 : ℝ)*base90 + (24783/1250000000000000000000 : ℝ)*base92 + (24783/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (533091809240481064326082551/101890625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3198262341/100000000000000 : ℝ)*(base19) + (2245129757/100000000000000 : ℝ)*(base23) + (495119/800000000000 : ℝ)*(upper3) + (17125147/50000000000000 : ℝ)*(lower4) + (484498393/100000000000000 : ℝ)*(upper5) + (134700751029891/3125000000000 : ℝ)*(major0) + (134700751029891/3125000000000 : ℝ)*(major1) + (134700751029891/3125000000000 : ℝ)*(major2) + (75407855101/100000000000000 : ℝ)*(sp1) + (24029971191/50000000000000 : ℝ)*(sp2) + (1446428502785333/25000000000000 : ℝ)*(sp4) + (5785635405023891/100000000000000 : ℝ)*(sp5) + (2892831853034597/50000000000000 : ℝ)*(sp6) + (2835133880371667/100000000000000 : ℝ)*(sp7) + (2835133880371667/100000000000000 : ℝ)*(f.failure) + (1446428502785333/25000000000000 : ℝ)*(f.sum) + (15756039356977/6521000000000000000000000000 : ℝ)*base66 + (129705937919965777/50945312500000000000000000000000 : ℝ)*base67 + (526068055130778277/50945312500000000000000000000000 : ℝ)*base69 + (207774056269103429/101890625000000000000000000000000 : ℝ)*base71 + (9546885187/260840000000000000000000000 : ℝ)*base73 + (226100101418615321/101890625000000000000000000000000 : ℝ)*base76 + (936957760008709071/101890625000000000000000000000000 : ℝ)*base78 + (95324488526434527/50945312500000000000000000000000 : ℝ)*base79 + (131777215147/101890625000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (10631333/2500000000000000000000 : ℝ)*base89 + (10631333/2500000000000000000000 : ℝ)*base91 + (10631333/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1272_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1009/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9623/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1272_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1272_s4_0 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-32894959/156250000 : ℝ)*x 0 + (2698137321/5000000000 : ℝ)*x 1 + (1052456863/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32894959/156250000 : ℝ)^4233 ≤ (3201220793017/25000000000000 : ℝ)^3209 := by
    have hnat : (32894959 : ℕ)^4233*25000000000000^3209 ≤ 3201220793017^3209*156250000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32894959 156250000 3201220793017 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698137321/5000000000 : ℝ)^4233 ≤ (44320492563017/100000000000000 : ℝ)^3209 := by
    have hnat : (2698137321 : ℕ)^4233*100000000000000^3209 ≤ 44320492563017^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698137321 5000000000 44320492563017 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052456863/2000000000 : ℝ)^4233 ≤ (8574924849963/20000000000000 : ℝ)^3209 := by
    have hnat : (1052456863 : ℕ)^4233*20000000000000^3209 ≤ 8574924849963^3209*2000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052456863 2000000000 8574924849963 20000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-32894959/156250000 : ℝ), (2698137321/5000000000 : ℝ), (1052456863/2000000000 : ℝ)] ![(3201220793017/25000000000000 : ℝ), (44320492563017/100000000000000 : ℝ), (8574924849963/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-32894959/156250000 : ℝ)|^4233 ≤ (3201220793017/25000000000000 : ℝ)^3209
        have hw : |(-32894959/156250000 : ℝ)|=(32894959/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698137321/5000000000 : ℝ)|^4233 ≤ (44320492563017/100000000000000 : ℝ)^3209
        have hw : |(2698137321/5000000000 : ℝ)|=(2698137321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052456863/2000000000 : ℝ)|^4233 ≤ (8574924849963/20000000000000 : ℝ)^3209
        have hw : |(1052456863/2000000000 : ℝ)|=(1052456863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s4_1 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345574173/10000000000 : ℝ)*x 0 + (-543322387/2500000000 : ℝ)*x 1 + (2631142157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345574173/10000000000 : ℝ)^4233 ≤ (43772028539847/100000000000000 : ℝ)^3209 := by
    have hnat : (5345574173 : ℕ)^4233*100000000000000^3209 ≤ 43772028539847^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345574173 10000000000 43772028539847 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543322387/2500000000 : ℝ)^4233 ≤ (13353347209677/100000000000000 : ℝ)^3209 := by
    have hnat : (543322387 : ℕ)^4233*100000000000000^3209 ≤ 13353347209677^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543322387 2500000000 13353347209677 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631142157/5000000000 : ℝ)^4233 ≤ (10718656059767/25000000000000 : ℝ)^3209 := by
    have hnat : (2631142157 : ℕ)^4233*25000000000000^3209 ≤ 10718656059767^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631142157 5000000000 10718656059767 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345574173/10000000000 : ℝ), (-543322387/2500000000 : ℝ), (2631142157/5000000000 : ℝ)] ![(43772028539847/100000000000000 : ℝ), (13353347209677/100000000000000 : ℝ), (10718656059767/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345574173/10000000000 : ℝ)|^4233 ≤ (43772028539847/100000000000000 : ℝ)^3209
        have hw : |(5345574173/10000000000 : ℝ)|=(5345574173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-543322387/2500000000 : ℝ)|^4233 ≤ (13353347209677/100000000000000 : ℝ)^3209
        have hw : |(-543322387/2500000000 : ℝ)|=(543322387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631142157/5000000000 : ℝ)|^4233 ≤ (10718656059767/25000000000000 : ℝ)^3209
        have hw : |(2631142157/5000000000 : ℝ)|=(2631142157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s4_2 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672787087/5000000000 : ℝ)*x 0 + (1315571079/2500000000 : ℝ)*x 1 + (-271661193/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672787087/5000000000 : ℝ)^4233 ≤ (43772028550649/100000000000000 : ℝ)^3209 := by
    have hnat : (2672787087 : ℕ)^4233*100000000000000^3209 ≤ 43772028550649^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672787087 5000000000 43772028550649 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315571079/2500000000 : ℝ)^4233 ≤ (42874624260563/100000000000000 : ℝ)^3209 := by
    have hnat : (1315571079 : ℕ)^4233*100000000000000^3209 ≤ 42874624260563^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315571079 2500000000 42874624260563 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271661193/1250000000 : ℝ)^4233 ≤ (13353347177257/100000000000000 : ℝ)^3209 := by
    have hnat : (271661193 : ℕ)^4233*100000000000000^3209 ≤ 13353347177257^3209*1250000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271661193 1250000000 13353347177257 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672787087/5000000000 : ℝ), (1315571079/2500000000 : ℝ), (-271661193/1250000000 : ℝ)] ![(43772028550649/100000000000000 : ℝ), (42874624260563/100000000000000 : ℝ), (13353347177257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672787087/5000000000 : ℝ)|^4233 ≤ (43772028550649/100000000000000 : ℝ)^3209
        have hw : |(2672787087/5000000000 : ℝ)|=(2672787087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315571079/2500000000 : ℝ)|^4233 ≤ (42874624260563/100000000000000 : ℝ)^3209
        have hw : |(1315571079/2500000000 : ℝ)|=(1315571079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-271661193/1250000000 : ℝ)|^4233 ≤ (13353347177257/100000000000000 : ℝ)^3209
        have hw : |(-271661193/1250000000 : ℝ)|=(271661193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s4_3 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (271640601/625000000 : ℝ)*x 0 + (4211606677/10000000000 : ℝ)*x 1 + (4485043403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271640601/625000000 : ℝ)^4233 ≤ (8328679502603/25000000000000 : ℝ)^3209 := by
    have hnat : (271640601 : ℕ)^4233*25000000000000^3209 ≤ 8328679502603^3209*625000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271640601 625000000 8328679502603 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4211606677/10000000000 : ℝ)^4233 ≤ (31960101679701/100000000000000 : ℝ)^3209 := by
    have hnat : (4211606677 : ℕ)^4233*100000000000000^3209 ≤ 31960101679701^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211606677 10000000000 31960101679701 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4485043403/10000000000 : ℝ)^4233 ≤ (4340647536609/12500000000000 : ℝ)^3209 := by
    have hnat : (4485043403 : ℕ)^4233*12500000000000^3209 ≤ 4340647536609^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485043403 10000000000 4340647536609 12500000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271640601/625000000 : ℝ), (4211606677/10000000000 : ℝ), (4485043403/10000000000 : ℝ)] ![(8328679502603/25000000000000 : ℝ), (31960101679701/100000000000000 : ℝ), (4340647536609/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271640601/625000000 : ℝ)|^4233 ≤ (8328679502603/25000000000000 : ℝ)^3209
        have hw : |(271640601/625000000 : ℝ)|=(271640601/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4211606677/10000000000 : ℝ)|^4233 ≤ (31960101679701/100000000000000 : ℝ)^3209
        have hw : |(4211606677/10000000000 : ℝ)|=(4211606677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4485043403/10000000000 : ℝ)|^4233 ≤ (4340647536609/12500000000000 : ℝ)^3209
        have hw : |(4485043403/10000000000 : ℝ)|=(4485043403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s4_4 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-526320841/2500000000 : ℝ)*x 0 + (5262652633/10000000000 : ℝ)*x 1 + (215836193/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526320841/2500000000 : ℝ)^4233 ≤ (2560986242941/20000000000000 : ℝ)^3209 := by
    have hnat : (526320841 : ℕ)^4233*20000000000000^3209 ≤ 2560986242941^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526320841 2500000000 2560986242941 20000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262652633/10000000000 : ℝ)^4233 ≤ (10719645691359/25000000000000 : ℝ)^3209 := by
    have hnat : (5262652633 : ℕ)^4233*25000000000000^3209 ≤ 10719645691359^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262652633 10000000000 10719645691359 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215836193/400000000 : ℝ)^4233 ≤ (4431648600711/10000000000000 : ℝ)^3209 := by
    have hnat : (215836193 : ℕ)^4233*10000000000000^3209 ≤ 4431648600711^3209*400000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215836193 400000000 4431648600711 10000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-526320841/2500000000 : ℝ), (5262652633/10000000000 : ℝ), (215836193/400000000 : ℝ)] ![(2560986242941/20000000000000 : ℝ), (10719645691359/25000000000000 : ℝ), (4431648600711/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-526320841/2500000000 : ℝ)|^4233 ≤ (2560986242941/20000000000000 : ℝ)^3209
        have hw : |(-526320841/2500000000 : ℝ)|=(526320841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262652633/10000000000 : ℝ)|^4233 ≤ (10719645691359/25000000000000 : ℝ)^3209
        have hw : |(5262652633/10000000000 : ℝ)|=(5262652633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215836193/400000000 : ℝ)|^4233 ≤ (4431648600711/10000000000000 : ℝ)^3209
        have hw : |(215836193/400000000 : ℝ)|=(215836193/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s4_5 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2655658447/5000000000 : ℝ)*x 0 + (-509917243/2500000000 : ℝ)*x 1 + (1348976219/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655658447/5000000000 : ℝ)^4233 ≤ (542529752151/1250000000000 : ℝ)^3209 := by
    have hnat : (2655658447 : ℕ)^4233*1250000000000^3209 ≤ 542529752151^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655658447 5000000000 542529752151 1250000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (509917243/2500000000 : ℝ)^4233 ≤ (153514165609/1250000000000 : ℝ)^3209 := by
    have hnat : (509917243 : ℕ)^4233*1250000000000^3209 ≤ 153514165609^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509917243 2500000000 153514165609 1250000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348976219/2500000000 : ℝ)^4233 ≤ (2769780409977/6250000000000 : ℝ)^3209 := by
    have hnat : (1348976219 : ℕ)^4233*6250000000000^3209 ≤ 2769780409977^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348976219 2500000000 2769780409977 6250000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655658447/5000000000 : ℝ), (-509917243/2500000000 : ℝ), (1348976219/2500000000 : ℝ)] ![(542529752151/1250000000000 : ℝ), (153514165609/1250000000000 : ℝ), (2769780409977/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655658447/5000000000 : ℝ)|^4233 ≤ (542529752151/1250000000000 : ℝ)^3209
        have hw : |(2655658447/5000000000 : ℝ)|=(2655658447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-509917243/2500000000 : ℝ)|^4233 ≤ (153514165609/1250000000000 : ℝ)^3209
        have hw : |(-509917243/2500000000 : ℝ)|=(509917243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348976219/2500000000 : ℝ)|^4233 ≤ (2769780409977/6250000000000 : ℝ)^3209
        have hw : |(1348976219/2500000000 : ℝ)|=(1348976219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s4_6 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062263397/2000000000 : ℝ)*x 0 + (337244047/625000000 : ℝ)*x 1 + (-1019834509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062263397/2000000000 : ℝ)^4233 ≤ (8680476230599/20000000000000 : ℝ)^3209 := by
    have hnat : (1062263397 : ℕ)^4233*20000000000000^3209 ≤ 8680476230599^3209*2000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062263397 2000000000 8680476230599 20000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337244047/625000000 : ℝ)^4233 ≤ (8863297043249/20000000000000 : ℝ)^3209 := by
    have hnat : (337244047 : ℕ)^4233*20000000000000^3209 ≤ 8863297043249^3209*625000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337244047 625000000 8863297043249 20000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1019834509/5000000000 : ℝ)^4233 ≤ (491245344563/4000000000000 : ℝ)^3209 := by
    have hnat : (1019834509 : ℕ)^4233*4000000000000^3209 ≤ 491245344563^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019834509 5000000000 491245344563 4000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062263397/2000000000 : ℝ), (337244047/625000000 : ℝ), (-1019834509/5000000000 : ℝ)] ![(8680476230599/20000000000000 : ℝ), (8863297043249/20000000000000 : ℝ), (491245344563/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062263397/2000000000 : ℝ)|^4233 ≤ (8680476230599/20000000000000 : ℝ)^3209
        have hw : |(1062263397/2000000000 : ℝ)|=(1062263397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337244047/625000000 : ℝ)|^4233 ≤ (8863297043249/20000000000000 : ℝ)^3209
        have hw : |(337244047/625000000 : ℝ)|=(337244047/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1019834509/5000000000 : ℝ)|^4233 ≤ (491245344563/4000000000000 : ℝ)^3209
        have hw : |(-1019834509/5000000000 : ℝ)|=(1019834509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s4_7 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (434626179/1000000000 : ℝ)*x 0 + (896858319/2000000000 : ℝ)*x 1 + (4212361389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434626179/1000000000 : ℝ)^4233 ≤ (16657420551729/50000000000000 : ℝ)^3209 := by
    have hnat : (434626179 : ℕ)^4233*50000000000000^3209 ≤ 16657420551729^3209*1000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434626179 1000000000 16657420551729 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (896858319/2000000000 : ℝ)^4233 ≤ (17358751114351/50000000000000 : ℝ)^3209 := by
    have hnat : (896858319 : ℕ)^4233*50000000000000^3209 ≤ 17358751114351^3209*2000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896858319 2000000000 17358751114351 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4212361389/10000000000 : ℝ)^4233 ≤ (3196765664667/10000000000000 : ℝ)^3209 := by
    have hnat : (4212361389 : ℕ)^4233*10000000000000^3209 ≤ 3196765664667^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4212361389 10000000000 3196765664667 10000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434626179/1000000000 : ℝ), (896858319/2000000000 : ℝ), (4212361389/10000000000 : ℝ)] ![(16657420551729/50000000000000 : ℝ), (17358751114351/50000000000000 : ℝ), (3196765664667/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434626179/1000000000 : ℝ)|^4233 ≤ (16657420551729/50000000000000 : ℝ)^3209
        have hw : |(434626179/1000000000 : ℝ)|=(434626179/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(896858319/2000000000 : ℝ)|^4233 ≤ (17358751114351/50000000000000 : ℝ)^3209
        have hw : |(896858319/2000000000 : ℝ)|=(896858319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4212361389/10000000000 : ℝ)|^4233 ≤ (3196765664667/10000000000000 : ℝ)^3209
        have hw : |(4212361389/10000000000 : ℝ)|=(4212361389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1272_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11401/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (89/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7337/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10989/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7337/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10989/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7337/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10989/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7337/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10989/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7337/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10989/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7337/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10989/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10989/100000 : ℝ) ^ (8465/2048 : ℝ) ≤ (2172809565170857/20000000000000000000 : ℝ) := by
    have hpowers : (10989/100000 : ℝ)^8465 ≤ (2172809565170857/20000000000000000000 : ℝ)^2048 := by
      have hnat : (10989 : ℕ)^8465*20000000000000000000^2048 ≤ 2172809565170857^2048*100000^8465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10989 100000 2172809565170857 20000000000000000000 8465 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10989/100000 : ℝ)) (X := (2172809565170857/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7337/50000 : ℝ) ^ (8465/2048 : ℝ) ≤ (17949994885545733/50000000000000000000 : ℝ) := by
    have hpowers : (7337/50000 : ℝ)^8465 ≤ (17949994885545733/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7337 : ℕ)^8465*50000000000000000000^2048 ≤ 17949994885545733^2048*50000^8465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7337 50000 17949994885545733 50000000000000000000 8465 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7337/50000 : ℝ)) (X := (17949994885545733/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002172809565170857/10000000000000000000 : ℝ) ≤ (2500131410146419/2500000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (10002172809565170857/10000000000000000000 : ℝ)^2048 ≤ (2500131410146419/2500000000000000 : ℝ)^8465 := by
      have hnat : (10002172809565170857 : ℕ)^2048*2500000000000000^8465 ≤ 2500131410146419^8465*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002172809565170857 10000000000000000000 2500131410146419 2500000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500131410146419/2500000000000000 : ℝ)) (X := (10002172809565170857/10000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046764037596945751/100000000000000000000 : ℝ) ≤ (2500282799107787/2500000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (100046764037596945751/100000000000000000000 : ℝ)^2048 ≤ (2500282799107787/2500000000000000 : ℝ)^8465 := by
      have hnat : (100046764037596945751 : ℕ)^2048*2500000000000000^8465 ≤ 2500282799107787^8465*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046764037596945751 100000000000000000000 2500282799107787 2500000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500282799107787/2500000000000000 : ℝ)) (X := (100046764037596945751/100000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017949994885545733/25000000000000000000 : ℝ) ≤ (500086837613831/500000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (25017949994885545733/25000000000000000000 : ℝ)^2048 ≤ (500086837613831/500000000000000 : ℝ)^8465 := by
      have hnat : (25017949994885545733 : ℕ)^2048*500000000000000^8465 ≤ 500086837613831^8465*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017949994885545733 25000000000000000000 500086837613831 500000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500086837613831/500000000000000 : ℝ)) (X := (25017949994885545733/25000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2172809565170857/20000000000000000000 : ℝ) ≤ ((837241547254237101/837500000000000000 : ℝ)+2*(18923620171/11515625000000 : ℝ)*(10989/100000 : ℝ))^(8465/2048 : ℝ) := by
    rw [show (837241547254237101/837500000000000000 : ℝ)+2*(18923620171/11515625000000 : ℝ)*(10989/100000 : ℝ)=(2500131410146419/2500000000000000 : ℝ) by norm_num, show 1+2*(2172809565170857/20000000000000000000 : ℝ)=(10002172809565170857/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17949994885545733/50000000000000000000 : ℝ)+(2172809565170857/20000000000000000000 : ℝ) ≤ ((837241547254237101/837500000000000000 : ℝ)+(18923620171/11515625000000 : ℝ)*((7337/50000 : ℝ)+(10989/100000 : ℝ)))^(8465/2048 : ℝ) := by
    rw [show (837241547254237101/837500000000000000 : ℝ)+(18923620171/11515625000000 : ℝ)*((7337/50000 : ℝ)+(10989/100000 : ℝ))=(2500282799107787/2500000000000000 : ℝ) by norm_num, show 1+(17949994885545733/50000000000000000000 : ℝ)+(2172809565170857/20000000000000000000 : ℝ)=(100046764037596945751/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17949994885545733/50000000000000000000 : ℝ) ≤ ((837241547254237101/837500000000000000 : ℝ)+2*(18923620171/11515625000000 : ℝ)*(7337/50000 : ℝ))^(8465/2048 : ℝ) := by
    rw [show (837241547254237101/837500000000000000 : ℝ)+2*(18923620171/11515625000000 : ℝ)*(7337/50000 : ℝ)=(500086837613831/500000000000000 : ℝ) by norm_num, show 1+2*(17949994885545733/50000000000000000000 : ℝ)=(25017949994885545733/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (837241547254237101/837500000000000000 : ℝ)*(X 1 0+X 2 0)+(18923620171/11515625000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (10989/100000 : ℝ)) (hi := (7337/50000 : ℝ)) (c := (837241547254237101/837500000000000000 : ℝ)) (alpha := (18923620171/11515625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (837241547254237101/837500000000000000 : ℝ)*(X 0 1+X 2 1)+(18923620171/11515625000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (10989/100000 : ℝ)) (hi := (7337/50000 : ℝ)) (c := (837241547254237101/837500000000000000 : ℝ)) (alpha := (18923620171/11515625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (837241547254237101/837500000000000000 : ℝ)*(X 0 2+X 1 2)+(18923620171/11515625000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (10989/100000 : ℝ)) (hi := (7337/50000 : ℝ)) (c := (837241547254237101/837500000000000000 : ℝ)) (alpha := (18923620171/11515625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-32894959/156250000 : ℝ)*X 0 0+(2698137321/5000000000 : ℝ)*X 0 1+(1052456863/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345574173/10000000000 : ℝ)*X 1 0+(-543322387/2500000000 : ℝ)*X 1 1+(2631142157/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672787087/5000000000 : ℝ)*X 2 0+(1315571079/2500000000 : ℝ)*X 2 1+(-271661193/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((271640601/625000000 : ℝ)*X 0 0+(4211606677/10000000000 : ℝ)*X 0 1+(4485043403/10000000000 : ℝ)*X 0 2+(271640601/625000000 : ℝ)*X 1 0+(4211606677/10000000000 : ℝ)*X 1 1+(4485043403/10000000000 : ℝ)*X 1 2+(271640601/625000000 : ℝ)*X 2 0+(4211606677/10000000000 : ℝ)*X 2 1+(4485043403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-526320841/2500000000 : ℝ)*X 0 0+(5262652633/10000000000 : ℝ)*X 0 1+(215836193/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655658447/5000000000 : ℝ)*X 1 0+(-509917243/2500000000 : ℝ)*X 1 1+(1348976219/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062263397/2000000000 : ℝ)*X 2 0+(337244047/625000000 : ℝ)*X 2 1+(-1019834509/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((434626179/1000000000 : ℝ)*X 0 0+(896858319/2000000000 : ℝ)*X 0 1+(4212361389/10000000000 : ℝ)*X 0 2+(434626179/1000000000 : ℝ)*X 1 0+(896858319/2000000000 : ℝ)*X 1 1+(4212361389/10000000000 : ℝ)*X 1 2+(434626179/1000000000 : ℝ)*X 2 0+(896858319/2000000000 : ℝ)*X 2 1+(4212361389/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2362814597572084028801880741/230312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (247896123/12500000000000 : ℝ)*(base19) + (461768267/25000000000000 : ℝ)*(base23) + (36748707/50000000000000 : ℝ)*(lower2) + (51362671/20000000000000 : ℝ)*(upper3) + (161295771/100000000000000 : ℝ)*(upper5) + (5560267143828777/100000000000000 : ℝ)*(major0) + (5560267143828777/100000000000000 : ℝ)*(major1) + (5560267143828777/100000000000000 : ℝ)*(major2) + (7463278499301109/100000000000000 : ℝ)*(sp0) + (7463327556903843/100000000000000 : ℝ)*(sp1) + (7463327692999759/100000000000000 : ℝ)*(sp2) + (1828588736426161/50000000000000 : ℝ)*(sp3) + (25520385859/50000000000000 : ℝ)*(sp4) + (13466380067/50000000000000 : ℝ)*(sp7) + (457150550701557/12500000000000 : ℝ)*(f.failure) + (7463329540072827/100000000000000 : ℝ)*(f.sum) + (7946089260639/4606250000000000000000000000 : ℝ)*base66 + (6704108070267989753/921250000000000000000000000000000 : ℝ)*base68 + (10267229810014239753/921250000000000000000000000000000 : ℝ)*base70 + (14537585126686739753/921250000000000000000000000000000 : ℝ)*base72 + (12046765349343/2303125000000000000000000000 : ℝ)*base73 + (11665269251824510247/921250000000000000000000000000000 : ℝ)*base75 + (15747533897060489753/921250000000000000000000000000000 : ℝ)*base78 + (9904225057972989753/921250000000000000000000000000000 : ℝ)*base80 + (22132727292861/4606250000000000000000000000 : ℝ)*base81 + (1186443/312500000000000000000 : ℝ)*base89 + (1186443/312500000000000000000 : ℝ)*base91 + (1186443/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2263318298716355091993997923/230312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2035130321/100000000000000 : ℝ)*(base19) + (225433641/10000000000000 : ℝ)*(base23) + (101281343/50000000000000 : ℝ)*(upper3) + (5361813/10000000000000 : ℝ)*(lower4) + (266940273/100000000000000 : ℝ)*(upper5) + (2795495733268269/50000000000000 : ℝ)*(major0) + (2795495733268269/50000000000000 : ℝ)*(major1) + (2795495733268269/50000000000000 : ℝ)*(major2) + (11565644793/20000000000000 : ℝ)*(sp1) + (28114006577/50000000000000 : ℝ)*(sp2) + (1876142403849489/25000000000000 : ℝ)*(sp4) + (750450975204367/10000000000000 : ℝ)*(sp5) + (938063891631049/12500000000000 : ℝ)*(sp6) + (1436489449259/39062500000 : ℝ)*(sp7) + (1436489449259/39062500000 : ℝ)*(f.failure) + (1876142403849489/25000000000000 : ℝ)*(f.sum) + (2865700423821/1151562500000000000000000000 : ℝ)*base65 + (2769675729401029859/460625000000000000000000000000000 : ℝ)*base67 + (2376258997561029859/460625000000000000000000000000000 : ℝ)*base69 + (1223708828254595141/460625000000000000000000000000000 : ℝ)*base72 + (10287386263391/4606250000000000000000000000 : ℝ)*base74 + (5904286182867279859/460625000000000000000000000000000 : ℝ)*base75 + (3423837858970141/460625000000000000000000000000000 : ℝ)*base78 + (10928066140588529859/460625000000000000000000000000000 : ℝ)*base79 + (1214454016173/575781250000000000000000000 : ℝ)*base81 + (11339/3906250000000000000 : ℝ)*base89 + (11339/3906250000000000000 : ℝ)*base91 + (11339/3906250000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1272_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11401/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (89/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1272_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1272_s5_0 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2105682397/10000000000 : ℝ)*x 0 + (1347919251/2500000000 : ℝ)*x 1 + (5266615427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105682397/10000000000 : ℝ)^4233 ≤ (12808132815571/100000000000000 : ℝ)^3209 := by
    have hnat : (2105682397 : ℕ)^4233*100000000000000^3209 ≤ 12808132815571^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105682397 10000000000 12808132815571 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347919251/2500000000 : ℝ)^4233 ≤ (8854137699267/20000000000000 : ℝ)^3209 := by
    have hnat : (1347919251 : ℕ)^4233*20000000000000^3209 ≤ 8854137699267^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347919251 2500000000 8854137699267 20000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266615427/10000000000 : ℝ)^4233 ≤ (13412868337/31250000000 : ℝ)^3209 := by
    have hnat : (5266615427 : ℕ)^4233*31250000000^3209 ≤ 13412868337^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266615427 10000000000 13412868337 31250000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2105682397/10000000000 : ℝ), (1347919251/2500000000 : ℝ), (5266615427/10000000000 : ℝ)] ![(12808132815571/100000000000000 : ℝ), (8854137699267/20000000000000 : ℝ), (13412868337/31250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2105682397/10000000000 : ℝ)|^4233 ≤ (12808132815571/100000000000000 : ℝ)^3209
        have hw : |(-2105682397/10000000000 : ℝ)|=(2105682397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347919251/2500000000 : ℝ)|^4233 ≤ (8854137699267/20000000000000 : ℝ)^3209
        have hw : |(1347919251/2500000000 : ℝ)|=(1347919251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266615427/10000000000 : ℝ)|^4233 ≤ (13412868337/31250000000 : ℝ)^3209
        have hw : |(5266615427/10000000000 : ℝ)|=(5266615427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s5_1 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (13361021/25000000 : ℝ)*x 0 + (-2169097529/10000000000 : ℝ)*x 1 + (526661569/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13361021/25000000 : ℝ)^4233 ≤ (350075495791/800000000000 : ℝ)^3209 := by
    have hnat : (13361021 : ℕ)^4233*800000000000^3209 ≤ 350075495791^3209*25000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13361021 25000000 350075495791 800000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2169097529/10000000000 : ℝ)^4233 ≤ (6659690753319/50000000000000 : ℝ)^3209 := by
    have hnat : (2169097529 : ℕ)^4233*50000000000000^3209 ≤ 6659690753319^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169097529 10000000000 6659690753319 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526661569/1000000000 : ℝ)^4233 ≤ (10730295376429/25000000000000 : ℝ)^3209 := by
    have hnat : (526661569 : ℕ)^4233*25000000000000^3209 ≤ 10730295376429^3209*1000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526661569 1000000000 10730295376429 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13361021/25000000 : ℝ), (-2169097529/10000000000 : ℝ), (526661569/1000000000 : ℝ)] ![(350075495791/800000000000 : ℝ), (6659690753319/50000000000000 : ℝ), (10730295376429/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13361021/25000000 : ℝ)|^4233 ≤ (350075495791/800000000000 : ℝ)^3209
        have hw : |(13361021/25000000 : ℝ)|=(13361021/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2169097529/10000000000 : ℝ)|^4233 ≤ (6659690753319/50000000000000 : ℝ)^3209
        have hw : |(-2169097529/10000000000 : ℝ)|=(2169097529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526661569/1000000000 : ℝ)|^4233 ≤ (10730295376429/25000000000000 : ℝ)^3209
        have hw : |(526661569/1000000000 : ℝ)|=(526661569/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s5_2 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344407463/10000000000 : ℝ)*x 0 + (5266616661/10000000000 : ℝ)*x 1 + (-216909749/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344407463/10000000000 : ℝ)^4233 ≤ (43759426853649/100000000000000 : ℝ)^3209 := by
    have hnat : (5344407463 : ℕ)^4233*100000000000000^3209 ≤ 43759426853649^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344407463 10000000000 43759426853649 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266616661/10000000000 : ℝ)^4233 ≤ (42921191944209/100000000000000 : ℝ)^3209 := by
    have hnat : (5266616661 : ℕ)^4233*100000000000000^3209 ≤ 42921191944209^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266616661 10000000000 42921191944209 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216909749/1000000000 : ℝ)^4233 ≤ (13319381190739/100000000000000 : ℝ)^3209 := by
    have hnat : (216909749 : ℕ)^4233*100000000000000^3209 ≤ 13319381190739^3209*1000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216909749 1000000000 13319381190739 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344407463/10000000000 : ℝ), (5266616661/10000000000 : ℝ), (-216909749/1000000000 : ℝ)] ![(43759426853649/100000000000000 : ℝ), (42921191944209/100000000000000 : ℝ), (13319381190739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344407463/10000000000 : ℝ)|^4233 ≤ (43759426853649/100000000000000 : ℝ)^3209
        have hw : |(5344407463/10000000000 : ℝ)|=(5344407463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266616661/10000000000 : ℝ)|^4233 ≤ (42921191944209/100000000000000 : ℝ)^3209
        have hw : |(5266616661/10000000000 : ℝ)|=(5266616661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-216909749/1000000000 : ℝ)|^4233 ≤ (13319381190739/100000000000000 : ℝ)^3209
        have hw : |(-216909749/1000000000 : ℝ)|=(216909749/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s5_3 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4346486747/10000000000 : ℝ)*x 0 + (168827541/400000000 : ℝ)*x 1 + (2237950617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346486747/10000000000 : ℝ)^4233 ≤ (33317115695493/100000000000000 : ℝ)^3209 := by
    have hnat : (4346486747 : ℕ)^4233*100000000000000^3209 ≤ 33317115695493^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346486747 10000000000 33317115695493 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168827541/400000000 : ℝ)^4233 ≤ (641020865001/2000000000000 : ℝ)^3209 := by
    have hnat : (168827541 : ℕ)^4233*2000000000000^3209 ≤ 641020865001^3209*400000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168827541 400000000 641020865001 2000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2237950617/5000000000 : ℝ)^4233 ≤ (17315920519569/50000000000000 : ℝ)^3209 := by
    have hnat : (2237950617 : ℕ)^4233*50000000000000^3209 ≤ 17315920519569^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237950617 5000000000 17315920519569 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346486747/10000000000 : ℝ), (168827541/400000000 : ℝ), (2237950617/5000000000 : ℝ)] ![(33317115695493/100000000000000 : ℝ), (641020865001/2000000000000 : ℝ), (17315920519569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346486747/10000000000 : ℝ)|^4233 ≤ (33317115695493/100000000000000 : ℝ)^3209
        have hw : |(4346486747/10000000000 : ℝ)|=(4346486747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168827541/400000000 : ℝ)|^4233 ≤ (641020865001/2000000000000 : ℝ)^3209
        have hw : |(168827541/400000000 : ℝ)|=(168827541/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2237950617/5000000000 : ℝ)|^4233 ≤ (17315920519569/50000000000000 : ℝ)^3209
        have hw : |(2237950617/5000000000 : ℝ)|=(2237950617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s5_4 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2105686543/10000000000 : ℝ)*x 0 + (2633468677/5000000000 : ℝ)*x 1 + (5391354401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105686543/10000000000 : ℝ)^4233 ≤ (6404083040799/50000000000000 : ℝ)^3209 := by
    have hnat : (2105686543 : ℕ)^4233*50000000000000^3209 ≤ 6404083040799^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105686543 10000000000 6404083040799 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633468677/5000000000 : ℝ)^4233 ≤ (8584927901609/20000000000000 : ℝ)^3209 := by
    have hnat : (2633468677 : ℕ)^4233*20000000000000^3209 ≤ 8584927901609^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633468677 5000000000 8584927901609 20000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391354401/10000000000 : ℝ)^4233 ≤ (22133597198627/50000000000000 : ℝ)^3209 := by
    have hnat : (5391354401 : ℕ)^4233*50000000000000^3209 ≤ 22133597198627^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391354401 10000000000 22133597198627 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2105686543/10000000000 : ℝ), (2633468677/5000000000 : ℝ), (5391354401/10000000000 : ℝ)] ![(6404083040799/50000000000000 : ℝ), (8584927901609/20000000000000 : ℝ), (22133597198627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2105686543/10000000000 : ℝ)|^4233 ≤ (6404083040799/50000000000000 : ℝ)^3209
        have hw : |(-2105686543/10000000000 : ℝ)|=(2105686543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633468677/5000000000 : ℝ)|^4233 ≤ (8584927901609/20000000000000 : ℝ)^3209
        have hw : |(2633468677/5000000000 : ℝ)|=(2633468677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391354401/10000000000 : ℝ)|^4233 ≤ (22133597198627/50000000000000 : ℝ)^3209
        have hw : |(5391354401/10000000000 : ℝ)|=(5391354401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s5_5 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062486411/2000000000 : ℝ)*x 0 + (-2044359883/10000000000 : ℝ)*x 1 + (5391354391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062486411/2000000000 : ℝ)^4233 ≤ (43414401211033/100000000000000 : ℝ)^3209 := by
    have hnat : (1062486411 : ℕ)^4233*100000000000000^3209 ≤ 43414401211033^3209*2000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062486411 2000000000 43414401211033 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2044359883/10000000000 : ℝ)^4233 ≤ (12318404480617/100000000000000 : ℝ)^3209 := by
    have hnat : (2044359883 : ℕ)^4233*100000000000000^3209 ≤ 12318404480617^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044359883 10000000000 12318404480617 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391354391/10000000000 : ℝ)^4233 ≤ (22133597144473/50000000000000 : ℝ)^3209 := by
    have hnat : (5391354391 : ℕ)^4233*50000000000000^3209 ≤ 22133597144473^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391354391 10000000000 22133597144473 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062486411/2000000000 : ℝ), (-2044359883/10000000000 : ℝ), (5391354391/10000000000 : ℝ)] ![(43414401211033/100000000000000 : ℝ), (12318404480617/100000000000000 : ℝ), (22133597144473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062486411/2000000000 : ℝ)|^4233 ≤ (43414401211033/100000000000000 : ℝ)^3209
        have hw : |(1062486411/2000000000 : ℝ)|=(1062486411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2044359883/10000000000 : ℝ)|^4233 ≤ (12318404480617/100000000000000 : ℝ)^3209
        have hw : |(-2044359883/10000000000 : ℝ)|=(2044359883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391354391/10000000000 : ℝ)|^4233 ≤ (22133597144473/50000000000000 : ℝ)^3209
        have hw : |(5391354391/10000000000 : ℝ)|=(5391354391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s5_6 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656216033/5000000000 : ℝ)*x 0 + (2695677193/5000000000 : ℝ)*x 1 + (-16354879/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656216033/5000000000 : ℝ)^4233 ≤ (21707200664807/50000000000000 : ℝ)^3209 := by
    have hnat : (2656216033 : ℕ)^4233*50000000000000^3209 ≤ 21707200664807^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656216033 5000000000 21707200664807 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695677193/5000000000 : ℝ)^4233 ≤ (5533399279349/12500000000000 : ℝ)^3209 := by
    have hnat : (2695677193 : ℕ)^4233*12500000000000^3209 ≤ 5533399279349^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695677193 5000000000 5533399279349 12500000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16354879/80000000 : ℝ)^4233 ≤ (12318404417031/100000000000000 : ℝ)^3209 := by
    have hnat : (16354879 : ℕ)^4233*100000000000000^3209 ≤ 12318404417031^3209*80000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16354879 80000000 12318404417031 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656216033/5000000000 : ℝ), (2695677193/5000000000 : ℝ), (-16354879/80000000 : ℝ)] ![(21707200664807/50000000000000 : ℝ), (5533399279349/12500000000000 : ℝ), (12318404417031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656216033/5000000000 : ℝ)|^4233 ≤ (21707200664807/50000000000000 : ℝ)^3209
        have hw : |(2656216033/5000000000 : ℝ)|=(2656216033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695677193/5000000000 : ℝ)|^4233 ≤ (5533399279349/12500000000000 : ℝ)^3209
        have hw : |(2695677193/5000000000 : ℝ)|=(2695677193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-16354879/80000000 : ℝ)|^4233 ≤ (12318404417031/100000000000000 : ℝ)^3209
        have hw : |(-16354879/80000000 : ℝ)|=(16354879/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s5_7 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4346496531/10000000000 : ℝ)*x 0 + (4475246283/10000000000 : ℝ)*x 1 + (2110672977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346496531/10000000000 : ℝ)^4233 ≤ (33317214624623/100000000000000 : ℝ)^3209 := by
    have hnat : (4346496531 : ℕ)^4233*100000000000000^3209 ≤ 33317214624623^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346496531 10000000000 33317214624623 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4475246283/10000000000 : ℝ)^4233 ≤ (4328144560893/12500000000000 : ℝ)^3209 := by
    have hnat : (4475246283 : ℕ)^4233*12500000000000^3209 ≤ 4328144560893^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475246283 10000000000 4328144560893 12500000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2110672977/5000000000 : ℝ)^4233 ≤ (16028814438061/50000000000000 : ℝ)^3209 := by
    have hnat : (2110672977 : ℕ)^4233*50000000000000^3209 ≤ 16028814438061^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110672977 5000000000 16028814438061 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346496531/10000000000 : ℝ), (4475246283/10000000000 : ℝ), (2110672977/5000000000 : ℝ)] ![(33317214624623/100000000000000 : ℝ), (4328144560893/12500000000000 : ℝ), (16028814438061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346496531/10000000000 : ℝ)|^4233 ≤ (33317214624623/100000000000000 : ℝ)^3209
        have hw : |(4346496531/10000000000 : ℝ)|=(4346496531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4475246283/10000000000 : ℝ)|^4233 ≤ (4328144560893/12500000000000 : ℝ)^3209
        have hw : |(4475246283/10000000000 : ℝ)|=(4475246283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2110672977/5000000000 : ℝ)|^4233 ≤ (16028814438061/50000000000000 : ℝ)^3209
        have hw : |(2110672977/5000000000 : ℝ)|=(2110672977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s5_8 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-28653433/10000000000 : ℝ)*x 0 + (5910804413/10000000000 : ℝ)*x 1 + (591079239/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (28653433/10000000000 : ℝ)^4233 ≤ (22116954357/50000000000000 : ℝ)^3209 := by
    have hnat : (28653433 : ℕ)^4233*50000000000000^3209 ≤ 22116954357^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28653433 10000000000 22116954357 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5910804413/10000000000 : ℝ)^4233 ≤ (49977950090367/100000000000000 : ℝ)^3209 := by
    have hnat : (5910804413 : ℕ)^4233*100000000000000^3209 ≤ 49977950090367^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5910804413 10000000000 49977950090367 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (591079239/1000000000 : ℝ)^4233 ≤ (24988907996059/50000000000000 : ℝ)^3209 := by
    have hnat : (591079239 : ℕ)^4233*50000000000000^3209 ≤ 24988907996059^3209*1000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      591079239 1000000000 24988907996059 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-28653433/10000000000 : ℝ), (5910804413/10000000000 : ℝ), (591079239/1000000000 : ℝ)] ![(22116954357/50000000000000 : ℝ), (49977950090367/100000000000000 : ℝ), (24988907996059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-28653433/10000000000 : ℝ)|^4233 ≤ (22116954357/50000000000000 : ℝ)^3209
        have hw : |(-28653433/10000000000 : ℝ)|=(28653433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5910804413/10000000000 : ℝ)|^4233 ≤ (49977950090367/100000000000000 : ℝ)^3209
        have hw : |(5910804413/10000000000 : ℝ)|=(5910804413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(591079239/1000000000 : ℝ)|^4233 ≤ (24988907996059/50000000000000 : ℝ)^3209
        have hw : |(591079239/1000000000 : ℝ)|=(591079239/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s5_9 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (138540217/1000000000 : ℝ)*x 0 + (5578945309/10000000000 : ℝ)*x 1 + (2789773177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (138540217/1000000000 : ℝ)^4233 ≤ (7373107310697/100000000000000 : ℝ)^3209 := by
    have hnat : (138540217 : ℕ)^4233*100000000000000^3209 ≤ 7373107310697^3209*1000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138540217 1000000000 7373107310697 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5578945309/10000000000 : ℝ)^4233 ≤ (1447192363947/3125000000000 : ℝ)^3209 := by
    have hnat : (5578945309 : ℕ)^4233*3125000000000^3209 ≤ 1447192363947^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5578945309 10000000000 1447192363947 3125000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2789773177/5000000000 : ℝ)^4233 ≤ (46316737028949/100000000000000 : ℝ)^3209 := by
    have hnat : (2789773177 : ℕ)^4233*100000000000000^3209 ≤ 46316737028949^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2789773177 5000000000 46316737028949 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(138540217/1000000000 : ℝ), (5578945309/10000000000 : ℝ), (2789773177/5000000000 : ℝ)] ![(7373107310697/100000000000000 : ℝ), (1447192363947/3125000000000 : ℝ), (46316737028949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(138540217/1000000000 : ℝ)|^4233 ≤ (7373107310697/100000000000000 : ℝ)^3209
        have hw : |(138540217/1000000000 : ℝ)|=(138540217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5578945309/10000000000 : ℝ)|^4233 ≤ (1447192363947/3125000000000 : ℝ)^3209
        have hw : |(5578945309/10000000000 : ℝ)|=(5578945309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2789773177/5000000000 : ℝ)|^4233 ≤ (46316737028949/100000000000000 : ℝ)^3209
        have hw : |(2789773177/5000000000 : ℝ)|=(2789773177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1272_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (89/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11401/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5747/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14143/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (89/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11401/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (89/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11401/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (89/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11401/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (89/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11401/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (89/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11401/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (89/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11401/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11401/100000 : ℝ) ^ (8465/2048 : ℝ) ≤ (12649155763918011/100000000000000000000 : ℝ) := by
    have hpowers : (11401/100000 : ℝ)^8465 ≤ (12649155763918011/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11401 : ℕ)^8465*100000000000000000000^2048 ≤ 12649155763918011^2048*100000^8465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11401 100000 12649155763918011 100000000000000000000 8465 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11401/100000 : ℝ)) (X := (12649155763918011/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (89/625 : ℝ) ^ (8465/2048 : ℝ) ≤ (15855216689102801/50000000000000000000 : ℝ) := by
    have hpowers : (89/625 : ℝ)^8465 ≤ (15855216689102801/50000000000000000000 : ℝ)^2048 := by
      have hnat : (89 : ℕ)^8465*50000000000000000000^2048 ≤ 15855216689102801^2048*625^8465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89 625 15855216689102801 50000000000000000000 8465 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (89/625 : ℝ)) (X := (15855216689102801/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50012649155763918011/50000000000000000000 : ℝ) ≤ (1250076500257931/1250000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (50012649155763918011/50000000000000000000 : ℝ)^2048 ≤ (1250076500257931/1250000000000000 : ℝ)^8465 := by
      have hnat : (50012649155763918011 : ℕ)^2048*1250000000000000^8465 ≤ 1250076500257931^8465*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012649155763918011 50000000000000000000 1250076500257931 1250000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250076500257931/1250000000000000 : ℝ)) (X := (50012649155763918011/50000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044359589142123613/100000000000000000000 : ℝ) ≤ (156266766311203/156250000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (100044359589142123613/100000000000000000000 : ℝ)^2048 ≤ (156266766311203/156250000000000 : ℝ)^8465 := by
      have hnat : (100044359589142123613 : ℕ)^2048*156250000000000^8465 ≤ 156266766311203^8465*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044359589142123613 100000000000000000000 156266766311203 156250000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156266766311203/156250000000000 : ℝ)) (X := (100044359589142123613/100000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015855216689102801/25000000000000000000 : ℝ) ≤ (1250191760721317/1250000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (25015855216689102801/25000000000000000000 : ℝ)^2048 ≤ (1250191760721317/1250000000000000 : ℝ)^8465 := by
      have hnat : (25015855216689102801 : ℕ)^2048*1250000000000000^8465 ≤ 1250191760721317^8465*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015855216689102801 25000000000000000000 1250191760721317 1250000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250191760721317/1250000000000000 : ℝ)) (X := (25015855216689102801/25000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12649155763918011/100000000000000000000 : ℝ) ≤ ((208685476452306019/208750000000000000 : ℝ)+2*(3390013629/2087500000000 : ℝ)*(11401/100000 : ℝ))^(8465/2048 : ℝ) := by
    rw [show (208685476452306019/208750000000000000 : ℝ)+2*(3390013629/2087500000000 : ℝ)*(11401/100000 : ℝ)=(1250076500257931/1250000000000000 : ℝ) by norm_num, show 1+2*(12649155763918011/100000000000000000000 : ℝ)=(50012649155763918011/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15855216689102801/50000000000000000000 : ℝ)+(12649155763918011/100000000000000000000 : ℝ) ≤ ((208685476452306019/208750000000000000 : ℝ)+(3390013629/2087500000000 : ℝ)*((89/625 : ℝ)+(11401/100000 : ℝ)))^(8465/2048 : ℝ) := by
    rw [show (208685476452306019/208750000000000000 : ℝ)+(3390013629/2087500000000 : ℝ)*((89/625 : ℝ)+(11401/100000 : ℝ))=(156266766311203/156250000000000 : ℝ) by norm_num, show 1+(15855216689102801/50000000000000000000 : ℝ)+(12649155763918011/100000000000000000000 : ℝ)=(100044359589142123613/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15855216689102801/50000000000000000000 : ℝ) ≤ ((208685476452306019/208750000000000000 : ℝ)+2*(3390013629/2087500000000 : ℝ)*(89/625 : ℝ))^(8465/2048 : ℝ) := by
    rw [show (208685476452306019/208750000000000000 : ℝ)+2*(3390013629/2087500000000 : ℝ)*(89/625 : ℝ)=(1250191760721317/1250000000000000 : ℝ) by norm_num, show 1+2*(15855216689102801/50000000000000000000 : ℝ)=(25015855216689102801/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (208685476452306019/208750000000000000 : ℝ)*(X 1 0+X 2 0)+(3390013629/2087500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (11401/100000 : ℝ)) (hi := (89/625 : ℝ)) (c := (208685476452306019/208750000000000000 : ℝ)) (alpha := (3390013629/2087500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (208685476452306019/208750000000000000 : ℝ)*(X 0 1+X 2 1)+(3390013629/2087500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (11401/100000 : ℝ)) (hi := (89/625 : ℝ)) (c := (208685476452306019/208750000000000000 : ℝ)) (alpha := (3390013629/2087500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (208685476452306019/208750000000000000 : ℝ)*(X 0 2+X 1 2)+(3390013629/2087500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (11401/100000 : ℝ)) (hi := (89/625 : ℝ)) (c := (208685476452306019/208750000000000000 : ℝ)) (alpha := (3390013629/2087500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2105682397/10000000000 : ℝ)*X 0 0+(1347919251/2500000000 : ℝ)*X 0 1+(5266615427/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((13361021/25000000 : ℝ)*X 1 0+(-2169097529/10000000000 : ℝ)*X 1 1+(526661569/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344407463/10000000000 : ℝ)*X 2 0+(5266616661/10000000000 : ℝ)*X 2 1+(-216909749/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4346486747/10000000000 : ℝ)*X 0 0+(168827541/400000000 : ℝ)*X 0 1+(2237950617/5000000000 : ℝ)*X 0 2+(4346486747/10000000000 : ℝ)*X 1 0+(168827541/400000000 : ℝ)*X 1 1+(2237950617/5000000000 : ℝ)*X 1 2+(4346486747/10000000000 : ℝ)*X 2 0+(168827541/400000000 : ℝ)*X 2 1+(2237950617/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2105686543/10000000000 : ℝ)*X 0 0+(2633468677/5000000000 : ℝ)*X 0 1+(5391354401/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062486411/2000000000 : ℝ)*X 1 0+(-2044359883/10000000000 : ℝ)*X 1 1+(5391354391/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656216033/5000000000 : ℝ)*X 2 0+(2695677193/5000000000 : ℝ)*X 2 1+(-16354879/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4346496531/10000000000 : ℝ)*X 0 0+(4475246283/10000000000 : ℝ)*X 0 1+(2110672977/5000000000 : ℝ)*X 0 2+(4346496531/10000000000 : ℝ)*X 1 0+(4475246283/10000000000 : ℝ)*X 1 1+(2110672977/5000000000 : ℝ)*X 1 2+(4346496531/10000000000 : ℝ)*X 2 0+(4475246283/10000000000 : ℝ)*X 2 1+(2110672977/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-28653433/10000000000 : ℝ)*X 0 0+(5910804413/10000000000 : ℝ)*X 0 1+(591079239/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s5_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((138540217/1000000000 : ℝ)*X 0 0+(5578945309/10000000000 : ℝ)*X 0 1+(2789773177/5000000000 : ℝ)*X 0 2+(138540217/1000000000 : ℝ)*X 1 0+(5578945309/10000000000 : ℝ)*X 1 1+(2789773177/5000000000 : ℝ)*X 1 2+(138540217/1000000000 : ℝ)*X 2 0+(5578945309/10000000000 : ℝ)*X 2 1+(2789773177/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s5_9 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7434284954430446974839987/2609375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (408964991/100000000000000 : ℝ)*(lower2) + (156127961/50000000000000 : ℝ)*(lower3) + (1042047691/100000000000000 : ℝ)*(lower4) + (101011959/20000000000000 : ℝ)*(lower5) + (1489310083420933/25000000000000 : ℝ)*(major0) + (1489310083420933/25000000000000 : ℝ)*(major1) + (1489310083420933/25000000000000 : ℝ)*(major2) + (3998066053097991/50000000000000 : ℝ)*(sp0) + (1999033775458463/25000000000000 : ℝ)*(sp1) + (7996171428237889/100000000000000 : ℝ)*(sp2) + (1959154572080329/50000000000000 : ℝ)*(sp3) + (29981428207/100000000000000 : ℝ)*(sp4) + (36326404037/100000000000000 : ℝ)*(sp5) + (9340613701/100000000000000 : ℝ)*(sp8) + (1959154572080329/50000000000000 : ℝ)*(f.failure) + (7996171428237889/100000000000000 : ℝ)*(f.sum) + (7489623470597/417500000000000000000000000 : ℝ)*base65 + (123040495627273023/5218750000000000000000000000000 : ℝ)*base68 + (40143973684710523/5218750000000000000000000000000 : ℝ)*base70 + (2161763379273023/5218750000000000000000000000000 : ℝ)*base72 + (702430858139/835000000000000000000000000 : ℝ)*base73 + (2262150339914477/5218750000000000000000000000000 : ℝ)*base75 + (1314252845648023/5218750000000000000000000000000 : ℝ)*base78 + (51520991657585523/5218750000000000000000000000000 : ℝ)*base80 + (291902944923/417500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (2880671/1250000000000000000000 : ℝ)*base89 + (2880671/1250000000000000000000 : ℝ)*base91 + (2880671/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (74756200061156892748689477/10437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (104972373/50000000000000 : ℝ)*(lower2) + (70834469/50000000000000 : ℝ)*(lower3) + (201103497/100000000000000 : ℝ)*(lower4) + (13780971/10000000000000 : ℝ)*(lower5) + (5988021026221561/100000000000000 : ℝ)*(major0) + (5988021026221561/100000000000000 : ℝ)*(major1) + (5988021026221561/100000000000000 : ℝ)*(major2) + (69858203/20000000000000 : ℝ)*(sp3) + (200937110894983/2500000000000 : ℝ)*(sp4) + (200937175210383/2500000000000 : ℝ)*(sp5) + (200937175210383/2500000000000 : ℝ)*(sp6) + (15754215351531/400000000000 : ℝ)*(sp7) + (321577/12500000000 : ℝ)*(sp8) + (618111663/100000000000000 : ℝ)*(sp9) + (984638701321357/25000000000000 : ℝ)*(f.failure) + (200937175210383/2500000000000 : ℝ)*(f.sum) + (3995997820777/835000000000000000000000000 : ℝ)*base65 + (156728183948224341/20875000000000000000000000000000 : ℝ)*base68 + (588661437186775659/20875000000000000000000000000000 : ℝ)*base69 + (2731720858489599341/20875000000000000000000000000000 : ℝ)*base72 + (469330317721/104375000000000000000000000 : ℝ)*base74 + (4326813763224341/20875000000000000000000000000000 : ℝ)*base76 + (42721773655400659/20875000000000000000000000000000 : ℝ)*base77 + (58227121708224341/20875000000000000000000000000000 : ℝ)*base80 + (337394987429/104375000000000000000000000 : ℝ)*base81 + (641643/625000000000000000000 : ℝ)*base89 + (641643/625000000000000000000 : ℝ)*base91 + (641643/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1272_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (89/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11401/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5747/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14143/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1272_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1272_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1009/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9623/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5747/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14143/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1272_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1272_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1272_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1009/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9623/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5747/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14143/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1272_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
