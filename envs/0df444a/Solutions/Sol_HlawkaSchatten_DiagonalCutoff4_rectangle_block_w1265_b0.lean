-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1265_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:56:49.610993+00:00
-- url     : https://prove2.me/submissions/cf68e666-9d60-4b97-a8dc-1a79329903fc

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
theorem support_rectangle_w1265_s0_0 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1853483923/10000000000 : ℝ)*x 0 + (6026336507/10000000000 : ℝ)*x 1 + (2397914309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1853483923/10000000000 : ℝ)^4229 ≤ (2163419186979/20000000000000 : ℝ)^3205 := by
    have hnat : (1853483923 : ℕ)^4229*20000000000000^3205 ≤ 2163419186979^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1853483923 10000000000 2163419186979 20000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6026336507/10000000000 : ℝ)^4229 ≤ (2050407836561/4000000000000 : ℝ)^3205 := by
    have hnat : (6026336507 : ℕ)^4229*4000000000000^3205 ≤ 2050407836561^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6026336507 10000000000 2050407836561 4000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2397914309/5000000000 : ℝ)^4229 ≤ (9480677036527/25000000000000 : ℝ)^3205 := by
    have hnat : (2397914309 : ℕ)^4229*25000000000000^3205 ≤ 9480677036527^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397914309 5000000000 9480677036527 25000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1853483923/10000000000 : ℝ), (6026336507/10000000000 : ℝ), (2397914309/5000000000 : ℝ)] ![(2163419186979/20000000000000 : ℝ), (2050407836561/4000000000000 : ℝ), (9480677036527/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1853483923/10000000000 : ℝ)|^4229 ≤ (2163419186979/20000000000000 : ℝ)^3205
        have hw : |(-1853483923/10000000000 : ℝ)|=(1853483923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6026336507/10000000000 : ℝ)|^4229 ≤ (2050407836561/4000000000000 : ℝ)^3205
        have hw : |(6026336507/10000000000 : ℝ)|=(6026336507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2397914309/5000000000 : ℝ)|^4229 ≤ (9480677036527/25000000000000 : ℝ)^3205
        have hw : |(2397914309/5000000000 : ℝ)|=(2397914309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s0_1 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5509863737/10000000000 : ℝ)*x 0 + (-2556322361/10000000000 : ℝ)*x 1 + (299739287/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5509863737/10000000000 : ℝ)^4229 ≤ (9108883688939/20000000000000 : ℝ)^3205 := by
    have hnat : (5509863737 : ℕ)^4229*20000000000000^3205 ≤ 9108883688939^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509863737 10000000000 9108883688939 20000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2556322361/10000000000 : ℝ)^4229 ≤ (2066609208213/12500000000000 : ℝ)^3205 := by
    have hnat : (2556322361 : ℕ)^4229*12500000000000^3205 ≤ 2066609208213^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2556322361 10000000000 2066609208213 12500000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (299739287/625000000 : ℝ)^4229 ≤ (9480676968707/25000000000000 : ℝ)^3205 := by
    have hnat : (299739287 : ℕ)^4229*25000000000000^3205 ≤ 9480676968707^3205*625000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299739287 625000000 9480676968707 25000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5509863737/10000000000 : ℝ), (-2556322361/10000000000 : ℝ), (299739287/625000000 : ℝ)] ![(9108883688939/20000000000000 : ℝ), (2066609208213/12500000000000 : ℝ), (9480676968707/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5509863737/10000000000 : ℝ)|^4229 ≤ (9108883688939/20000000000000 : ℝ)^3205
        have hw : |(5509863737/10000000000 : ℝ)|=(5509863737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2556322361/10000000000 : ℝ)|^4229 ≤ (2066609208213/12500000000000 : ℝ)^3205
        have hw : |(-2556322361/10000000000 : ℝ)|=(2556322361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(299739287/625000000 : ℝ)|^4229 ≤ (9480676968707/25000000000000 : ℝ)^3205
        have hw : |(299739287/625000000 : ℝ)|=(299739287/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s0_2 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5509863763/10000000000 : ℝ)*x 0 + (479582859/1000000000 : ℝ)*x 1 + (-2556322331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5509863763/10000000000 : ℝ)^4229 ≤ (11386104682069/25000000000000 : ℝ)^3205 := by
    have hnat : (5509863763 : ℕ)^4229*25000000000000^3205 ≤ 11386104682069^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509863763 10000000000 11386104682069 25000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (479582859/1000000000 : ℝ)^4229 ≤ (948067696349/2500000000000 : ℝ)^3205 := by
    have hnat : (479582859 : ℕ)^4229*2500000000000^3205 ≤ 948067696349^3205*1000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479582859 1000000000 948067696349 2500000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2556322331/10000000000 : ℝ)^4229 ≤ (1653287340969/10000000000000 : ℝ)^3205 := by
    have hnat : (2556322331 : ℕ)^4229*10000000000000^3205 ≤ 1653287340969^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2556322331 10000000000 1653287340969 10000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5509863763/10000000000 : ℝ), (479582859/1000000000 : ℝ), (-2556322331/10000000000 : ℝ)] ![(11386104682069/25000000000000 : ℝ), (948067696349/2500000000000 : ℝ), (1653287340969/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5509863763/10000000000 : ℝ)|^4229 ≤ (11386104682069/25000000000000 : ℝ)^3205
        have hw : |(5509863763/10000000000 : ℝ)|=(5509863763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(479582859/1000000000 : ℝ)|^4229 ≤ (948067696349/2500000000000 : ℝ)^3205
        have hw : |(479582859/1000000000 : ℝ)|=(479582859/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2556322331/10000000000 : ℝ)|^4229 ≤ (1653287340969/10000000000000 : ℝ)^3205
        have hw : |(-2556322331/10000000000 : ℝ)|=(2556322331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s0_3 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4191221031/10000000000 : ℝ)*x 0 + (3116050467/10000000000 : ℝ)*x 1 + (2811656329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4191221031/10000000000 : ℝ)^4229 ≤ (15872600473701/50000000000000 : ℝ)^3205 := by
    have hnat : (4191221031 : ℕ)^4229*50000000000000^3205 ≤ 15872600473701^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4191221031 10000000000 15872600473701 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3116050467/10000000000 : ℝ)^4229 ≤ (21468945823733/100000000000000 : ℝ)^3205 := by
    have hnat : (3116050467 : ℕ)^4229*100000000000000^3205 ≤ 21468945823733^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3116050467 10000000000 21468945823733 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2811656329/5000000000 : ℝ)^4229 ≤ (4678585321221/10000000000000 : ℝ)^3205 := by
    have hnat : (2811656329 : ℕ)^4229*10000000000000^3205 ≤ 4678585321221^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2811656329 5000000000 4678585321221 10000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4191221031/10000000000 : ℝ), (3116050467/10000000000 : ℝ), (2811656329/5000000000 : ℝ)] ![(15872600473701/50000000000000 : ℝ), (21468945823733/100000000000000 : ℝ), (4678585321221/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4191221031/10000000000 : ℝ)|^4229 ≤ (15872600473701/50000000000000 : ℝ)^3205
        have hw : |(4191221031/10000000000 : ℝ)|=(4191221031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3116050467/10000000000 : ℝ)|^4229 ≤ (21468945823733/100000000000000 : ℝ)^3205
        have hw : |(3116050467/10000000000 : ℝ)|=(3116050467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2811656329/5000000000 : ℝ)|^4229 ≤ (4678585321221/10000000000000 : ℝ)^3205
        have hw : |(2811656329/5000000000 : ℝ)|=(2811656329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s0_4 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-371655269/2000000000 : ℝ)*x 0 + (4827501459/10000000000 : ℝ)*x 1 + (5993543517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (371655269/2000000000 : ℝ)^4229 ≤ (5427008142389/50000000000000 : ℝ)^3205 := by
    have hnat : (371655269 : ℕ)^4229*50000000000000^3205 ≤ 5427008142389^3205*2000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371655269 2000000000 5427008142389 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4827501459/10000000000 : ℝ)^4229 ≤ (1195422703917/3125000000000 : ℝ)^3205 := by
    have hnat : (4827501459 : ℕ)^4229*3125000000000^3205 ≤ 1195422703917^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4827501459 10000000000 1195422703917 3125000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5993543517/10000000000 : ℝ)^4229 ≤ (5089245717117/10000000000000 : ℝ)^3205 := by
    have hnat : (5993543517 : ℕ)^4229*10000000000000^3205 ≤ 5089245717117^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5993543517 10000000000 5089245717117 10000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-371655269/2000000000 : ℝ), (4827501459/10000000000 : ℝ), (5993543517/10000000000 : ℝ)] ![(5427008142389/50000000000000 : ℝ), (1195422703917/3125000000000 : ℝ), (5089245717117/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-371655269/2000000000 : ℝ)|^4229 ≤ (5427008142389/50000000000000 : ℝ)^3205
        have hw : |(-371655269/2000000000 : ℝ)|=(371655269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4827501459/10000000000 : ℝ)|^4229 ≤ (1195422703917/3125000000000 : ℝ)^3205
        have hw : |(4827501459/10000000000 : ℝ)|=(4827501459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5993543517/10000000000 : ℝ)|^4229 ≤ (5089245717117/10000000000000 : ℝ)^3205
        have hw : |(5993543517/10000000000 : ℝ)|=(5993543517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s0_5 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (80858827/156250000 : ℝ)*x 0 + (-1358605007/10000000000 : ℝ)*x 1 + (2996772979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (80858827/156250000 : ℝ)^4229 ≤ (41927658116383/100000000000000 : ℝ)^3205 := by
    have hnat : (80858827 : ℕ)^4229*100000000000000^3205 ≤ 41927658116383^3205*156250000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80858827 156250000 41927658116383 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358605007/10000000000 : ℝ)^4229 ≤ (3589928672639/50000000000000 : ℝ)^3205 := by
    have hnat : (1358605007 : ℕ)^4229*50000000000000^3205 ≤ 3589928672639^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358605007 10000000000 3589928672639 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2996772979/5000000000 : ℝ)^4229 ≤ (50892484520533/100000000000000 : ℝ)^3205 := by
    have hnat : (2996772979 : ℕ)^4229*100000000000000^3205 ≤ 50892484520533^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2996772979 5000000000 50892484520533 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(80858827/156250000 : ℝ), (-1358605007/10000000000 : ℝ), (2996772979/5000000000 : ℝ)] ![(41927658116383/100000000000000 : ℝ), (3589928672639/50000000000000 : ℝ), (50892484520533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(80858827/156250000 : ℝ)|^4229 ≤ (41927658116383/100000000000000 : ℝ)^3205
        have hw : |(80858827/156250000 : ℝ)|=(80858827/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1358605007/10000000000 : ℝ)|^4229 ≤ (3589928672639/50000000000000 : ℝ)^3205
        have hw : |(-1358605007/10000000000 : ℝ)|=(1358605007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2996772979/5000000000 : ℝ)|^4229 ≤ (50892484520533/100000000000000 : ℝ)^3205
        have hw : |(2996772979/5000000000 : ℝ)|=(2996772979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s0_6 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5174966011/10000000000 : ℝ)*x 0 + (1498385983/2500000000 : ℝ)*x 1 + (-1358606603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174966011/10000000000 : ℝ)^4229 ≤ (41927669694323/100000000000000 : ℝ)^3205 := by
    have hnat : (5174966011 : ℕ)^4229*100000000000000^3205 ≤ 41927669694323^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174966011 10000000000 41927669694323 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1498385983/2500000000 : ℝ)^4229 ≤ (25446230910449/50000000000000 : ℝ)^3205 := by
    have hnat : (1498385983 : ℕ)^4229*50000000000000^3205 ≤ 25446230910449^3205*2500000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1498385983 2500000000 25446230910449 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358606603/10000000000 : ℝ)^4229 ≤ (7179868474511/100000000000000 : ℝ)^3205 := by
    have hnat : (1358606603 : ℕ)^4229*100000000000000^3205 ≤ 7179868474511^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358606603 10000000000 7179868474511 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174966011/10000000000 : ℝ), (1498385983/2500000000 : ℝ), (-1358606603/10000000000 : ℝ)] ![(41927669694323/100000000000000 : ℝ), (25446230910449/50000000000000 : ℝ), (7179868474511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174966011/10000000000 : ℝ)|^4229 ≤ (41927669694323/100000000000000 : ℝ)^3205
        have hw : |(5174966011/10000000000 : ℝ)|=(5174966011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1498385983/2500000000 : ℝ)|^4229 ≤ (25446230910449/50000000000000 : ℝ)^3205
        have hw : |(1498385983/2500000000 : ℝ)|=(1498385983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1358606603/10000000000 : ℝ)|^4229 ≤ (7179868474511/100000000000000 : ℝ)^3205
        have hw : |(-1358606603/10000000000 : ℝ)|=(1358606603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s0_7 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4200988703/10000000000 : ℝ)*x 0 + (2779391291/5000000000 : ℝ)*x 1 + (49732231/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4200988703/10000000000 : ℝ)^4229 ≤ (6368571428841/20000000000000 : ℝ)^3205 := by
    have hnat : (4200988703 : ℕ)^4229*20000000000000^3205 ≤ 6368571428841^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4200988703 10000000000 6368571428841 20000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2779391291/5000000000 : ℝ)^4229 ≤ (4607872985723/10000000000000 : ℝ)^3205 := by
    have hnat : (2779391291 : ℕ)^4229*10000000000000^3205 ≤ 4607872985723^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2779391291 5000000000 4607872985723 10000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49732231/156250000 : ℝ)^4229 ≤ (22078412979733/100000000000000 : ℝ)^3205 := by
    have hnat : (49732231 : ℕ)^4229*100000000000000^3205 ≤ 22078412979733^3205*156250000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49732231 156250000 22078412979733 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4200988703/10000000000 : ℝ), (2779391291/5000000000 : ℝ), (49732231/156250000 : ℝ)] ![(6368571428841/20000000000000 : ℝ), (4607872985723/10000000000000 : ℝ), (22078412979733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4200988703/10000000000 : ℝ)|^4229 ≤ (6368571428841/20000000000000 : ℝ)^3205
        have hw : |(4200988703/10000000000 : ℝ)|=(4200988703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2779391291/5000000000 : ℝ)|^4229 ≤ (4607872985723/10000000000000 : ℝ)^3205
        have hw : |(2779391291/5000000000 : ℝ)|=(2779391291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(49732231/156250000 : ℝ)|^4229 ≤ (22078412979733/100000000000000 : ℝ)^3205
        have hw : |(49732231/156250000 : ℝ)|=(49732231/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1265_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37969791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (909/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (547/2000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8457/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8457 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8457*1^2048 ≤ 0^2048*1^8457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8457 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8457/2048 : ℝ) ≤ (2273781373195432969/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8457 ≤ (2273781373195432969/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8457*100000000000000000000^2048 ≤ 2273781373195432969^2048*5^8457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2273781373195432969 100000000000000000000 8457 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2273781373195432969/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8457/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8457 := by
      have hnat : (1 : ℕ)^2048*1^8457 ≤ 1^8457*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102273781373195432969/100000000000000000000 : ℝ) ≤ (10054595123442933/10000000000000000 : ℝ) ^ (8457/2048 : ℝ) := by
    have hpowers : (102273781373195432969/100000000000000000000 : ℝ)^2048 ≤ (10054595123442933/10000000000000000 : ℝ)^8457 := by
      have hnat : (102273781373195432969 : ℕ)^2048*10000000000000000^8457 ≤ 10054595123442933^8457*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102273781373195432969 100000000000000000000 10054595123442933 10000000000000000 2048 8457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10054595123442933/10000000000000000 : ℝ)) (X := (102273781373195432969/100000000000000000000 : ℝ)) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52273781373195432969/50000000000000000000 : ℝ) ≤ (5054595123442933/5000000000000000 : ℝ) ^ (8457/2048 : ℝ) := by
    have hpowers : (52273781373195432969/50000000000000000000 : ℝ)^2048 ≤ (5054595123442933/5000000000000000 : ℝ)^8457 := by
      have hnat : (52273781373195432969 : ℕ)^2048*5000000000000000^8457 ≤ 5054595123442933^8457*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52273781373195432969 50000000000000000000 5054595123442933 5000000000000000 2048 8457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5054595123442933/5000000000000000 : ℝ)) (X := (52273781373195432969/50000000000000000000 : ℝ)) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(54595123442933/4000000000000000 : ℝ)*(0 : ℝ))^(8457/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(54595123442933/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2273781373195432969/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(54595123442933/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8457/2048 : ℝ) := by
    rw [show (1 : ℝ)+(54595123442933/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10054595123442933/10000000000000000 : ℝ) by norm_num, show 1+(2273781373195432969/100000000000000000000 : ℝ)+(0 : ℝ)=(102273781373195432969/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2273781373195432969/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(54595123442933/4000000000000000 : ℝ)*(2/5 : ℝ))^(8457/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(54595123442933/4000000000000000 : ℝ)*(2/5 : ℝ)=(5054595123442933/5000000000000000 : ℝ) by norm_num, show 1+2*(2273781373195432969/100000000000000000000 : ℝ)=(52273781373195432969/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(54595123442933/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8457/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54595123442933/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(54595123442933/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8457/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54595123442933/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(54595123442933/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8457/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54595123442933/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1853483923/10000000000 : ℝ)*X 0 0+(6026336507/10000000000 : ℝ)*X 0 1+(2397914309/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5509863737/10000000000 : ℝ)*X 1 0+(-2556322361/10000000000 : ℝ)*X 1 1+(299739287/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5509863763/10000000000 : ℝ)*X 2 0+(479582859/1000000000 : ℝ)*X 2 1+(-2556322331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4191221031/10000000000 : ℝ)*X 0 0+(3116050467/10000000000 : ℝ)*X 0 1+(2811656329/5000000000 : ℝ)*X 0 2+(4191221031/10000000000 : ℝ)*X 1 0+(3116050467/10000000000 : ℝ)*X 1 1+(2811656329/5000000000 : ℝ)*X 1 2+(4191221031/10000000000 : ℝ)*X 2 0+(3116050467/10000000000 : ℝ)*X 2 1+(2811656329/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-371655269/2000000000 : ℝ)*X 0 0+(4827501459/10000000000 : ℝ)*X 0 1+(5993543517/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((80858827/156250000 : ℝ)*X 1 0+(-1358605007/10000000000 : ℝ)*X 1 1+(2996772979/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5174966011/10000000000 : ℝ)*X 2 0+(1498385983/2500000000 : ℝ)*X 2 1+(-1358606603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4200988703/10000000000 : ℝ)*X 0 0+(2779391291/5000000000 : ℝ)*X 0 1+(49732231/156250000 : ℝ)*X 0 2+(4200988703/10000000000 : ℝ)*X 1 0+(2779391291/5000000000 : ℝ)*X 1 1+(49732231/156250000 : ℝ)*X 1 2+(4200988703/10000000000 : ℝ)*X 2 0+(2779391291/5000000000 : ℝ)*X 2 1+(49732231/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (599562637857450316856847/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67453691/100000000000000 : ℝ)*(base1) + (1458025799/100000000000000 : ℝ)*(base19) + (730930341/50000000000000 : ℝ)*(base23) + (82882187/50000000000000 : ℝ)*(upper3) + (87258489/50000000000000 : ℝ)*(upper5) + (605763807210149/100000000000000 : ℝ)*(major0) + (605763807210149/100000000000000 : ℝ)*(major1) + (605763807210149/100000000000000 : ℝ)*(major2) + (203169231498927/25000000000000 : ℝ)*(sp0) + (406340032009337/50000000000000 : ℝ)*(sp1) + (812680060183791/100000000000000 : ℝ)*(sp2) + (19942178582103/5000000000000 : ℝ)*(sp3) + (4663502457/100000000000000 : ℝ)*(sp4) + (2253425851/100000000000000 : ℝ)*(sp7) + (398845892521603/100000000000000 : ℝ)*(f.failure) + (406340761022237/50000000000000 : ℝ)*(f.sum) + (364353747127017/200000000000000000000000000000 : ℝ)*base65 + (2731735931527017/400000000000000000000000000000 : ℝ)*base67 + (1659075349127017/400000000000000000000000000000 : ℝ)*base69 + (2936422399527017/400000000000000000000000000000 : ℝ)*base71 + (848042342327017/200000000000000000000000000000 : ℝ)*base73 + (3677621671127017/400000000000000000000000000000 : ℝ)*base75 + (3421446081527017/400000000000000000000000000000 : ℝ)*base77 + (3584100743127017/400000000000000000000000000000 : ℝ)*base79 + (232504771327017/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3894973/2500000000000000000000 : ℝ)*base89 + (3894973/2500000000000000000000 : ℝ)*base91 + (3894973/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (58393815632213837802123/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (55984383/25000000000000 : ℝ)*(base1) + (113454643/20000000000000 : ℝ)*(base19) + (700346761/100000000000000 : ℝ)*(base23) + (28112573/25000000000000 : ℝ)*(upper3) + (319623141935477/50000000000000 : ℝ)*(major0) + (319623141935477/50000000000000 : ℝ)*(major1) + (319623141935477/50000000000000 : ℝ)*(major2) + (1585913469/100000000000000 : ℝ)*(sp1) + (217223189/25000000000000 : ℝ)*(sp2) + (572448013/100000000000000 : ℝ)*(sp3) + (428800665547063/50000000000000 : ℝ)*(sp4) + (857598953969911/100000000000000 : ℝ)*(sp5) + (214399884479269/25000000000000 : ℝ)*(sp6) + (6576415107449/1562500000000 : ℝ)*(sp7) + (10522284081557/2500000000000 : ℝ)*(f.failure) + (428800553578297/50000000000000 : ℝ)*(f.sum) + (323496956465959/100000000000000000000000000000 : ℝ)*base66 + (896197273765959/200000000000000000000000000000 : ℝ)*base68 + (1154738966365959/200000000000000000000000000000 : ℝ)*base70 + (1302900396765959/200000000000000000000000000000 : ℝ)*base72 + (281190396065959/100000000000000000000000000000 : ℝ)*base74 + (2713077815165959/200000000000000000000000000000 : ℝ)*base76 + (422670317365959/200000000000000000000000000000 : ℝ)*base78 + (1040533318634041/200000000000000000000000000000 : ℝ)*base79 + (533259873765959/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (5413/62500000000000000000 : ℝ)*base90 + (5413/62500000000000000000 : ℝ)*base92 + (5413/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1265_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37969791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (909/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (547/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1265_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1265_s1_0 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2049223957/10000000000 : ℝ)*x 0 + (5669871573/10000000000 : ℝ)*x 1 + (1005399277/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2049223957/10000000000 : ℝ)^4229 ≤ (12349282017221/100000000000000 : ℝ)^3205 := by
    have hnat : (2049223957 : ℕ)^4229*100000000000000^3205 ≤ 12349282017221^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049223957 10000000000 12349282017221 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5669871573/10000000000 : ℝ)^4229 ≤ (47297662074371/100000000000000 : ℝ)^3205 := by
    have hnat : (5669871573 : ℕ)^4229*100000000000000^3205 ≤ 47297662074371^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5669871573 10000000000 47297662074371 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1005399277/2000000000 : ℝ)^4229 ≤ (40353055895491/100000000000000 : ℝ)^3205 := by
    have hnat : (1005399277 : ℕ)^4229*100000000000000^3205 ≤ 40353055895491^3205*2000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005399277 2000000000 40353055895491 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2049223957/10000000000 : ℝ), (5669871573/10000000000 : ℝ), (1005399277/2000000000 : ℝ)] ![(12349282017221/100000000000000 : ℝ), (47297662074371/100000000000000 : ℝ), (40353055895491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2049223957/10000000000 : ℝ)|^4229 ≤ (12349282017221/100000000000000 : ℝ)^3205
        have hw : |(-2049223957/10000000000 : ℝ)|=(2049223957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5669871573/10000000000 : ℝ)|^4229 ≤ (47297662074371/100000000000000 : ℝ)^3205
        have hw : |(5669871573/10000000000 : ℝ)|=(5669871573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1005399277/2000000000 : ℝ)|^4229 ≤ (40353055895491/100000000000000 : ℝ)^3205
        have hw : |(1005399277/2000000000 : ℝ)|=(1005399277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s1_1 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1082481937/2000000000 : ℝ)*x 0 + (-478812657/2000000000 : ℝ)*x 1 + (502699661/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082481937/2000000000 : ℝ)^4229 ≤ (22242252954471/50000000000000 : ℝ)^3205 := by
    have hnat : (1082481937 : ℕ)^4229*50000000000000^3205 ≤ 22242252954471^3205*2000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082481937 2000000000 22242252954471 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (478812657/2000000000 : ℝ)^4229 ≤ (1895304473951/12500000000000 : ℝ)^3205 := by
    have hnat : (478812657 : ℕ)^4229*12500000000000^3205 ≤ 1895304473951^3205*2000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478812657 2000000000 1895304473951 12500000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (502699661/1000000000 : ℝ)^4229 ≤ (40353058278689/100000000000000 : ℝ)^3205 := by
    have hnat : (502699661 : ℕ)^4229*100000000000000^3205 ≤ 40353058278689^3205*1000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502699661 1000000000 40353058278689 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082481937/2000000000 : ℝ), (-478812657/2000000000 : ℝ), (502699661/1000000000 : ℝ)] ![(22242252954471/50000000000000 : ℝ), (1895304473951/12500000000000 : ℝ), (40353058278689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082481937/2000000000 : ℝ)|^4229 ≤ (22242252954471/50000000000000 : ℝ)^3205
        have hw : |(1082481937/2000000000 : ℝ)|=(1082481937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-478812657/2000000000 : ℝ)|^4229 ≤ (1895304473951/12500000000000 : ℝ)^3205
        have hw : |(-478812657/2000000000 : ℝ)|=(478812657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(502699661/1000000000 : ℝ)|^4229 ≤ (40353058278689/100000000000000 : ℝ)^3205
        have hw : |(502699661/1000000000 : ℝ)|=(502699661/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s1_2 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5412409889/10000000000 : ℝ)*x 0 + (2513498243/5000000000 : ℝ)*x 1 + (-1197031589/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5412409889/10000000000 : ℝ)^4229 ≤ (44484508121313/100000000000000 : ℝ)^3205 := by
    have hnat : (5412409889 : ℕ)^4229*100000000000000^3205 ≤ 44484508121313^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412409889 10000000000 44484508121313 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2513498243/5000000000 : ℝ)^4229 ≤ (20176528482641/50000000000000 : ℝ)^3205 := by
    have hnat : (2513498243 : ℕ)^4229*50000000000000^3205 ≤ 20176528482641^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2513498243 5000000000 20176528482641 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1197031589/5000000000 : ℝ)^4229 ≤ (947652181089/6250000000000 : ℝ)^3205 := by
    have hnat : (1197031589 : ℕ)^4229*6250000000000^3205 ≤ 947652181089^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1197031589 5000000000 947652181089 6250000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5412409889/10000000000 : ℝ), (2513498243/5000000000 : ℝ), (-1197031589/5000000000 : ℝ)] ![(44484508121313/100000000000000 : ℝ), (20176528482641/50000000000000 : ℝ), (947652181089/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5412409889/10000000000 : ℝ)|^4229 ≤ (44484508121313/100000000000000 : ℝ)^3205
        have hw : |(5412409889/10000000000 : ℝ)|=(5412409889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2513498243/5000000000 : ℝ)|^4229 ≤ (20176528482641/50000000000000 : ℝ)^3205
        have hw : |(2513498243/5000000000 : ℝ)|=(2513498243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1197031589/5000000000 : ℝ)|^4229 ≤ (947652181089/6250000000000 : ℝ)^3205
        have hw : |(-1197031589/5000000000 : ℝ)|=(1197031589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s1_3 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (861370799/2000000000 : ℝ)*x 0 + (3699580893/10000000000 : ℝ)*x 1 + (250474659/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (861370799/2000000000 : ℝ)^4229 ≤ (32905919539853/100000000000000 : ℝ)^3205 := by
    have hnat : (861370799 : ℕ)^4229*100000000000000^3205 ≤ 32905919539853^3205*2000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861370799 2000000000 32905919539853 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3699580893/10000000000 : ℝ)^4229 ≤ (26926315090813/100000000000000 : ℝ)^3205 := by
    have hnat : (3699580893 : ℕ)^4229*100000000000000^3205 ≤ 26926315090813^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3699580893 10000000000 26926315090813 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (250474659/500000000 : ℝ)^4229 ≤ (40167765348827/100000000000000 : ℝ)^3205 := by
    have hnat : (250474659 : ℕ)^4229*100000000000000^3205 ≤ 40167765348827^3205*500000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250474659 500000000 40167765348827 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(861370799/2000000000 : ℝ), (3699580893/10000000000 : ℝ), (250474659/500000000 : ℝ)] ![(32905919539853/100000000000000 : ℝ), (26926315090813/100000000000000 : ℝ), (40167765348827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(861370799/2000000000 : ℝ)|^4229 ≤ (32905919539853/100000000000000 : ℝ)^3205
        have hw : |(861370799/2000000000 : ℝ)|=(861370799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3699580893/10000000000 : ℝ)|^4229 ≤ (26926315090813/100000000000000 : ℝ)^3205
        have hw : |(3699580893/10000000000 : ℝ)|=(3699580893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(250474659/500000000 : ℝ)|^4229 ≤ (40167765348827/100000000000000 : ℝ)^3205
        have hw : |(250474659/500000000 : ℝ)|=(250474659/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s1_4 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-512468361/2500000000 : ℝ)*x 0 + (5035365171/10000000000 : ℝ)*x 1 + (5661345047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (512468361/2500000000 : ℝ)^4229 ≤ (3088611706911/25000000000000 : ℝ)^3205 := by
    have hnat : (512468361 : ℕ)^4229*25000000000000^3205 ≤ 3088611706911^3205*2500000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512468361 2500000000 3088611706911 25000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5035365171/10000000000 : ℝ)^4229 ≤ (20220860773593/50000000000000 : ℝ)^3205 := by
    have hnat : (5035365171 : ℕ)^4229*50000000000000^3205 ≤ 20220860773593^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5035365171 10000000000 20220860773593 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5661345047/10000000000 : ℝ)^4229 ≤ (11800957903769/25000000000000 : ℝ)^3205 := by
    have hnat : (5661345047 : ℕ)^4229*25000000000000^3205 ≤ 11800957903769^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5661345047 10000000000 11800957903769 25000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-512468361/2500000000 : ℝ), (5035365171/10000000000 : ℝ), (5661345047/10000000000 : ℝ)] ![(3088611706911/25000000000000 : ℝ), (20220860773593/50000000000000 : ℝ), (11800957903769/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-512468361/2500000000 : ℝ)|^4229 ≤ (3088611706911/25000000000000 : ℝ)^3205
        have hw : |(-512468361/2500000000 : ℝ)|=(512468361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5035365171/10000000000 : ℝ)|^4229 ≤ (20220860773593/50000000000000 : ℝ)^3205
        have hw : |(5035365171/10000000000 : ℝ)|=(5035365171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5661345047/10000000000 : ℝ)|^4229 ≤ (11800957903769/25000000000000 : ℝ)^3205
        have hw : |(5661345047/10000000000 : ℝ)|=(5661345047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s1_5 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2623304003/5000000000 : ℝ)*x 0 + (-1759714449/10000000000 : ℝ)*x 1 + (5661345529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2623304003/5000000000 : ℝ)^4229 ≤ (42695255560087/100000000000000 : ℝ)^3205 := by
    have hnat : (2623304003 : ℕ)^4229*100000000000000^3205 ≤ 42695255560087^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623304003 5000000000 42695255560087 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1759714449/10000000000 : ℝ)^4229 ≤ (10100907507873/100000000000000 : ℝ)^3205 := by
    have hnat : (1759714449 : ℕ)^4229*100000000000000^3205 ≤ 10100907507873^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759714449 10000000000 10100907507873 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5661345529/10000000000 : ℝ)^4229 ≤ (47203836917987/100000000000000 : ℝ)^3205 := by
    have hnat : (5661345529 : ℕ)^4229*100000000000000^3205 ≤ 47203836917987^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5661345529 10000000000 47203836917987 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2623304003/5000000000 : ℝ), (-1759714449/10000000000 : ℝ), (5661345529/10000000000 : ℝ)] ![(42695255560087/100000000000000 : ℝ), (10100907507873/100000000000000 : ℝ), (47203836917987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2623304003/5000000000 : ℝ)|^4229 ≤ (42695255560087/100000000000000 : ℝ)^3205
        have hw : |(2623304003/5000000000 : ℝ)|=(2623304003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1759714449/10000000000 : ℝ)|^4229 ≤ (10100907507873/100000000000000 : ℝ)^3205
        have hw : |(-1759714449/10000000000 : ℝ)|=(1759714449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5661345529/10000000000 : ℝ)|^4229 ≤ (47203836917987/100000000000000 : ℝ)^3205
        have hw : |(5661345529/10000000000 : ℝ)|=(5661345529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s1_6 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2623303961/5000000000 : ℝ)*x 0 + (5661345227/10000000000 : ℝ)*x 1 + (-1759715007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2623303961/5000000000 : ℝ)^4229 ≤ (21347627329061/50000000000000 : ℝ)^3205 := by
    have hnat : (2623303961 : ℕ)^4229*50000000000000^3205 ≤ 21347627329061^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623303961 5000000000 21347627329061 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5661345227/10000000000 : ℝ)^4229 ≤ (5900479199427/12500000000000 : ℝ)^3205 := by
    have hnat : (5661345227 : ℕ)^4229*12500000000000^3205 ≤ 5900479199427^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5661345227 10000000000 5900479199427 12500000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1759715007/10000000000 : ℝ)^4229 ≤ (1010091173419/10000000000000 : ℝ)^3205 := by
    have hnat : (1759715007 : ℕ)^4229*10000000000000^3205 ≤ 1010091173419^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759715007 10000000000 1010091173419 10000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2623303961/5000000000 : ℝ), (5661345227/10000000000 : ℝ), (-1759715007/10000000000 : ℝ)] ![(21347627329061/50000000000000 : ℝ), (5900479199427/12500000000000 : ℝ), (1010091173419/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2623303961/5000000000 : ℝ)|^4229 ≤ (21347627329061/50000000000000 : ℝ)^3205
        have hw : |(2623303961/5000000000 : ℝ)|=(2623303961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5661345227/10000000000 : ℝ)|^4229 ≤ (5900479199427/12500000000000 : ℝ)^3205
        have hw : |(5661345227/10000000000 : ℝ)|=(5661345227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1759715007/10000000000 : ℝ)|^4229 ≤ (1010091173419/10000000000000 : ℝ)^3205
        have hw : |(-1759715007/10000000000 : ℝ)|=(1759715007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s1_7 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (172327081/400000000 : ℝ)*x 0 + (4992441287/10000000000 : ℝ)*x 1 + (3716954623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172327081/400000000 : ℝ)^4229 ≤ (1316770330861/4000000000000 : ℝ)^3205 := by
    have hnat : (172327081 : ℕ)^4229*4000000000000^3205 ≤ 1316770330861^3205*400000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172327081 400000000 1316770330861 4000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4992441287/10000000000 : ℝ)^4229 ≤ (39987451233477/100000000000000 : ℝ)^3205 := by
    have hnat : (4992441287 : ℕ)^4229*100000000000000^3205 ≤ 39987451233477^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4992441287 10000000000 39987451233477 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3716954623/10000000000 : ℝ)^4229 ≤ (27093290477757/100000000000000 : ℝ)^3205 := by
    have hnat : (3716954623 : ℕ)^4229*100000000000000^3205 ≤ 27093290477757^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3716954623 10000000000 27093290477757 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172327081/400000000 : ℝ), (4992441287/10000000000 : ℝ), (3716954623/10000000000 : ℝ)] ![(1316770330861/4000000000000 : ℝ), (39987451233477/100000000000000 : ℝ), (27093290477757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172327081/400000000 : ℝ)|^4229 ≤ (1316770330861/4000000000000 : ℝ)^3205
        have hw : |(172327081/400000000 : ℝ)|=(172327081/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4992441287/10000000000 : ℝ)|^4229 ≤ (39987451233477/100000000000000 : ℝ)^3205
        have hw : |(4992441287/10000000000 : ℝ)|=(4992441287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3716954623/10000000000 : ℝ)|^4229 ≤ (27093290477757/100000000000000 : ℝ)^3205
        have hw : |(3716954623/10000000000 : ℝ)|=(3716954623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1265_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37969791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (547/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (909/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (6311/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9951/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (547/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (909/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (547/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (909/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (547/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (909/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (547/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (909/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (547/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (909/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (547/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (909/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (909/100000 : ℝ) ^ (8457/2048 : ℝ) ≤ (371624949743/100000000000000000000 : ℝ) := by
    have hpowers : (909/100000 : ℝ)^8457 ≤ (371624949743/100000000000000000000 : ℝ)^2048 := by
      have hnat : (909 : ℕ)^8457*100000000000000000000^2048 ≤ 371624949743^2048*100000^8457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        909 100000 371624949743 100000000000000000000 8457 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (909/100000 : ℝ)) (X := (371624949743/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (547/2000 : ℝ) ^ (8457/2048 : ℝ) ≤ (473123674801302219/100000000000000000000 : ℝ) := by
    have hpowers : (547/2000 : ℝ)^8457 ≤ (473123674801302219/100000000000000000000 : ℝ)^2048 := by
      have hnat : (547 : ℕ)^8457*100000000000000000000^2048 ≤ 473123674801302219^2048*2000^8457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        547 2000 473123674801302219 100000000000000000000 8457 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (547/2000 : ℝ)) (X := (473123674801302219/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000371624949743/50000000000000000000 : ℝ) ≤ (2000000003599801/2000000000000000 : ℝ) ^ (8457/2048 : ℝ) := by
    have hpowers : (50000000371624949743/50000000000000000000 : ℝ)^2048 ≤ (2000000003599801/2000000000000000 : ℝ)^8457 := by
      have hnat : (50000000371624949743 : ℕ)^2048*2000000000000000^8457 ≤ 2000000003599801^8457*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000371624949743 50000000000000000000 2000000003599801 2000000000000000 2048 8457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000003599801/2000000000000000 : ℝ)) (X := (50000000371624949743/50000000000000000000 : ℝ)) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50236562023213125981/50000000000000000000 : ℝ) ≤ (2002287396832453/2000000000000000 : ℝ) ^ (8457/2048 : ℝ) := by
    have hpowers : (50236562023213125981/50000000000000000000 : ℝ)^2048 ≤ (2002287396832453/2000000000000000 : ℝ)^8457 := by
      have hnat : (50236562023213125981 : ℕ)^2048*2000000000000000^8457 ≤ 2002287396832453^8457*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50236562023213125981 50000000000000000000 2002287396832453 2000000000000000 2048 8457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002287396832453/2000000000000000 : ℝ)) (X := (50236562023213125981/50000000000000000000 : ℝ)) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50473123674801302219/50000000000000000000 : ℝ) ≤ (400914958013021/400000000000000 : ℝ) ^ (8457/2048 : ℝ) := by
    have hpowers : (50473123674801302219/50000000000000000000 : ℝ)^2048 ≤ (400914958013021/400000000000000 : ℝ)^8457 := by
      have hnat : (50473123674801302219 : ℕ)^2048*400000000000000^8457 ≤ 400914958013021^8457*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50473123674801302219 50000000000000000000 400914958013021 400000000000000 2048 8457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400914958013021/400000000000000 : ℝ)) (X := (50473123674801302219/50000000000000000000 : ℝ)) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(371624949743/100000000000000000000 : ℝ) ≤ ((10575568322857075381/10576400000000000000 : ℝ)+2*(571848308163/132205000000000 : ℝ)*(909/100000 : ℝ))^(8457/2048 : ℝ) := by
    rw [show (10575568322857075381/10576400000000000000 : ℝ)+2*(571848308163/132205000000000 : ℝ)*(909/100000 : ℝ)=(2000000003599801/2000000000000000 : ℝ) by norm_num, show 1+2*(371624949743/100000000000000000000 : ℝ)=(50000000371624949743/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(473123674801302219/100000000000000000000 : ℝ)+(371624949743/100000000000000000000 : ℝ) ≤ ((10575568322857075381/10576400000000000000 : ℝ)+(571848308163/132205000000000 : ℝ)*((547/2000 : ℝ)+(909/100000 : ℝ)))^(8457/2048 : ℝ) := by
    rw [show (10575568322857075381/10576400000000000000 : ℝ)+(571848308163/132205000000000 : ℝ)*((547/2000 : ℝ)+(909/100000 : ℝ))=(2002287396832453/2000000000000000 : ℝ) by norm_num, show 1+(473123674801302219/100000000000000000000 : ℝ)+(371624949743/100000000000000000000 : ℝ)=(50236562023213125981/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(473123674801302219/100000000000000000000 : ℝ) ≤ ((10575568322857075381/10576400000000000000 : ℝ)+2*(571848308163/132205000000000 : ℝ)*(547/2000 : ℝ))^(8457/2048 : ℝ) := by
    rw [show (10575568322857075381/10576400000000000000 : ℝ)+2*(571848308163/132205000000000 : ℝ)*(547/2000 : ℝ)=(400914958013021/400000000000000 : ℝ) by norm_num, show 1+2*(473123674801302219/100000000000000000000 : ℝ)=(50473123674801302219/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10575568322857075381/10576400000000000000 : ℝ)*(X 1 0+X 2 0)+(571848308163/132205000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8457/2048 : ℝ)) (lo := (909/100000 : ℝ)) (hi := (547/2000 : ℝ)) (c := (10575568322857075381/10576400000000000000 : ℝ)) (alpha := (571848308163/132205000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10575568322857075381/10576400000000000000 : ℝ)*(X 0 1+X 2 1)+(571848308163/132205000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8457/2048 : ℝ)) (lo := (909/100000 : ℝ)) (hi := (547/2000 : ℝ)) (c := (10575568322857075381/10576400000000000000 : ℝ)) (alpha := (571848308163/132205000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10575568322857075381/10576400000000000000 : ℝ)*(X 0 2+X 1 2)+(571848308163/132205000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8457/2048 : ℝ)) (lo := (909/100000 : ℝ)) (hi := (547/2000 : ℝ)) (c := (10575568322857075381/10576400000000000000 : ℝ)) (alpha := (571848308163/132205000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2049223957/10000000000 : ℝ)*X 0 0+(5669871573/10000000000 : ℝ)*X 0 1+(1005399277/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1082481937/2000000000 : ℝ)*X 1 0+(-478812657/2000000000 : ℝ)*X 1 1+(502699661/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5412409889/10000000000 : ℝ)*X 2 0+(2513498243/5000000000 : ℝ)*X 2 1+(-1197031589/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((861370799/2000000000 : ℝ)*X 0 0+(3699580893/10000000000 : ℝ)*X 0 1+(250474659/500000000 : ℝ)*X 0 2+(861370799/2000000000 : ℝ)*X 1 0+(3699580893/10000000000 : ℝ)*X 1 1+(250474659/500000000 : ℝ)*X 1 2+(861370799/2000000000 : ℝ)*X 2 0+(3699580893/10000000000 : ℝ)*X 2 1+(250474659/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-512468361/2500000000 : ℝ)*X 0 0+(5035365171/10000000000 : ℝ)*X 0 1+(5661345047/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2623304003/5000000000 : ℝ)*X 1 0+(-1759714449/10000000000 : ℝ)*X 1 1+(5661345529/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2623303961/5000000000 : ℝ)*X 2 0+(5661345227/10000000000 : ℝ)*X 2 1+(-1759715007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((172327081/400000000 : ℝ)*X 0 0+(4992441287/10000000000 : ℝ)*X 0 1+(3716954623/10000000000 : ℝ)*X 0 2+(172327081/400000000 : ℝ)*X 1 0+(4992441287/10000000000 : ℝ)*X 1 1+(3716954623/10000000000 : ℝ)*X 1 2+(172327081/400000000 : ℝ)*X 2 0+(4992441287/10000000000 : ℝ)*X 2 1+(3716954623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (575846466790145275074136761/264410000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (514647/6250000000000 : ℝ)*(base1) + (271367129/50000000000000 : ℝ)*(base19) + (601363551/100000000000000 : ℝ)*(base23) + (765357/1562500000000 : ℝ)*(upper3) + (52397969/50000000000000 : ℝ)*(upper5) + (1159466408556327/100000000000000 : ℝ)*(major0) + (1159466408556327/100000000000000 : ℝ)*(major1) + (1159466408556327/100000000000000 : ℝ)*(major2) + (777757521045087/50000000000000 : ℝ)*(sp0) + (1555518460214107/100000000000000 : ℝ)*(sp1) + (777759200792407/50000000000000 : ℝ)*(sp2) + (763411885251891/100000000000000 : ℝ)*(sp3) + (62017071/1562500000000 : ℝ)*(sp4) + (924041447/50000000000000 : ℝ)*(sp7) + (381706870784569/50000000000000 : ℝ)*(f.failure) + (311103800589673/20000000000000 : ℝ)*(f.sum) + (81152929328323/26441000000000000000000000000 : ℝ)*base65 + (1088593965770314413/1057640000000000000000000000000000 : ℝ)*base68 + (11347491424548434413/1057640000000000000000000000000000 : ℝ)*base70 + (4158943216784034413/1057640000000000000000000000000000 : ℝ)*base72 + (73493699711609/13220500000000000000000000000 : ℝ)*base73 + (4115483120228114413/1057640000000000000000000000000000 : ℝ)*base76 + (4862696186375674413/1057640000000000000000000000000000 : ℝ)*base78 + (5034766301061765587/1057640000000000000000000000000000 : ℝ)*base79 + (27163772486123/13220500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (3455079/1250000000000000000000 : ℝ)*base89 + (3455079/1250000000000000000000 : ℝ)*base91 + (3455079/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3389094066535040524678993851/528820000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (968701/10000000000000 : ℝ)*(base1) + (1206723877/100000000000000 : ℝ)*(base19) + (1145177269/100000000000000 : ℝ)*(base23) + (89522513/50000000000000 : ℝ)*(upper3) + (137051309/100000000000000 : ℝ)*(upper5) + (1190754805774043/100000000000000 : ℝ)*(major0) + (1190754805774043/100000000000000 : ℝ)*(major1) + (1190754805774043/100000000000000 : ℝ)*(major2) + (204947277/3125000000000 : ℝ)*(sp1) + (1084013467/20000000000000 : ℝ)*(sp2) + (399373704263297/25000000000000 : ℝ)*(sp4) + (1597487042329437/100000000000000 : ℝ)*(sp5) + (798744121060787/50000000000000 : ℝ)*(sp6) + (156802916173741/20000000000000 : ℝ)*(sp7) + (156802918111143/20000000000000 : ℝ)*(f.failure) + (798747403683089/50000000000000 : ℝ)*(f.sum) + (87829458123563/26441000000000000000000000000 : ℝ)*base65 + (503716590784735383/1057640000000000000000000000000000 : ℝ)*base67 + (69730072114784617/1057640000000000000000000000000000 : ℝ)*base70 + (417069852610175383/1057640000000000000000000000000000 : ℝ)*base71 + (70224492741037/13220500000000000000000000000 : ℝ)*base73 + (424115489634935383/1057640000000000000000000000000000 : ℝ)*base75 + (620110734761335383/1057640000000000000000000000000000 : ℝ)*base77 + (64550165989664617/1057640000000000000000000000000000 : ℝ)*base80 + (164252979998989/26441000000000000000000000000 : ℝ)*base81 + (518887/500000000000000000000 : ℝ)*base90 + (518887/500000000000000000000 : ℝ)*base92 + (518887/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1265_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37969791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (547/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (909/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6311/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9951/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1265_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1265_s2_0 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2096123939/10000000000 : ℝ)*x 0 + (5488917997/10000000000 : ℝ)*x 1 + (5178020053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096123939/10000000000 : ℝ)^4229 ≤ (6361787390333/50000000000000 : ℝ)^3205 := by
    have hnat : (2096123939 : ℕ)^4229*50000000000000^3205 ≤ 6361787390333^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096123939 10000000000 6361787390333 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5488917997/10000000000 : ℝ)^4229 ≤ (9063220566357/20000000000000 : ℝ)^3205 := by
    have hnat : (5488917997 : ℕ)^4229*20000000000000^3205 ≤ 9063220566357^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488917997 10000000000 9063220566357 20000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5178020053/10000000000 : ℝ)^4229 ≤ (4196032237319/10000000000000 : ℝ)^3205 := by
    have hnat : (5178020053 : ℕ)^4229*10000000000000^3205 ≤ 4196032237319^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178020053 10000000000 4196032237319 10000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2096123939/10000000000 : ℝ), (5488917997/10000000000 : ℝ), (5178020053/10000000000 : ℝ)] ![(6361787390333/50000000000000 : ℝ), (9063220566357/20000000000000 : ℝ), (4196032237319/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2096123939/10000000000 : ℝ)|^4229 ≤ (6361787390333/50000000000000 : ℝ)^3205
        have hw : |(-2096123939/10000000000 : ℝ)|=(2096123939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5488917997/10000000000 : ℝ)|^4229 ≤ (9063220566357/20000000000000 : ℝ)^3205
        have hw : |(5488917997/10000000000 : ℝ)|=(5488917997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5178020053/10000000000 : ℝ)|^4229 ≤ (4196032237319/10000000000000 : ℝ)^3205
        have hw : |(5178020053/10000000000 : ℝ)|=(5178020053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s2_1 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5368758169/10000000000 : ℝ)*x 0 + (-451407909/2000000000 : ℝ)*x 1 + (517802027/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368758169/10000000000 : ℝ)^4229 ≤ (11002929555599/25000000000000 : ℝ)^3205 := by
    have hnat : (5368758169 : ℕ)^4229*25000000000000^3205 ≤ 11002929555599^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368758169 10000000000 11002929555599 25000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451407909/2000000000 : ℝ)^4229 ≤ (14027957075997/100000000000000 : ℝ)^3205 := by
    have hnat : (451407909 : ℕ)^4229*100000000000000^3205 ≤ 14027957075997^3205*2000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451407909 2000000000 14027957075997 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517802027/1000000000 : ℝ)^4229 ≤ (10490081173373/25000000000000 : ℝ)^3205 := by
    have hnat : (517802027 : ℕ)^4229*25000000000000^3205 ≤ 10490081173373^3205*1000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517802027 1000000000 10490081173373 25000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368758169/10000000000 : ℝ), (-451407909/2000000000 : ℝ), (517802027/1000000000 : ℝ)] ![(11002929555599/25000000000000 : ℝ), (14027957075997/100000000000000 : ℝ), (10490081173373/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368758169/10000000000 : ℝ)|^4229 ≤ (11002929555599/25000000000000 : ℝ)^3205
        have hw : |(5368758169/10000000000 : ℝ)|=(5368758169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-451407909/2000000000 : ℝ)|^4229 ≤ (14027957075997/100000000000000 : ℝ)^3205
        have hw : |(-451407909/2000000000 : ℝ)|=(451407909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(517802027/1000000000 : ℝ)|^4229 ≤ (10490081173373/25000000000000 : ℝ)^3205
        have hw : |(517802027/1000000000 : ℝ)|=(517802027/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s2_2 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1342189527/2500000000 : ℝ)*x 0 + (1294505069/2500000000 : ℝ)*x 1 + (-8816561/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342189527/2500000000 : ℝ)^4229 ≤ (44011717562563/100000000000000 : ℝ)^3205 := by
    have hnat : (1342189527 : ℕ)^4229*100000000000000^3205 ≤ 44011717562563^3205*2500000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342189527 2500000000 44011717562563 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294505069/2500000000 : ℝ)^4229 ≤ (2622520297353/6250000000000 : ℝ)^3205 := by
    have hnat : (1294505069 : ℕ)^4229*6250000000000^3205 ≤ 2622520297353^3205*2500000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294505069 2500000000 2622520297353 6250000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8816561/39062500 : ℝ)^4229 ≤ (2805591531653/20000000000000 : ℝ)^3205 := by
    have hnat : (8816561 : ℕ)^4229*20000000000000^3205 ≤ 2805591531653^3205*39062500^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8816561 39062500 2805591531653 20000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342189527/2500000000 : ℝ), (1294505069/2500000000 : ℝ), (-8816561/39062500 : ℝ)] ![(44011717562563/100000000000000 : ℝ), (2622520297353/6250000000000 : ℝ), (2805591531653/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342189527/2500000000 : ℝ)|^4229 ≤ (44011717562563/100000000000000 : ℝ)^3205
        have hw : |(1342189527/2500000000 : ℝ)|=(1342189527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1294505069/2500000000 : ℝ)|^4229 ≤ (2622520297353/6250000000000 : ℝ)^3205
        have hw : |(1294505069/2500000000 : ℝ)|=(1294505069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8816561/39062500 : ℝ)|^4229 ≤ (2805591531653/20000000000000 : ℝ)^3205
        have hw : |(-8816561/39062500 : ℝ)|=(8816561/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s2_3 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (867859777/2000000000 : ℝ)*x 0 + (31513267/78125000 : ℝ)*x 1 + (2333588993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (867859777/2000000000 : ℝ)^4229 ≤ (2077087777869/6250000000000 : ℝ)^3205 := by
    have hnat : (867859777 : ℕ)^4229*6250000000000^3205 ≤ 2077087777869^3205*2000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867859777 2000000000 2077087777869 6250000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31513267/78125000 : ℝ)^4229 ≤ (30180423322469/100000000000000 : ℝ)^3205 := by
    have hnat : (31513267 : ℕ)^4229*100000000000000^3205 ≤ 30180423322469^3205*78125000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31513267 78125000 30180423322469 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2333588993/5000000000 : ℝ)^4229 ≤ (36586172209141/100000000000000 : ℝ)^3205 := by
    have hnat : (2333588993 : ℕ)^4229*100000000000000^3205 ≤ 36586172209141^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2333588993 5000000000 36586172209141 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(867859777/2000000000 : ℝ), (31513267/78125000 : ℝ), (2333588993/5000000000 : ℝ)] ![(2077087777869/6250000000000 : ℝ), (30180423322469/100000000000000 : ℝ), (36586172209141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(867859777/2000000000 : ℝ)|^4229 ≤ (2077087777869/6250000000000 : ℝ)^3205
        have hw : |(867859777/2000000000 : ℝ)|=(867859777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(31513267/78125000 : ℝ)|^4229 ≤ (30180423322469/100000000000000 : ℝ)^3205
        have hw : |(31513267/78125000 : ℝ)|=(31513267/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2333588993/5000000000 : ℝ)|^4229 ≤ (36586172209141/100000000000000 : ℝ)^3205
        have hw : |(2333588993/5000000000 : ℝ)|=(2333588993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s2_4 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2096197697/10000000000 : ℝ)*x 0 + (5179987189/10000000000 : ℝ)*x 1 + (5486932707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096197697/10000000000 : ℝ)^4229 ≤ (12724165543837/100000000000000 : ℝ)^3205 := by
    have hnat : (2096197697 : ℕ)^4229*100000000000000^3205 ≤ 12724165543837^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096197697 10000000000 12724165543837 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179987189/10000000000 : ℝ)^4229 ≤ (41981357516723/100000000000000 : ℝ)^3205 := by
    have hnat : (5179987189 : ℕ)^4229*100000000000000^3205 ≤ 41981357516723^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179987189 10000000000 41981357516723 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5486932707/10000000000 : ℝ)^4229 ≤ (22647238462643/50000000000000 : ℝ)^3205 := by
    have hnat : (5486932707 : ℕ)^4229*50000000000000^3205 ≤ 22647238462643^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486932707 10000000000 22647238462643 50000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2096197697/10000000000 : ℝ), (5179987189/10000000000 : ℝ), (5486932707/10000000000 : ℝ)] ![(12724165543837/100000000000000 : ℝ), (41981357516723/100000000000000 : ℝ), (22647238462643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2096197697/10000000000 : ℝ)|^4229 ≤ (12724165543837/100000000000000 : ℝ)^3205
        have hw : |(-2096197697/10000000000 : ℝ)|=(2096197697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179987189/10000000000 : ℝ)|^4229 ≤ (41981357516723/100000000000000 : ℝ)^3205
        have hw : |(5179987189/10000000000 : ℝ)|=(5179987189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5486932707/10000000000 : ℝ)|^4229 ≤ (22647238462643/50000000000000 : ℝ)^3205
        have hw : |(5486932707/10000000000 : ℝ)|=(5486932707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s2_5 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322312613/2500000000 : ℝ)*x 0 + (-1948126831/10000000000 : ℝ)*x 1 + (21947731/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322312613/2500000000 : ℝ)^4229 ≤ (8630746024097/20000000000000 : ℝ)^3205 := by
    have hnat : (1322312613 : ℕ)^4229*20000000000000^3205 ≤ 8630746024097^3205*2500000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322312613 2500000000 8630746024097 20000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1948126831/10000000000 : ℝ)^4229 ≤ (2887948116497/25000000000000 : ℝ)^3205 := by
    have hnat : (1948126831 : ℕ)^4229*25000000000000^3205 ≤ 2887948116497^3205*10000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948126831 10000000000 2887948116497 25000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21947731/40000000 : ℝ)^4229 ≤ (45294477393661/100000000000000 : ℝ)^3205 := by
    have hnat : (21947731 : ℕ)^4229*100000000000000^3205 ≤ 45294477393661^3205*40000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21947731 40000000 45294477393661 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322312613/2500000000 : ℝ), (-1948126831/10000000000 : ℝ), (21947731/40000000 : ℝ)] ![(8630746024097/20000000000000 : ℝ), (2887948116497/25000000000000 : ℝ), (45294477393661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322312613/2500000000 : ℝ)|^4229 ≤ (8630746024097/20000000000000 : ℝ)^3205
        have hw : |(1322312613/2500000000 : ℝ)|=(1322312613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1948126831/10000000000 : ℝ)|^4229 ≤ (2887948116497/25000000000000 : ℝ)^3205
        have hw : |(-1948126831/10000000000 : ℝ)|=(1948126831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21947731/40000000 : ℝ)|^4229 ≤ (45294477393661/100000000000000 : ℝ)^3205
        have hw : |(21947731/40000000 : ℝ)|=(21947731/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s2_6 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528925057/1000000000 : ℝ)*x 0 + (2743466433/5000000000 : ℝ)*x 1 + (-487031627/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528925057/1000000000 : ℝ)^4229 ≤ (43153731390813/100000000000000 : ℝ)^3205 := by
    have hnat : (528925057 : ℕ)^4229*100000000000000^3205 ≤ 43153731390813^3205*1000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528925057 1000000000 43153731390813 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2743466433/5000000000 : ℝ)^4229 ≤ (1415452458037/3125000000000 : ℝ)^3205 := by
    have hnat : (2743466433 : ℕ)^4229*3125000000000^3205 ≤ 1415452458037^3205*5000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743466433 5000000000 1415452458037 3125000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (487031627/2500000000 : ℝ)^4229 ≤ (11551789938761/100000000000000 : ℝ)^3205 := by
    have hnat : (487031627 : ℕ)^4229*100000000000000^3205 ≤ 11551789938761^3205*2500000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487031627 2500000000 11551789938761 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528925057/1000000000 : ℝ), (2743466433/5000000000 : ℝ), (-487031627/2500000000 : ℝ)] ![(43153731390813/100000000000000 : ℝ), (1415452458037/3125000000000 : ℝ), (11551789938761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528925057/1000000000 : ℝ)|^4229 ≤ (43153731390813/100000000000000 : ℝ)^3205
        have hw : |(528925057/1000000000 : ℝ)|=(528925057/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2743466433/5000000000 : ℝ)|^4229 ≤ (1415452458037/3125000000000 : ℝ)^3205
        have hw : |(2743466433/5000000000 : ℝ)|=(2743466433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-487031627/2500000000 : ℝ)|^4229 ≤ (11551789938761/100000000000000 : ℝ)^3205
        have hw : |(-487031627/2500000000 : ℝ)|=(487031627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1265_s2_7 (p : ℝ) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (867889751/2000000000 : ℝ)*x 0 + (932634061/2000000000 : ℝ)*x 1 + (1009435607/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (867889751/2000000000 : ℝ)^4229 ≤ (33234918990351/100000000000000 : ℝ)^3205 := by
    have hnat : (867889751 : ℕ)^4229*100000000000000^3205 ≤ 33234918990351^3205*2000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867889751 2000000000 33234918990351 100000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (932634061/2000000000 : ℝ)^4229 ≤ (1461788959823/4000000000000 : ℝ)^3205 := by
    have hnat : (932634061 : ℕ)^4229*4000000000000^3205 ≤ 1461788959823^3205*2000000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932634061 2000000000 1461788959823 4000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1009435607/2500000000 : ℝ)^4229 ≤ (3022035700191/10000000000000 : ℝ)^3205 := by
    have hnat : (1009435607 : ℕ)^4229*10000000000000^3205 ≤ 3022035700191^3205*2500000000^4229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009435607 2500000000 3022035700191 10000000000000 4229 3205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4229/1024 : ℝ)) 4229 3205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(867889751/2000000000 : ℝ), (932634061/2000000000 : ℝ), (1009435607/2500000000 : ℝ)] ![(33234918990351/100000000000000 : ℝ), (1461788959823/4000000000000 : ℝ), (3022035700191/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(867889751/2000000000 : ℝ)|^4229 ≤ (33234918990351/100000000000000 : ℝ)^3205
        have hw : |(867889751/2000000000 : ℝ)|=(867889751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(932634061/2000000000 : ℝ)|^4229 ≤ (1461788959823/4000000000000 : ℝ)^3205
        have hw : |(932634061/2000000000 : ℝ)|=(932634061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1009435607/2500000000 : ℝ)|^4229 ≤ (3022035700191/10000000000000 : ℝ)^3205
        have hw : |(1009435607/2500000000 : ℝ)|=(1009435607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1265_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37969791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9951/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6311/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1199/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4041/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9951/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6311/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9951/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6311/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9951/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6311/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9951/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6311/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9951/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6311/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9951/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6311/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6311/100000 : ℝ) ^ (8457/2048 : ℝ) ≤ (1109511957700661/100000000000000000000 : ℝ) := by
    have hpowers : (6311/100000 : ℝ)^8457 ≤ (1109511957700661/100000000000000000000 : ℝ)^2048 := by
      have hnat : (6311 : ℕ)^8457*100000000000000000000^2048 ≤ 1109511957700661^2048*100000^8457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6311 100000 1109511957700661 100000000000000000000 8457 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6311/100000 : ℝ)) (X := (1109511957700661/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (9951/50000 : ℝ) ^ (8457/2048 : ℝ) ≤ (994621832344831/781250000000000000 : ℝ) := by
    have hpowers : (9951/50000 : ℝ)^8457 ≤ (994621832344831/781250000000000000 : ℝ)^2048 := by
      have hnat : (9951 : ℕ)^8457*781250000000000000^2048 ≤ 994621832344831^2048*50000^8457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9951 50000 994621832344831 781250000000000000 8457 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9951/50000 : ℝ)) (X := (994621832344831/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001109511957700661/50000000000000000000 : ℝ) ≤ (5000026868409409/5000000000000000 : ℝ) ^ (8457/2048 : ℝ) := by
    have hpowers : (50001109511957700661/50000000000000000000 : ℝ)^2048 ≤ (5000026868409409/5000000000000000 : ℝ)^8457 := by
      have hnat : (50001109511957700661 : ℕ)^2048*5000000000000000^8457 ≤ 5000026868409409^8457*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001109511957700661 50000000000000000000 5000026868409409 5000000000000000 2048 8457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000026868409409/5000000000000000 : ℝ)) (X := (50001109511957700661/50000000000000000000 : ℝ)) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100128421106497839029/100000000000000000000 : ℝ) ≤ (625194275852081/625000000000000 : ℝ) ^ (8457/2048 : ℝ) := by
    have hpowers : (100128421106497839029/100000000000000000000 : ℝ)^2048 ≤ (625194275852081/625000000000000 : ℝ)^8457 := by
      have hnat : (100128421106497839029 : ℕ)^2048*625000000000000^8457 ≤ 625194275852081^8457*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100128421106497839029 100000000000000000000 625194275852081 625000000000000 2048 8457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625194275852081/625000000000000 : ℝ)) (X := (100128421106497839029/100000000000000000000 : ℝ)) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (391619621832344831/390625000000000000 : ℝ) ≤ (5003081545223887/5000000000000000 : ℝ) ^ (8457/2048 : ℝ) := by
    have hpowers : (391619621832344831/390625000000000000 : ℝ)^2048 ≤ (5003081545223887/5000000000000000 : ℝ)^8457 := by
      have hnat : (391619621832344831 : ℕ)^2048*5000000000000000^8457 ≤ 5003081545223887^8457*390625000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        391619621832344831 390625000000000000 5003081545223887 5000000000000000 2048 8457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003081545223887/5000000000000000 : ℝ)) (X := (391619621832344831/390625000000000000 : ℝ)) (by norm_num) 8457 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1109511957700661/100000000000000000000 : ℝ) ≤ ((67936087103176107061/67955000000000000000 : ℝ)+2*(1527338407239/679550000000000 : ℝ)*(6311/100000 : ℝ))^(8457/2048 : ℝ) := by
    rw [show (67936087103176107061/67955000000000000000 : ℝ)+2*(1527338407239/679550000000000 : ℝ)*(6311/100000 : ℝ)=(5000026868409409/5000000000000000 : ℝ) by norm_num, show 1+2*(1109511957700661/100000000000000000000 : ℝ)=(50001109511957700661/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(994621832344831/781250000000000000 : ℝ)+(1109511957700661/100000000000000000000 : ℝ) ≤ ((67936087103176107061/67955000000000000000 : ℝ)+(1527338407239/679550000000000 : ℝ)*((9951/50000 : ℝ)+(6311/100000 : ℝ)))^(8457/2048 : ℝ) := by
    rw [show (67936087103176107061/67955000000000000000 : ℝ)+(1527338407239/679550000000000 : ℝ)*((9951/50000 : ℝ)+(6311/100000 : ℝ))=(625194275852081/625000000000000 : ℝ) by norm_num, show 1+(994621832344831/781250000000000000 : ℝ)+(1109511957700661/100000000000000000000 : ℝ)=(100128421106497839029/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(994621832344831/781250000000000000 : ℝ) ≤ ((67936087103176107061/67955000000000000000 : ℝ)+2*(1527338407239/679550000000000 : ℝ)*(9951/50000 : ℝ))^(8457/2048 : ℝ) := by
    rw [show (67936087103176107061/67955000000000000000 : ℝ)+2*(1527338407239/679550000000000 : ℝ)*(9951/50000 : ℝ)=(5003081545223887/5000000000000000 : ℝ) by norm_num, show 1+2*(994621832344831/781250000000000000 : ℝ)=(391619621832344831/390625000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (67936087103176107061/67955000000000000000 : ℝ)*(X 1 0+X 2 0)+(1527338407239/679550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8457/2048 : ℝ)) (lo := (6311/100000 : ℝ)) (hi := (9951/50000 : ℝ)) (c := (67936087103176107061/67955000000000000000 : ℝ)) (alpha := (1527338407239/679550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (67936087103176107061/67955000000000000000 : ℝ)*(X 0 1+X 2 1)+(1527338407239/679550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8457/2048 : ℝ)) (lo := (6311/100000 : ℝ)) (hi := (9951/50000 : ℝ)) (c := (67936087103176107061/67955000000000000000 : ℝ)) (alpha := (1527338407239/679550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (67936087103176107061/67955000000000000000 : ℝ)*(X 0 2+X 1 2)+(1527338407239/679550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8457/2048 : ℝ)) (lo := (6311/100000 : ℝ)) (hi := (9951/50000 : ℝ)) (c := (67936087103176107061/67955000000000000000 : ℝ)) (alpha := (1527338407239/679550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2096123939/10000000000 : ℝ)*X 0 0+(5488917997/10000000000 : ℝ)*X 0 1+(5178020053/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5368758169/10000000000 : ℝ)*X 1 0+(-451407909/2000000000 : ℝ)*X 1 1+(517802027/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1342189527/2500000000 : ℝ)*X 2 0+(1294505069/2500000000 : ℝ)*X 2 1+(-8816561/39062500 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((867859777/2000000000 : ℝ)*X 0 0+(31513267/78125000 : ℝ)*X 0 1+(2333588993/5000000000 : ℝ)*X 0 2+(867859777/2000000000 : ℝ)*X 1 0+(31513267/78125000 : ℝ)*X 1 1+(2333588993/5000000000 : ℝ)*X 1 2+(867859777/2000000000 : ℝ)*X 2 0+(31513267/78125000 : ℝ)*X 2 1+(2333588993/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2096197697/10000000000 : ℝ)*X 0 0+(5179987189/10000000000 : ℝ)*X 0 1+(5486932707/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1322312613/2500000000 : ℝ)*X 1 0+(-1948126831/10000000000 : ℝ)*X 1 1+(21947731/40000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((528925057/1000000000 : ℝ)*X 2 0+(2743466433/5000000000 : ℝ)*X 2 1+(-487031627/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((867889751/2000000000 : ℝ)*X 0 0+(932634061/2000000000 : ℝ)*X 0 1+(1009435607/2500000000 : ℝ)*X 0 2+(867889751/2000000000 : ℝ)*X 1 0+(932634061/2000000000 : ℝ)*X 1 1+(1009435607/2500000000 : ℝ)*X 1 2+(867889751/2000000000 : ℝ)*X 2 0+(932634061/2000000000 : ℝ)*X 2 1+(1009435607/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1265_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6174754952910425088294682269/1698875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (557330169/100000000000000 : ℝ)*(base19) + (507415277/100000000000000 : ℝ)*(base23) + (3588707/50000000000000 : ℝ)*(lower2) + (3223729/3125000000000 : ℝ)*(upper3) + (33508189/100000000000000 : ℝ)*(upper5) + (2397547648100843/100000000000000 : ℝ)*(major0) + (2397547648100843/100000000000000 : ℝ)*(major1) + (2397547648100843/100000000000000 : ℝ)*(major2) + (402062329960353/12500000000000 : ℝ)*(sp0) + (160825285102893/5000000000000 : ℝ)*(sp1) + (201031609498297/6250000000000 : ℝ)*(sp2) + (1578585292010593/100000000000000 : ℝ)*(sp3) + (1904926301/25000000000000 : ℝ)*(sp4) + (724729851/20000000000000 : ℝ)*(sp7) + (197323614457481/12500000000000 : ℝ)*(f.failure) + (804126564847007/25000000000000 : ℝ)*(f.sum) + (1699903584993/2123593750000000000000000000 : ℝ)*base66 + (10193090844638447577/6795500000000000000000000000000000 : ℝ)*base68 + (5722382435638947577/6795500000000000000000000000000000 : ℝ)*base70 + (1122514819044947577/6795500000000000000000000000000000 : ℝ)*base72 + (22308566234111/67955000000000000000000000000 : ℝ)*base74 + (33145250971788947577/6795500000000000000000000000000000 : ℝ)*base76 + (44343356391097052423/6795500000000000000000000000000000 : ℝ)*base77 + (45213730456932447577/6795500000000000000000000000000000 : ℝ)*base80 + (10483422611347/8494375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2418529/312500000000000000000 : ℝ)*base90 + (2418529/312500000000000000000 : ℝ)*base92 + (2418529/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23846320736526127187834247021/3397750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (72095131/4000000000000 : ℝ)*(base19) + (508621/25000000000 : ℝ)*(base23) + (36256657/100000000000000 : ℝ)*(upper2) + (244685573/100000000000000 : ℝ)*(upper3) + (33786639/25000000000000 : ℝ)*(upper5) + (2428405909072787/100000000000000 : ℝ)*(major0) + (2428405909072787/100000000000000 : ℝ)*(major1) + (2428405909072787/100000000000000 : ℝ)*(major2) + (4716132343/25000000000000 : ℝ)*(sp1) + (12455057097/50000000000000 : ℝ)*(sp2) + (1628952514536601/50000000000000 : ℝ)*(sp4) + (1628942181082777/50000000000000 : ℝ)*(sp5) + (25452172534961/781250000000 : ℝ)*(sp6) + (319781311026019/20000000000000 : ℝ)*(sp7) + (319781311026019/20000000000000 : ℝ)*(f.failure) + (1628952514536601/50000000000000 : ℝ)*(f.sum) + (37998857430919/67955000000000000000000000000 : ℝ)*base66 + (33977262995448550993/6795500000000000000000000000000000 : ℝ)*base68 + (38516319401804050993/6795500000000000000000000000000000 : ℝ)*base70 + (27885477150467449007/6795500000000000000000000000000000 : ℝ)*base71 + (136701315614069/67955000000000000000000000000 : ℝ)*base74 + (6063206248962949007/6795500000000000000000000000000000 : ℝ)*base75 + (12883236492770550993/6795500000000000000000000000000000 : ℝ)*base78 + (39787424288825550993/6795500000000000000000000000000000 : ℝ)*base80 + (21196525931663/33977500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1992029/500000000000000000000 : ℝ)*base89 + (1992029/500000000000000000000 : ℝ)*base91 + (1992029/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1265_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37969791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9951/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6311/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1199/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4041/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1265_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1265_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37969791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1199/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4041/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1265_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1265_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1265_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8457/2048 : ℝ) ≤ p) (hpb : p ≤ (4229/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37969791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1199/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4041/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1265_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
