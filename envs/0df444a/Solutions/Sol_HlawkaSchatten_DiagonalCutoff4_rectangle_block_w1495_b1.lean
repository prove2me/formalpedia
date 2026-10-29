-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1495_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:49:53.254868+00:00
-- url     : https://prove2.me/submissions/c4ad4718-ac5e-444e-a000-aec5692df3d6

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
theorem support_rectangle_w1495_s3_0 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1892817057/10000000000 : ℝ)*x 0 + (5439431687/10000000000 : ℝ)*x 1 + (2606577613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1892817057/10000000000 : ℝ)^4487 ≤ (1446310631603/12500000000000 : ℝ)^3463 := by
    have hnat : (1892817057 : ℕ)^4487*12500000000000^3463 ≤ 1446310631603^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1892817057 10000000000 1446310631603 12500000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439431687/10000000000 : ℝ)^4487 ≤ (45431533857559/100000000000000 : ℝ)^3463 := by
    have hnat : (5439431687 : ℕ)^4487*100000000000000^3463 ≤ 45431533857559^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439431687 10000000000 45431533857559 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2606577613/5000000000 : ℝ)^4487 ≤ (21498990534101/50000000000000 : ℝ)^3463 := by
    have hnat : (2606577613 : ℕ)^4487*50000000000000^3463 ≤ 21498990534101^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606577613 5000000000 21498990534101 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1892817057/10000000000 : ℝ), (5439431687/10000000000 : ℝ), (2606577613/5000000000 : ℝ)] ![(1446310631603/12500000000000 : ℝ), (45431533857559/100000000000000 : ℝ), (21498990534101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1892817057/10000000000 : ℝ)|^4487 ≤ (1446310631603/12500000000000 : ℝ)^3463
        have hw : |(-1892817057/10000000000 : ℝ)|=(1892817057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439431687/10000000000 : ℝ)|^4487 ≤ (45431533857559/100000000000000 : ℝ)^3463
        have hw : |(5439431687/10000000000 : ℝ)|=(5439431687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2606577613/5000000000 : ℝ)|^4487 ≤ (21498990534101/50000000000000 : ℝ)^3463
        have hw : |(2606577613/5000000000 : ℝ)|=(2606577613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s3_1 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676777811/5000000000 : ℝ)*x 0 + (-50221063/250000000 : ℝ)*x 1 + (2606577373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676777811/5000000000 : ℝ)^4487 ≤ (8900872125177/20000000000000 : ℝ)^3463 := by
    have hnat : (2676777811 : ℕ)^4487*20000000000000^3463 ≤ 8900872125177^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676777811 5000000000 8900872125177 20000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (50221063/250000000 : ℝ)^4487 ≤ (12497663419737/100000000000000 : ℝ)^3463 := by
    have hnat : (50221063 : ℕ)^4487*100000000000000^3463 ≤ 12497663419737^3463*250000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50221063 250000000 12497663419737 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2606577373/5000000000 : ℝ)^4487 ≤ (42997975938499/100000000000000 : ℝ)^3463 := by
    have hnat : (2606577373 : ℕ)^4487*100000000000000^3463 ≤ 42997975938499^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606577373 5000000000 42997975938499 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676777811/5000000000 : ℝ), (-50221063/250000000 : ℝ), (2606577373/5000000000 : ℝ)] ![(8900872125177/20000000000000 : ℝ), (12497663419737/100000000000000 : ℝ), (42997975938499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676777811/5000000000 : ℝ)|^4487 ≤ (8900872125177/20000000000000 : ℝ)^3463
        have hw : |(2676777811/5000000000 : ℝ)|=(2676777811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-50221063/250000000 : ℝ)|^4487 ≤ (12497663419737/100000000000000 : ℝ)^3463
        have hw : |(-50221063/250000000 : ℝ)|=(50221063/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2606577373/5000000000 : ℝ)|^4487 ≤ (42997975938499/100000000000000 : ℝ)^3463
        have hw : |(2606577373/5000000000 : ℝ)|=(2606577373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s3_2 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338389227/2500000000 : ℝ)*x 0 + (1042630859/2000000000 : ℝ)*x 1 + (-10044207/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338389227/2500000000 : ℝ)^4487 ≤ (1112609361941/2500000000000 : ℝ)^3463 := by
    have hnat : (1338389227 : ℕ)^4487*2500000000000^3463 ≤ 1112609361941^3463*2500000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338389227 2500000000 1112609361941 2500000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042630859/2000000000 : ℝ)^4487 ≤ (10749492779679/25000000000000 : ℝ)^3463 := by
    have hnat : (1042630859 : ℕ)^4487*25000000000000^3463 ≤ 10749492779679^3463*2000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042630859 2000000000 10749492779679 25000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10044207/50000000 : ℝ)^4487 ≤ (3124413597867/25000000000000 : ℝ)^3463 := by
    have hnat : (10044207 : ℕ)^4487*25000000000000^3463 ≤ 3124413597867^3463*50000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10044207 50000000 3124413597867 25000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338389227/2500000000 : ℝ), (1042630859/2000000000 : ℝ), (-10044207/50000000 : ℝ)] ![(1112609361941/2500000000000 : ℝ), (10749492779679/25000000000000 : ℝ), (3124413597867/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338389227/2500000000 : ℝ)|^4487 ≤ (1112609361941/2500000000000 : ℝ)^3463
        have hw : |(1338389227/2500000000 : ℝ)|=(1338389227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042630859/2000000000 : ℝ)|^4487 ≤ (10749492779679/25000000000000 : ℝ)^3463
        have hw : |(1042630859/2000000000 : ℝ)|=(1042630859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-10044207/50000000 : ℝ)|^4487 ≤ (3124413597867/25000000000000 : ℝ)^3463
        have hw : |(-10044207/50000000 : ℝ)|=(10044207/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s3_3 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2138687571/5000000000 : ℝ)*x 0 + (100759027/250000000 : ℝ)*x 1 + (56716543/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138687571/5000000000 : ℝ)^4487 ≤ (33274952958427/100000000000000 : ℝ)^3463 := by
    have hnat : (2138687571 : ℕ)^4487*100000000000000^3463 ≤ 33274952958427^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138687571 5000000000 33274952958427 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100759027/250000000 : ℝ)^4487 ≤ (3850837694167/12500000000000 : ℝ)^3463 := by
    have hnat : (100759027 : ℕ)^4487*12500000000000^3463 ≤ 3850837694167^3463*250000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100759027 250000000 3850837694167 12500000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56716543/125000000 : ℝ)^4487 ≤ (35918345477527/100000000000000 : ℝ)^3463 := by
    have hnat : (56716543 : ℕ)^4487*100000000000000^3463 ≤ 35918345477527^3463*125000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56716543 125000000 35918345477527 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2138687571/5000000000 : ℝ), (100759027/250000000 : ℝ), (56716543/125000000 : ℝ)] ![(33274952958427/100000000000000 : ℝ), (3850837694167/12500000000000 : ℝ), (35918345477527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2138687571/5000000000 : ℝ)|^4487 ≤ (33274952958427/100000000000000 : ℝ)^3463
        have hw : |(2138687571/5000000000 : ℝ)|=(2138687571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(100759027/250000000 : ℝ)|^4487 ≤ (3850837694167/12500000000000 : ℝ)^3463
        have hw : |(100759027/250000000 : ℝ)|=(100759027/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(56716543/125000000 : ℝ)|^4487 ≤ (35918345477527/100000000000000 : ℝ)^3463
        have hw : |(56716543/125000000 : ℝ)|=(56716543/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s3_4 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1892849571/10000000000 : ℝ)*x 0 + (2607177699/5000000000 : ℝ)*x 1 + (169944457/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1892849571/10000000000 : ℝ)^4487 ≤ (11570742577001/100000000000000 : ℝ)^3463 := by
    have hnat : (1892849571 : ℕ)^4487*100000000000000^3463 ≤ 11570742577001^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1892849571 10000000000 11570742577001 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607177699/5000000000 : ℝ)^4487 ≤ (43010807600449/100000000000000 : ℝ)^3463 := by
    have hnat : (2607177699 : ℕ)^4487*100000000000000^3463 ≤ 43010807600449^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607177699 5000000000 43010807600449 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169944457/312500000 : ℝ)^4487 ≤ (45418449810171/100000000000000 : ℝ)^3463 := by
    have hnat : (169944457 : ℕ)^4487*100000000000000^3463 ≤ 45418449810171^3463*312500000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169944457 312500000 45418449810171 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1892849571/10000000000 : ℝ), (2607177699/5000000000 : ℝ), (169944457/312500000 : ℝ)] ![(11570742577001/100000000000000 : ℝ), (43010807600449/100000000000000 : ℝ), (45418449810171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1892849571/10000000000 : ℝ)|^4487 ≤ (11570742577001/100000000000000 : ℝ)^3463
        have hw : |(-1892849571/10000000000 : ℝ)|=(1892849571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607177699/5000000000 : ℝ)|^4487 ≤ (43010807600449/100000000000000 : ℝ)^3463
        have hw : |(2607177699/5000000000 : ℝ)|=(2607177699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169944457/312500000 : ℝ)|^4487 ≤ (45418449810171/100000000000000 : ℝ)^3463
        have hw : |(169944457/312500000 : ℝ)|=(169944457/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s3_5 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294310371/10000000000 : ℝ)*x 0 + (-222971783/1250000000 : ℝ)*x 1 + (1359555723/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294310371/10000000000 : ℝ)^4487 ≤ (43867265402923/100000000000000 : ℝ)^3463 := by
    have hnat : (5294310371 : ℕ)^4487*100000000000000^3463 ≤ 43867265402923^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294310371 10000000000 43867265402923 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222971783/1250000000 : ℝ)^4487 ≤ (10714281870849/100000000000000 : ℝ)^3463 := by
    have hnat : (222971783 : ℕ)^4487*100000000000000^3463 ≤ 10714281870849^3463*1250000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222971783 1250000000 10714281870849 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359555723/2500000000 : ℝ)^4487 ≤ (11354613177569/25000000000000 : ℝ)^3463 := by
    have hnat : (1359555723 : ℕ)^4487*25000000000000^3463 ≤ 11354613177569^3463*2500000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359555723 2500000000 11354613177569 25000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294310371/10000000000 : ℝ), (-222971783/1250000000 : ℝ), (1359555723/2500000000 : ℝ)] ![(43867265402923/100000000000000 : ℝ), (10714281870849/100000000000000 : ℝ), (11354613177569/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294310371/10000000000 : ℝ)|^4487 ≤ (43867265402923/100000000000000 : ℝ)^3463
        have hw : |(5294310371/10000000000 : ℝ)|=(5294310371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-222971783/1250000000 : ℝ)|^4487 ≤ (10714281870849/100000000000000 : ℝ)^3463
        have hw : |(-222971783/1250000000 : ℝ)|=(222971783/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359555723/2500000000 : ℝ)|^4487 ≤ (11354613177569/25000000000000 : ℝ)^3463
        have hw : |(1359555723/2500000000 : ℝ)|=(1359555723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s3_6 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647155621/5000000000 : ℝ)*x 0 + (1359555559/2500000000 : ℝ)*x 1 + (-222971747/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647155621/5000000000 : ℝ)^4487 ≤ (43867274753813/100000000000000 : ℝ)^3463 := by
    have hnat : (2647155621 : ℕ)^4487*100000000000000^3463 ≤ 43867274753813^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647155621 5000000000 43867274753813 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359555559/2500000000 : ℝ)^4487 ≤ (5677305701439/12500000000000 : ℝ)^3463 := by
    have hnat : (1359555559 : ℕ)^4487*12500000000000^3463 ≤ 5677305701439^3463*2500000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359555559 2500000000 5677305701439 12500000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (222971747/1250000000 : ℝ)^4487 ≤ (214285592589/2000000000000 : ℝ)^3463 := by
    have hnat : (222971747 : ℕ)^4487*2000000000000^3463 ≤ 214285592589^3463*1250000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222971747 1250000000 214285592589 2000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647155621/5000000000 : ℝ), (1359555559/2500000000 : ℝ), (-222971747/1250000000 : ℝ)] ![(43867274753813/100000000000000 : ℝ), (5677305701439/12500000000000 : ℝ), (214285592589/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647155621/5000000000 : ℝ)|^4487 ≤ (43867274753813/100000000000000 : ℝ)^3463
        have hw : |(2647155621/5000000000 : ℝ)|=(2647155621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359555559/2500000000 : ℝ)|^4487 ≤ (5677305701439/12500000000000 : ℝ)^3463
        have hw : |(1359555559/2500000000 : ℝ)|=(1359555559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-222971747/1250000000 : ℝ)|^4487 ≤ (214285592589/2000000000000 : ℝ)^3463
        have hw : |(-222971747/1250000000 : ℝ)|=(222971747/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s3_7 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2138724133/5000000000 : ℝ)*x 0 + (1133658209/2500000000 : ℝ)*x 1 + (4033072683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138724133/5000000000 : ℝ)^4487 ≤ (1663784501081/5000000000000 : ℝ)^3463 := by
    have hnat : (2138724133 : ℕ)^4487*5000000000000^3463 ≤ 1663784501081^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138724133 5000000000 1663784501081 5000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133658209/2500000000 : ℝ)^4487 ≤ (35890750384461/100000000000000 : ℝ)^3463 := by
    have hnat : (1133658209 : ℕ)^4487*100000000000000^3463 ≤ 35890750384461^3463*2500000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133658209 2500000000 35890750384461 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4033072683/10000000000 : ℝ)^4487 ≤ (15416779790589/50000000000000 : ℝ)^3463 := by
    have hnat : (4033072683 : ℕ)^4487*50000000000000^3463 ≤ 15416779790589^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033072683 10000000000 15416779790589 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2138724133/5000000000 : ℝ), (1133658209/2500000000 : ℝ), (4033072683/10000000000 : ℝ)] ![(1663784501081/5000000000000 : ℝ), (35890750384461/100000000000000 : ℝ), (15416779790589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2138724133/5000000000 : ℝ)|^4487 ≤ (1663784501081/5000000000000 : ℝ)^3463
        have hw : |(2138724133/5000000000 : ℝ)|=(2138724133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1133658209/2500000000 : ℝ)|^4487 ≤ (35890750384461/100000000000000 : ℝ)^3463
        have hw : |(1133658209/2500000000 : ℝ)|=(1133658209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4033072683/10000000000 : ℝ)|^4487 ≤ (15416779790589/50000000000000 : ℝ)^3463
        have hw : |(4033072683/10000000000 : ℝ)|=(4033072683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1495_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40505603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3213/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1031/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (2693/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7781/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3213/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1031/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3213/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1031/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3213/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1031/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3213/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1031/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3213/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1031/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3213/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1031/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1031/10000 : ℝ) ^ (4485/1024 : ℝ) ≤ (238318958372601/5000000000000000000 : ℝ) := by
    have hpowers : (1031/10000 : ℝ)^4485 ≤ (238318958372601/5000000000000000000 : ℝ)^1024 := by
      have hnat : (1031 : ℕ)^4485*5000000000000000000^1024 ≤ 238318958372601^1024*10000^4485 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1031 10000 238318958372601 5000000000000000000 4485 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1031/10000 : ℝ)) (X := (238318958372601/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3213/20000 : ℝ) ^ (4485/1024 : ℝ) ≤ (16627259012464217/50000000000000000000 : ℝ) := by
    have hpowers : (3213/20000 : ℝ)^4485 ≤ (16627259012464217/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3213 : ℕ)^4485*50000000000000000000^1024 ≤ 16627259012464217^1024*20000^4485 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3213 20000 16627259012464217 50000000000000000000 4485 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3213/20000 : ℝ)) (X := (16627259012464217/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500238318958372601/2500000000000000000 : ℝ) ≤ (1250027205087827/1250000000000000 : ℝ) ^ (4485/1024 : ℝ) := by
    have hpowers : (2500238318958372601/2500000000000000000 : ℝ)^1024 ≤ (1250027205087827/1250000000000000 : ℝ)^4485 := by
      have hnat : (2500238318958372601 : ℕ)^1024*1250000000000000^4485 ≤ 1250027205087827^4485*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500238318958372601 2500000000000000000 1250027205087827 1250000000000000 1024 4485 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250027205087827/1250000000000000 : ℝ)) (X := (2500238318958372601/2500000000000000000 : ℝ)) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019010448596190227/50000000000000000000 : ℝ) ≤ (2000173590583987/2000000000000000 : ℝ) ^ (4485/1024 : ℝ) := by
    have hpowers : (50019010448596190227/50000000000000000000 : ℝ)^1024 ≤ (2000173590583987/2000000000000000 : ℝ)^4485 := by
      have hnat : (50019010448596190227 : ℕ)^1024*2000000000000000^4485 ≤ 2000173590583987^4485*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019010448596190227 50000000000000000000 2000173590583987 2000000000000000 1024 4485 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000173590583987/2000000000000000 : ℝ)) (X := (50019010448596190227/50000000000000000000 : ℝ)) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016627259012464217/25000000000000000000 : ℝ) ≤ (5000759132568627/5000000000000000 : ℝ) ^ (4485/1024 : ℝ) := by
    have hpowers : (25016627259012464217/25000000000000000000 : ℝ)^1024 ≤ (5000759132568627/5000000000000000 : ℝ)^4485 := by
      have hnat : (25016627259012464217 : ℕ)^1024*5000000000000000^4485 ≤ 5000759132568627^4485*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016627259012464217 25000000000000000000 5000759132568627 5000000000000000 1024 4485 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000759132568627/5000000000000000 : ℝ)) (X := (25016627259012464217/25000000000000000000 : ℝ)) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(238318958372601/5000000000000000000 : ℝ) ≤ ((575378430843224373/575500000000000000 : ℝ)+2*(650312217319/575500000000000 : ℝ)*(1031/10000 : ℝ))^(4485/1024 : ℝ) := by
    rw [show (575378430843224373/575500000000000000 : ℝ)+2*(650312217319/575500000000000 : ℝ)*(1031/10000 : ℝ)=(1250027205087827/1250000000000000 : ℝ) by norm_num, show 1+2*(238318958372601/5000000000000000000 : ℝ)=(2500238318958372601/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16627259012464217/50000000000000000000 : ℝ)+(238318958372601/5000000000000000000 : ℝ) ≤ ((575378430843224373/575500000000000000 : ℝ)+(650312217319/575500000000000 : ℝ)*((3213/20000 : ℝ)+(1031/10000 : ℝ)))^(4485/1024 : ℝ) := by
    rw [show (575378430843224373/575500000000000000 : ℝ)+(650312217319/575500000000000 : ℝ)*((3213/20000 : ℝ)+(1031/10000 : ℝ))=(2000173590583987/2000000000000000 : ℝ) by norm_num, show 1+(16627259012464217/50000000000000000000 : ℝ)+(238318958372601/5000000000000000000 : ℝ)=(50019010448596190227/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16627259012464217/50000000000000000000 : ℝ) ≤ ((575378430843224373/575500000000000000 : ℝ)+2*(650312217319/575500000000000 : ℝ)*(3213/20000 : ℝ))^(4485/1024 : ℝ) := by
    rw [show (575378430843224373/575500000000000000 : ℝ)+2*(650312217319/575500000000000 : ℝ)*(3213/20000 : ℝ)=(5000759132568627/5000000000000000 : ℝ) by norm_num, show 1+2*(16627259012464217/50000000000000000000 : ℝ)=(25016627259012464217/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (575378430843224373/575500000000000000 : ℝ)*(X 1 0+X 2 0)+(650312217319/575500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4485/1024 : ℝ)) (lo := (1031/10000 : ℝ)) (hi := (3213/20000 : ℝ)) (c := (575378430843224373/575500000000000000 : ℝ)) (alpha := (650312217319/575500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (575378430843224373/575500000000000000 : ℝ)*(X 0 1+X 2 1)+(650312217319/575500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4485/1024 : ℝ)) (lo := (1031/10000 : ℝ)) (hi := (3213/20000 : ℝ)) (c := (575378430843224373/575500000000000000 : ℝ)) (alpha := (650312217319/575500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (575378430843224373/575500000000000000 : ℝ)*(X 0 2+X 1 2)+(650312217319/575500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4485/1024 : ℝ)) (lo := (1031/10000 : ℝ)) (hi := (3213/20000 : ℝ)) (c := (575378430843224373/575500000000000000 : ℝ)) (alpha := (650312217319/575500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1892817057/10000000000 : ℝ)*X 0 0+(5439431687/10000000000 : ℝ)*X 0 1+(2606577613/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676777811/5000000000 : ℝ)*X 1 0+(-50221063/250000000 : ℝ)*X 1 1+(2606577373/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338389227/2500000000 : ℝ)*X 2 0+(1042630859/2000000000 : ℝ)*X 2 1+(-10044207/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2138687571/5000000000 : ℝ)*X 0 0+(100759027/250000000 : ℝ)*X 0 1+(56716543/125000000 : ℝ)*X 0 2+(2138687571/5000000000 : ℝ)*X 1 0+(100759027/250000000 : ℝ)*X 1 1+(56716543/125000000 : ℝ)*X 1 2+(2138687571/5000000000 : ℝ)*X 2 0+(100759027/250000000 : ℝ)*X 2 1+(56716543/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1892849571/10000000000 : ℝ)*X 0 0+(2607177699/5000000000 : ℝ)*X 0 1+(169944457/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294310371/10000000000 : ℝ)*X 1 0+(-222971783/1250000000 : ℝ)*X 1 1+(1359555723/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647155621/5000000000 : ℝ)*X 2 0+(1359555559/2500000000 : ℝ)*X 2 1+(-222971747/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2138724133/5000000000 : ℝ)*X 0 0+(1133658209/2500000000 : ℝ)*X 0 1+(4033072683/10000000000 : ℝ)*X 0 2+(2138724133/5000000000 : ℝ)*X 1 0+(1133658209/2500000000 : ℝ)*X 1 1+(4033072683/10000000000 : ℝ)*X 1 2+(2138724133/5000000000 : ℝ)*X 2 0+(1133658209/2500000000 : ℝ)*X 2 1+(4033072683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64683405832194665068433511/14387500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (428570133/50000000000000 : ℝ)*(base19) + (12824283/625000000000 : ℝ)*(base23) + (52586999/100000000000000 : ℝ)*(upper4) + (41680501/20000000000000 : ℝ)*(upper5) + (1597994563348423/50000000000000 : ℝ)*(major0) + (1597994563348423/50000000000000 : ℝ)*(major1) + (1597994563348423/50000000000000 : ℝ)*(major2) + (220969424631309/5000000000000 : ℝ)*(sp0) + (552424555046449/12500000000000 : ℝ)*(sp1) + (441941615252953/10000000000000 : ℝ)*(sp2) + (1972545836969523/100000000000000 : ℝ)*(sp3) + (29711788631/100000000000000 : ℝ)*(sp4) + (2613362869/12500000000000 : ℝ)*(sp5) + (7031074577/50000000000000 : ℝ)*(sp7) + (493139974779669/25000000000000 : ℝ)*(f.failure) + (441941820441481/10000000000000 : ℝ)*(f.sum) + (171832332525399/28775000000000000000000000000 : ℝ)*base65 + (387912363314399221/28775000000000000000000000000000 : ℝ)*base68 + (358477044512999221/28775000000000000000000000000000 : ℝ)*base70 + (242778119360999221/28775000000000000000000000000000 : ℝ)*base72 + (35160206377737/14387500000000000000000000000 : ℝ)*base73 + (355183699492799221/28775000000000000000000000000000 : ℝ)*base76 + (490838411496599221/28775000000000000000000000000000 : ℝ)*base78 + (468660352573199221/28775000000000000000000000000000 : ℝ)*base80 + (2667688998647/3596875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (2514593/625000000000000000000 : ℝ)*base90 + (2514593/625000000000000000000 : ℝ)*base92 + (2514593/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (127342594514913165872475477/14387500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (441080211/50000000000000 : ℝ)*(base19) + (435250417/25000000000000 : ℝ)*(base23) + (7371159/25000000000000 : ℝ)*(lower4) + (122694307/100000000000000 : ℝ)*(upper5) + (3230369208125483/100000000000000 : ℝ)*(major0) + (3230369208125483/100000000000000 : ℝ)*(major1) + (3230369208125483/100000000000000 : ℝ)*(major2) + (9068170583/100000000000000 : ℝ)*(sp0) + (32267177221/100000000000000 : ℝ)*(sp1) + (4795884777/12500000000000 : ℝ)*(sp2) + (446694981704783/10000000000000 : ℝ)*(sp4) + (4466925735880771/100000000000000 : ℝ)*(sp5) + (4466918777138529/100000000000000 : ℝ)*(sp6) + (3115280056253/156250000000 : ℝ)*(sp7) + (3115280056253/156250000000 : ℝ)*(f.failure) + (2233479442609207/50000000000000 : ℝ)*(f.sum) + (26104298967537/7193750000000000000000000000 : ℝ)*base66 + (150553946408475841/57550000000000000000000000000000 : ℝ)*base68 + (1212363861174159/57550000000000000000000000000000 : ℝ)*base69 + (201723852235575841/57550000000000000000000000000000 : ℝ)*base72 + (61308651786323/28775000000000000000000000000 : ℝ)*base74 + (533543842934825841/57550000000000000000000000000000 : ℝ)*base76 + (169466884040225841/57550000000000000000000000000000 : ℝ)*base78 + (42666037766125841/57550000000000000000000000000000 : ℝ)*base80 + (13996760538677/28775000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (11743/7812500000000000000 : ℝ)*base89 + (11743/7812500000000000000 : ℝ)*base91 + (11743/7812500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1495_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40505603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3213/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1031/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2693/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7781/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1495_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1495_s4_0 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-473337091/2500000000 : ℝ)*x 0 + (5435964739/10000000000 : ℝ)*x 1 + (20376061/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (473337091/2500000000 : ℝ)^4487 ≤ (11574693385483/100000000000000 : ℝ)^3463 := by
    have hnat : (473337091 : ℕ)^4487*100000000000000^3463 ≤ 11574693385483^3463*2500000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473337091 2500000000 11574693385483 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435964739/10000000000 : ℝ)^4487 ≤ (9078803617853/20000000000000 : ℝ)^3463 := by
    have hnat : (5435964739 : ℕ)^4487*20000000000000^3463 ≤ 9078803617853^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435964739 10000000000 9078803617853 20000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20376061/39062500 : ℝ)^4487 ≤ (43031288501343/100000000000000 : ℝ)^3463 := by
    have hnat : (20376061 : ℕ)^4487*100000000000000^3463 ≤ 43031288501343^3463*39062500^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20376061 39062500 43031288501343 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-473337091/2500000000 : ℝ), (5435964739/10000000000 : ℝ), (20376061/39062500 : ℝ)] ![(11574693385483/100000000000000 : ℝ), (9078803617853/20000000000000 : ℝ), (43031288501343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-473337091/2500000000 : ℝ)|^4487 ≤ (11574693385483/100000000000000 : ℝ)^3463
        have hw : |(-473337091/2500000000 : ℝ)|=(473337091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435964739/10000000000 : ℝ)|^4487 ≤ (9078803617853/20000000000000 : ℝ)^3463
        have hw : |(5435964739/10000000000 : ℝ)|=(5435964739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20376061/39062500 : ℝ)|^4487 ≤ (43031288501343/100000000000000 : ℝ)^3463
        have hw : |(20376061/39062500 : ℝ)|=(20376061/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s4_1 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676326143/5000000000 : ℝ)*x 0 + (-2005915323/10000000000 : ℝ)*x 1 + (652034047/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676326143/5000000000 : ℝ)^4487 ≤ (5561828857731/12500000000000 : ℝ)^3463 := by
    have hnat : (2676326143 : ℕ)^4487*12500000000000^3463 ≤ 5561828857731^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676326143 5000000000 5561828857731 12500000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2005915323/10000000000 : ℝ)^4487 ≤ (12474072500951/100000000000000 : ℝ)^3463 := by
    have hnat : (2005915323 : ℕ)^4487*100000000000000^3463 ≤ 12474072500951^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005915323 10000000000 12474072500951 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652034047/1250000000 : ℝ)^4487 ≤ (5378912078101/12500000000000 : ℝ)^3463 := by
    have hnat : (652034047 : ℕ)^4487*12500000000000^3463 ≤ 5378912078101^3463*1250000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652034047 1250000000 5378912078101 12500000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676326143/5000000000 : ℝ), (-2005915323/10000000000 : ℝ), (652034047/1250000000 : ℝ)] ![(5561828857731/12500000000000 : ℝ), (12474072500951/100000000000000 : ℝ), (5378912078101/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676326143/5000000000 : ℝ)|^4487 ≤ (5561828857731/12500000000000 : ℝ)^3463
        have hw : |(2676326143/5000000000 : ℝ)|=(2676326143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2005915323/10000000000 : ℝ)|^4487 ≤ (12474072500951/100000000000000 : ℝ)^3463
        have hw : |(-2005915323/10000000000 : ℝ)|=(2005915323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652034047/1250000000 : ℝ)|^4487 ≤ (5378912078101/12500000000000 : ℝ)^3463
        have hw : |(652034047/1250000000 : ℝ)|=(652034047/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s4_2 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070530503/2000000000 : ℝ)*x 0 + (1043254329/2000000000 : ℝ)*x 1 + (-2005915987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070530503/2000000000 : ℝ)^4487 ≤ (44494633328329/100000000000000 : ℝ)^3463 := by
    have hnat : (1070530503 : ℕ)^4487*100000000000000^3463 ≤ 44494633328329^3463*2000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070530503 2000000000 44494633328329 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043254329/2000000000 : ℝ)^4487 ≤ (43031288811317/100000000000000 : ℝ)^3463 := by
    have hnat : (1043254329 : ℕ)^4487*100000000000000^3463 ≤ 43031288811317^3463*2000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043254329 2000000000 43031288811317 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2005915987/10000000000 : ℝ)^4487 ≤ (6237038925559/50000000000000 : ℝ)^3463 := by
    have hnat : (2005915987 : ℕ)^4487*50000000000000^3463 ≤ 6237038925559^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005915987 10000000000 6237038925559 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070530503/2000000000 : ℝ), (1043254329/2000000000 : ℝ), (-2005915987/10000000000 : ℝ)] ![(44494633328329/100000000000000 : ℝ), (43031288811317/100000000000000 : ℝ), (6237038925559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070530503/2000000000 : ℝ)|^4487 ≤ (44494633328329/100000000000000 : ℝ)^3463
        have hw : |(1070530503/2000000000 : ℝ)|=(1070530503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043254329/2000000000 : ℝ)|^4487 ≤ (43031288811317/100000000000000 : ℝ)^3463
        have hw : |(1043254329/2000000000 : ℝ)|=(1043254329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2005915987/10000000000 : ℝ)|^4487 ≤ (6237038925559/50000000000000 : ℝ)^3463
        have hw : |(-2005915987/10000000000 : ℝ)|=(2005915987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s4_3 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4277706311/10000000000 : ℝ)*x 0 + (2018850429/5000000000 : ℝ)*x 1 + (4529907209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4277706311/10000000000 : ℝ)^4487 ≤ (831957276267/2500000000000 : ℝ)^3463 := by
    have hnat : (4277706311 : ℕ)^4487*2500000000000^3463 ≤ 831957276267^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4277706311 10000000000 831957276267 2500000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2018850429/5000000000 : ℝ)^4487 ≤ (15439706653209/50000000000000 : ℝ)^3463 := by
    have hnat : (2018850429 : ℕ)^4487*50000000000000^3463 ≤ 15439706653209^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018850429 5000000000 15439706653209 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4529907209/10000000000 : ℝ)^4487 ≤ (35842295619503/100000000000000 : ℝ)^3463 := by
    have hnat : (4529907209 : ℕ)^4487*100000000000000^3463 ≤ 35842295619503^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529907209 10000000000 35842295619503 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4277706311/10000000000 : ℝ), (2018850429/5000000000 : ℝ), (4529907209/10000000000 : ℝ)] ![(831957276267/2500000000000 : ℝ), (15439706653209/50000000000000 : ℝ), (35842295619503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4277706311/10000000000 : ℝ)|^4487 ≤ (831957276267/2500000000000 : ℝ)^3463
        have hw : |(4277706311/10000000000 : ℝ)|=(4277706311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2018850429/5000000000 : ℝ)|^4487 ≤ (15439706653209/50000000000000 : ℝ)^3463
        have hw : |(2018850429/5000000000 : ℝ)|=(2018850429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4529907209/10000000000 : ℝ)|^4487 ≤ (35842295619503/100000000000000 : ℝ)^3463
        have hw : |(4529907209/10000000000 : ℝ)|=(4529907209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s4_4 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-946689507/5000000000 : ℝ)*x 0 + (1304351063/2500000000 : ℝ)*x 1 + (169838229/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (946689507/5000000000 : ℝ)^4487 ≤ (11574936166129/100000000000000 : ℝ)^3463 := by
    have hnat : (946689507 : ℕ)^4487*100000000000000^3463 ≤ 11574936166129^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946689507 5000000000 11574936166129 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304351063/2500000000 : ℝ)^4487 ≤ (43043395375649/100000000000000 : ℝ)^3463 := by
    have hnat : (1304351063 : ℕ)^4487*100000000000000^3463 ≤ 43043395375649^3463*2500000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304351063 2500000000 43043395375649 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169838229/312500000 : ℝ)^4487 ≤ (22690834226823/50000000000000 : ℝ)^3463 := by
    have hnat : (169838229 : ℕ)^4487*50000000000000^3463 ≤ 22690834226823^3463*312500000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169838229 312500000 22690834226823 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-946689507/5000000000 : ℝ), (1304351063/2500000000 : ℝ), (169838229/312500000 : ℝ)] ![(11574936166129/100000000000000 : ℝ), (43043395375649/100000000000000 : ℝ), (22690834226823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-946689507/5000000000 : ℝ)|^4487 ≤ (11574936166129/100000000000000 : ℝ)^3463
        have hw : |(-946689507/5000000000 : ℝ)|=(946689507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304351063/2500000000 : ℝ)|^4487 ≤ (43043395375649/100000000000000 : ℝ)^3463
        have hw : |(1304351063/2500000000 : ℝ)|=(1304351063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169838229/312500000 : ℝ)|^4487 ≤ (22690834226823/50000000000000 : ℝ)^3463
        have hw : |(169838229/312500000 : ℝ)|=(169838229/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s4_5 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529513317/1000000000 : ℝ)*x 0 + (-893682303/5000000000 : ℝ)*x 1 + (169838229/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529513317/1000000000 : ℝ)^4487 ≤ (10969024754527/25000000000000 : ℝ)^3463 := by
    have hnat : (529513317 : ℕ)^4487*25000000000000^3463 ≤ 10969024754527^3463*1000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529513317 1000000000 10969024754527 25000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (893682303/5000000000 : ℝ)^4487 ≤ (5371116254613/50000000000000 : ℝ)^3463 := by
    have hnat : (893682303 : ℕ)^4487*50000000000000^3463 ≤ 5371116254613^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893682303 5000000000 5371116254613 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169838229/312500000 : ℝ)^4487 ≤ (22690834226823/50000000000000 : ℝ)^3463 := by
    have hnat : (169838229 : ℕ)^4487*50000000000000^3463 ≤ 22690834226823^3463*312500000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169838229 312500000 22690834226823 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529513317/1000000000 : ℝ), (-893682303/5000000000 : ℝ), (169838229/312500000 : ℝ)] ![(10969024754527/25000000000000 : ℝ), (5371116254613/50000000000000 : ℝ), (22690834226823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529513317/1000000000 : ℝ)|^4487 ≤ (10969024754527/25000000000000 : ℝ)^3463
        have hw : |(529513317/1000000000 : ℝ)|=(529513317/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-893682303/5000000000 : ℝ)|^4487 ≤ (5371116254613/50000000000000 : ℝ)^3463
        have hw : |(-893682303/5000000000 : ℝ)|=(893682303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169838229/312500000 : ℝ)|^4487 ≤ (22690834226823/50000000000000 : ℝ)^3463
        have hw : |(169838229/312500000 : ℝ)|=(169838229/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s4_6 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529513317/1000000000 : ℝ)*x 0 + (169838229/312500000 : ℝ)*x 1 + (-893682303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529513317/1000000000 : ℝ)^4487 ≤ (10969024754527/25000000000000 : ℝ)^3463 := by
    have hnat : (529513317 : ℕ)^4487*25000000000000^3463 ≤ 10969024754527^3463*1000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529513317 1000000000 10969024754527 25000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169838229/312500000 : ℝ)^4487 ≤ (22690834226823/50000000000000 : ℝ)^3463 := by
    have hnat : (169838229 : ℕ)^4487*50000000000000^3463 ≤ 22690834226823^3463*312500000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169838229 312500000 22690834226823 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (893682303/5000000000 : ℝ)^4487 ≤ (5371116254613/50000000000000 : ℝ)^3463 := by
    have hnat : (893682303 : ℕ)^4487*50000000000000^3463 ≤ 5371116254613^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893682303 5000000000 5371116254613 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529513317/1000000000 : ℝ), (169838229/312500000 : ℝ), (-893682303/5000000000 : ℝ)] ![(10969024754527/25000000000000 : ℝ), (22690834226823/50000000000000 : ℝ), (5371116254613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529513317/1000000000 : ℝ)|^4487 ≤ (10969024754527/25000000000000 : ℝ)^3463
        have hw : |(529513317/1000000000 : ℝ)|=(529513317/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169838229/312500000 : ℝ)|^4487 ≤ (22690834226823/50000000000000 : ℝ)^3463
        have hw : |(169838229/312500000 : ℝ)|=(169838229/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-893682303/5000000000 : ℝ)|^4487 ≤ (5371116254613/50000000000000 : ℝ)^3463
        have hw : |(-893682303/5000000000 : ℝ)|=(893682303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s4_7 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (427777463/1000000000 : ℝ)*x 0 + (181094841/400000000 : ℝ)*x 1 + (2020127419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427777463/1000000000 : ℝ)^4487 ≤ (415987246211/1250000000000 : ℝ)^3463 := by
    have hnat : (427777463 : ℕ)^4487*1250000000000^3463 ≤ 415987246211^3463*1000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427777463 1000000000 415987246211 1250000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (181094841/400000000 : ℝ)^4487 ≤ (35816296724379/100000000000000 : ℝ)^3463 := by
    have hnat : (181094841 : ℕ)^4487*100000000000000^3463 ≤ 35816296724379^3463*400000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181094841 400000000 35816296724379 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2020127419/5000000000 : ℝ)^4487 ≤ (3090472356471/10000000000000 : ℝ)^3463 := by
    have hnat : (2020127419 : ℕ)^4487*10000000000000^3463 ≤ 3090472356471^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020127419 5000000000 3090472356471 10000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(427777463/1000000000 : ℝ), (181094841/400000000 : ℝ), (2020127419/5000000000 : ℝ)] ![(415987246211/1250000000000 : ℝ), (35816296724379/100000000000000 : ℝ), (3090472356471/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(427777463/1000000000 : ℝ)|^4487 ≤ (415987246211/1250000000000 : ℝ)^3463
        have hw : |(427777463/1000000000 : ℝ)|=(427777463/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(181094841/400000000 : ℝ)|^4487 ≤ (35816296724379/100000000000000 : ℝ)^3463
        have hw : |(181094841/400000000 : ℝ)|=(181094841/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2020127419/5000000000 : ℝ)|^4487 ≤ (3090472356471/10000000000000 : ℝ)^3463
        have hw : |(2020127419/5000000000 : ℝ)|=(2020127419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1495_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40505603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7781/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2693/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10839/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7781/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2693/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7781/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2693/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7781/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2693/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7781/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2693/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7781/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2693/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7781/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2693/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2693/25000 : ℝ) ^ (4485/1024 : ℝ) ≤ (721907253911637/12500000000000000000 : ℝ) := by
    have hpowers : (2693/25000 : ℝ)^4485 ≤ (721907253911637/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2693 : ℕ)^4485*12500000000000000000^1024 ≤ 721907253911637^1024*25000^4485 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2693 25000 721907253911637 12500000000000000000 4485 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2693/25000 : ℝ)) (X := (721907253911637/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7781/50000 : ℝ) ^ (4485/1024 : ℝ) ≤ (3616189600751179/12500000000000000000 : ℝ) := by
    have hpowers : (7781/50000 : ℝ)^4485 ≤ (3616189600751179/12500000000000000000 : ℝ)^1024 := by
      have hnat : (7781 : ℕ)^4485*12500000000000000000^1024 ≤ 3616189600751179^1024*50000^4485 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7781 50000 3616189600751179 12500000000000000000 4485 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7781/50000 : ℝ)) (X := (3616189600751179/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250721907253911637/6250000000000000000 : ℝ) ≤ (39063530100453/39062500000000 : ℝ) ^ (4485/1024 : ℝ) := by
    have hpowers : (6250721907253911637/6250000000000000000 : ℝ)^1024 ≤ (39063530100453/39062500000000 : ℝ)^4485 := by
      have hnat : (6250721907253911637 : ℕ)^1024*39062500000000^4485 ≤ 39063530100453^4485*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250721907253911637 6250000000000000000 39063530100453 39062500000000 1024 4485 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39063530100453/39062500000000 : ℝ)) (X := (6250721907253911637/6250000000000000000 : ℝ)) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (390760565526708213/390625000000000000 : ℝ) ≤ (10000792261576739/10000000000000000 : ℝ) ^ (4485/1024 : ℝ) := by
    have hpowers : (390760565526708213/390625000000000000 : ℝ)^1024 ≤ (10000792261576739/10000000000000000 : ℝ)^4485 := by
      have hnat : (390760565526708213 : ℕ)^1024*10000000000000000^4485 ≤ 10000792261576739^4485*390625000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390760565526708213 390625000000000000 10000792261576739 10000000000000000 1024 4485 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000792261576739/10000000000000000 : ℝ)) (X := (390760565526708213/390625000000000000 : ℝ)) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253616189600751179/6250000000000000000 : ℝ) ≤ (1000132081743751/1000000000000000 : ℝ) ^ (4485/1024 : ℝ) := by
    have hpowers : (6253616189600751179/6250000000000000000 : ℝ)^1024 ≤ (1000132081743751/1000000000000000 : ℝ)^4485 := by
      have hnat : (6253616189600751179 : ℕ)^1024*1000000000000000^4485 ≤ 1000132081743751^4485*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253616189600751179 6250000000000000000 1000132081743751 1000000000000000 1024 4485 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000132081743751/1000000000000000 : ℝ)) (X := (6253616189600751179/6250000000000000000 : ℝ)) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(721907253911637/12500000000000000000 : ℝ) ≤ ((5986234492864379537/5987500000000000000 : ℝ)+2*(528555860771/479000000000000 : ℝ)*(2693/25000 : ℝ))^(4485/1024 : ℝ) := by
    rw [show (5986234492864379537/5987500000000000000 : ℝ)+2*(528555860771/479000000000000 : ℝ)*(2693/25000 : ℝ)=(39063530100453/39062500000000 : ℝ) by norm_num, show 1+2*(721907253911637/12500000000000000000 : ℝ)=(6250721907253911637/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3616189600751179/12500000000000000000 : ℝ)+(721907253911637/12500000000000000000 : ℝ) ≤ ((5986234492864379537/5987500000000000000 : ℝ)+(528555860771/479000000000000 : ℝ)*((7781/50000 : ℝ)+(2693/25000 : ℝ)))^(4485/1024 : ℝ) := by
    rw [show (5986234492864379537/5987500000000000000 : ℝ)+(528555860771/479000000000000 : ℝ)*((7781/50000 : ℝ)+(2693/25000 : ℝ))=(10000792261576739/10000000000000000 : ℝ) by norm_num, show 1+(3616189600751179/12500000000000000000 : ℝ)+(721907253911637/12500000000000000000 : ℝ)=(390760565526708213/390625000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3616189600751179/12500000000000000000 : ℝ) ≤ ((5986234492864379537/5987500000000000000 : ℝ)+2*(528555860771/479000000000000 : ℝ)*(7781/50000 : ℝ))^(4485/1024 : ℝ) := by
    rw [show (5986234492864379537/5987500000000000000 : ℝ)+2*(528555860771/479000000000000 : ℝ)*(7781/50000 : ℝ)=(1000132081743751/1000000000000000 : ℝ) by norm_num, show 1+2*(3616189600751179/12500000000000000000 : ℝ)=(6253616189600751179/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5986234492864379537/5987500000000000000 : ℝ)*(X 1 0+X 2 0)+(528555860771/479000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4485/1024 : ℝ)) (lo := (2693/25000 : ℝ)) (hi := (7781/50000 : ℝ)) (c := (5986234492864379537/5987500000000000000 : ℝ)) (alpha := (528555860771/479000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5986234492864379537/5987500000000000000 : ℝ)*(X 0 1+X 2 1)+(528555860771/479000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4485/1024 : ℝ)) (lo := (2693/25000 : ℝ)) (hi := (7781/50000 : ℝ)) (c := (5986234492864379537/5987500000000000000 : ℝ)) (alpha := (528555860771/479000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5986234492864379537/5987500000000000000 : ℝ)*(X 0 2+X 1 2)+(528555860771/479000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4485/1024 : ℝ)) (lo := (2693/25000 : ℝ)) (hi := (7781/50000 : ℝ)) (c := (5986234492864379537/5987500000000000000 : ℝ)) (alpha := (528555860771/479000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-473337091/2500000000 : ℝ)*X 0 0+(5435964739/10000000000 : ℝ)*X 0 1+(20376061/39062500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676326143/5000000000 : ℝ)*X 1 0+(-2005915323/10000000000 : ℝ)*X 1 1+(652034047/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070530503/2000000000 : ℝ)*X 2 0+(1043254329/2000000000 : ℝ)*X 2 1+(-2005915987/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4277706311/10000000000 : ℝ)*X 0 0+(2018850429/5000000000 : ℝ)*X 0 1+(4529907209/10000000000 : ℝ)*X 0 2+(4277706311/10000000000 : ℝ)*X 1 0+(2018850429/5000000000 : ℝ)*X 1 1+(4529907209/10000000000 : ℝ)*X 1 2+(4277706311/10000000000 : ℝ)*X 2 0+(2018850429/5000000000 : ℝ)*X 2 1+(4529907209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-946689507/5000000000 : ℝ)*X 0 0+(1304351063/2500000000 : ℝ)*X 0 1+(169838229/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((529513317/1000000000 : ℝ)*X 1 0+(-893682303/5000000000 : ℝ)*X 1 1+(169838229/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((529513317/1000000000 : ℝ)*X 2 0+(169838229/312500000 : ℝ)*X 2 1+(-893682303/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((427777463/1000000000 : ℝ)*X 0 0+(181094841/400000000 : ℝ)*X 0 1+(2020127419/5000000000 : ℝ)*X 0 2+(427777463/1000000000 : ℝ)*X 1 0+(181094841/400000000 : ℝ)*X 1 1+(2020127419/5000000000 : ℝ)*X 1 2+(427777463/1000000000 : ℝ)*X 2 0+(181094841/400000000 : ℝ)*X 2 1+(2020127419/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (688257246043787990411393763/149687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (148630463/100000000000000 : ℝ)*(base19) + (60432319/12500000000000 : ℝ)*(base23) + (100301821/100000000000000 : ℝ)*(lower4) + (31668699/12500000000000 : ℝ)*(lower5) + (3291759678954883/100000000000000 : ℝ)*(major0) + (3291759678954883/100000000000000 : ℝ)*(major1) + (3291759678954883/100000000000000 : ℝ)*(major2) + (1137957694041751/25000000000000 : ℝ)*(sp0) + (4551849709581247/100000000000000 : ℝ)*(sp1) + (56898062165237/1250000000000 : ℝ)*(sp2) + (406333522084829/20000000000000 : ℝ)*(sp3) + (9541022353/50000000000000 : ℝ)*(sp4) + (2200767099/50000000000000 : ℝ)*(sp6) + (1736008547/100000000000000 : ℝ)*(sp7) + (507917336608173/25000000000000 : ℝ)*(f.failure) + (455184985821171/10000000000000 : ℝ)*(f.sum) + (88915322853043/23950000000000000000000000000 : ℝ)*base65 + (3876255501762408329/598750000000000000000000000000000 : ℝ)*base68 + (4554754672799908329/598750000000000000000000000000000 : ℝ)*base70 + (4493075953580091671/598750000000000000000000000000000 : ℝ)*base71 + (32538933736007/23950000000000000000000000000 : ℝ)*base74 + (7491667035749908329/598750000000000000000000000000000 : ℝ)*base76 + (5536915457947408329/598750000000000000000000000000000 : ℝ)*base78 + (5341275969517408329/598750000000000000000000000000000 : ℝ)*base80 + (54336616188057/23950000000000000000000000000 : ℝ)*base82 + (3343319/625000000000000000000 : ℝ)*base89 + (3343319/625000000000000000000 : ℝ)*base91 + (3343319/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (878988683096853202942806537/74843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (482887717/25000000000000 : ℝ)*(base19) + (523931357/25000000000000 : ℝ)*(base23) + (242594703/100000000000000 : ℝ)*(upper3) + (74193719/100000000000000 : ℝ)*(lower4) + (241997277/100000000000000 : ℝ)*(upper5) + (1663077376745083/50000000000000 : ℝ)*(major0) + (1663077376745083/50000000000000 : ℝ)*(major1) + (1663077376745083/50000000000000 : ℝ)*(major2) + (2924683641/10000000000000 : ℝ)*(sp1) + (31461435209/100000000000000 : ℝ)*(sp2) + (2299705589231643/50000000000000 : ℝ)*(sp4) + (4599380000076007/100000000000000 : ℝ)*(sp5) + (4599377621302649/100000000000000 : ℝ)*(sp6) + (82115917481593/4000000000000 : ℝ)*(sp7) + (82115917481593/4000000000000 : ℝ)*(f.failure) + (2299705589231643/50000000000000 : ℝ)*(f.sum) + (27524741119357/11975000000000000000000000000 : ℝ)*base66 + (1632002553483604071/299375000000000000000000000000000 : ℝ)*base67 + (1162314175471729071/299375000000000000000000000000000 : ℝ)*base69 + (2902471466647979071/299375000000000000000000000000000 : ℝ)*base71 + (13430506100909/5987500000000000000000000000 : ℝ)*base73 + (4890620959601729071/299375000000000000000000000000000 : ℝ)*base75 + (851518451219854071/299375000000000000000000000000000 : ℝ)*base77 + (1075081695138270929/299375000000000000000000000000000 : ℝ)*base80 + (13868565021341/5987500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (134421/100000000000000000000 : ℝ)*base90 + (134421/100000000000000000000 : ℝ)*base92 + (134421/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1495_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40505603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7781/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2693/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10839/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1495_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1495_s5_0 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1893416693/10000000000 : ℝ)*x 0 + (5435512749/10000000000 : ℝ)*x 1 + (1304169627/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1893416693/10000000000 : ℝ)^4487 ≤ (5787617312767/50000000000000 : ℝ)^3463 := by
    have hnat : (1893416693 : ℕ)^4487*50000000000000^3463 ≤ 5787617312767^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893416693 10000000000 5787617312767 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435512749/10000000000 : ℝ)^4487 ≤ (11347281909147/25000000000000 : ℝ)^3463 := by
    have hnat : (5435512749 : ℕ)^4487*25000000000000^3463 ≤ 11347281909147^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435512749 10000000000 11347281909147 25000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304169627/2500000000 : ℝ)^4487 ≤ (43035637726493/100000000000000 : ℝ)^3463 := by
    have hnat : (1304169627 : ℕ)^4487*100000000000000^3463 ≤ 43035637726493^3463*2500000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304169627 2500000000 43035637726493 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1893416693/10000000000 : ℝ), (5435512749/10000000000 : ℝ), (1304169627/2500000000 : ℝ)] ![(5787617312767/50000000000000 : ℝ), (11347281909147/25000000000000 : ℝ), (43035637726493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1893416693/10000000000 : ℝ)|^4487 ≤ (5787617312767/50000000000000 : ℝ)^3463
        have hw : |(-1893416693/10000000000 : ℝ)|=(1893416693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435512749/10000000000 : ℝ)|^4487 ≤ (11347281909147/25000000000000 : ℝ)^3463
        have hw : |(5435512749/10000000000 : ℝ)|=(5435512749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304169627/2500000000 : ℝ)|^4487 ≤ (43035637726493/100000000000000 : ℝ)^3463
        have hw : |(1304169627/2500000000 : ℝ)|=(1304169627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s5_1 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352534709/10000000000 : ℝ)*x 0 + (-2005533667/10000000000 : ℝ)*x 1 + (5216678543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352534709/10000000000 : ℝ)^4487 ≤ (8898672896909/20000000000000 : ℝ)^3463 := by
    have hnat : (5352534709 : ℕ)^4487*20000000000000^3463 ≤ 8898672896909^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352534709 10000000000 8898672896909 20000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2005533667/10000000000 : ℝ)^4487 ≤ (2494199480361/20000000000000 : ℝ)^3463 := by
    have hnat : (2005533667 : ℕ)^4487*20000000000000^3463 ≤ 2494199480361^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005533667 10000000000 2494199480361 20000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216678543/10000000000 : ℝ)^4487 ≤ (43035638100609/100000000000000 : ℝ)^3463 := by
    have hnat : (5216678543 : ℕ)^4487*100000000000000^3463 ≤ 43035638100609^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216678543 10000000000 43035638100609 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352534709/10000000000 : ℝ), (-2005533667/10000000000 : ℝ), (5216678543/10000000000 : ℝ)] ![(8898672896909/20000000000000 : ℝ), (2494199480361/20000000000000 : ℝ), (43035638100609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352534709/10000000000 : ℝ)|^4487 ≤ (8898672896909/20000000000000 : ℝ)^3463
        have hw : |(5352534709/10000000000 : ℝ)|=(5352534709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2005533667/10000000000 : ℝ)|^4487 ≤ (2494199480361/20000000000000 : ℝ)^3463
        have hw : |(-2005533667/10000000000 : ℝ)|=(2005533667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216678543/10000000000 : ℝ)|^4487 ≤ (43035638100609/100000000000000 : ℝ)^3463
        have hw : |(5216678543/10000000000 : ℝ)|=(5216678543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s5_2 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676267369/5000000000 : ℝ)*x 0 + (5216678519/10000000000 : ℝ)*x 1 + (-2005533661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676267369/5000000000 : ℝ)^4487 ≤ (11123341199223/25000000000000 : ℝ)^3463 := by
    have hnat : (2676267369 : ℕ)^4487*25000000000000^3463 ≤ 11123341199223^3463*5000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676267369 5000000000 11123341199223 25000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216678519/10000000000 : ℝ)^4487 ≤ (5379454730509/12500000000000 : ℝ)^3463 := by
    have hnat : (5216678519 : ℕ)^4487*12500000000000^3463 ≤ 5379454730509^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216678519 10000000000 5379454730509 12500000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2005533661/10000000000 : ℝ)^4487 ≤ (12470997353463/100000000000000 : ℝ)^3463 := by
    have hnat : (2005533661 : ℕ)^4487*100000000000000^3463 ≤ 12470997353463^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005533661 10000000000 12470997353463 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676267369/5000000000 : ℝ), (5216678519/10000000000 : ℝ), (-2005533661/10000000000 : ℝ)] ![(11123341199223/25000000000000 : ℝ), (5379454730509/12500000000000 : ℝ), (12470997353463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676267369/5000000000 : ℝ)|^4487 ≤ (11123341199223/25000000000000 : ℝ)^3463
        have hw : |(2676267369/5000000000 : ℝ)|=(2676267369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216678519/10000000000 : ℝ)|^4487 ≤ (5379454730509/12500000000000 : ℝ)^3463
        have hw : |(5216678519/10000000000 : ℝ)|=(5216678519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2005533661/10000000000 : ℝ)|^4487 ≤ (12470997353463/100000000000000 : ℝ)^3463
        have hw : |(-2005533661/10000000000 : ℝ)|=(2005533661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s5_3 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4277749701/10000000000 : ℝ)*x 0 + (403865521/1000000000 : ℝ)*x 1 + (141529439/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4277749701/10000000000 : ℝ)^4487 ≤ (1039960262987/3125000000000 : ℝ)^3463 := by
    have hnat : (4277749701 : ℕ)^4487*3125000000000^3463 ≤ 1039960262987^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4277749701 10000000000 1039960262987 3125000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (403865521/1000000000 : ℝ)^4487 ≤ (3861108812399/12500000000000 : ℝ)^3463 := by
    have hnat : (403865521 : ℕ)^4487*12500000000000^3463 ≤ 3861108812399^3463*1000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403865521 1000000000 3861108812399 12500000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141529439/312500000 : ℝ)^4487 ≤ (17916200533327/50000000000000 : ℝ)^3463 := by
    have hnat : (141529439 : ℕ)^4487*50000000000000^3463 ≤ 17916200533327^3463*312500000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141529439 312500000 17916200533327 50000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4277749701/10000000000 : ℝ), (403865521/1000000000 : ℝ), (141529439/312500000 : ℝ)] ![(1039960262987/3125000000000 : ℝ), (3861108812399/12500000000000 : ℝ), (17916200533327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4277749701/10000000000 : ℝ)|^4487 ≤ (1039960262987/3125000000000 : ℝ)^3463
        have hw : |(4277749701/10000000000 : ℝ)|=(4277749701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(403865521/1000000000 : ℝ)|^4487 ≤ (3861108812399/12500000000000 : ℝ)^3463
        have hw : |(403865521/1000000000 : ℝ)|=(403865521/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(141529439/312500000 : ℝ)|^4487 ≤ (17916200533327/50000000000000 : ℝ)^3463
        have hw : |(141529439/312500000 : ℝ)|=(141529439/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s5_4 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1893446433/10000000000 : ℝ)*x 0 + (5217801629/10000000000 : ℝ)*x 1 + (5434381349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1893446433/10000000000 : ℝ)^4487 ≤ (2893867550127/25000000000000 : ℝ)^3463 := by
    have hnat : (1893446433 : ℕ)^4487*25000000000000^3463 ≤ 2893867550127^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893446433 10000000000 2893867550127 25000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217801629/10000000000 : ℝ)^4487 ≤ (43047643167521/100000000000000 : ℝ)^3463 := by
    have hnat : (5217801629 : ℕ)^4487*100000000000000^3463 ≤ 43047643167521^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217801629 10000000000 43047643167521 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434381349/10000000000 : ℝ)^4487 ≤ (9075377322777/20000000000000 : ℝ)^3463 := by
    have hnat : (5434381349 : ℕ)^4487*20000000000000^3463 ≤ 9075377322777^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434381349 10000000000 9075377322777 20000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1893446433/10000000000 : ℝ), (5217801629/10000000000 : ℝ), (5434381349/10000000000 : ℝ)] ![(2893867550127/25000000000000 : ℝ), (43047643167521/100000000000000 : ℝ), (9075377322777/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1893446433/10000000000 : ℝ)|^4487 ≤ (2893867550127/25000000000000 : ℝ)^3463
        have hw : |(-1893446433/10000000000 : ℝ)|=(1893446433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217801629/10000000000 : ℝ)|^4487 ≤ (43047643167521/100000000000000 : ℝ)^3463
        have hw : |(5217801629/10000000000 : ℝ)|=(5217801629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434381349/10000000000 : ℝ)|^4487 ≤ (9075377322777/20000000000000 : ℝ)^3463
        have hw : |(5434381349/10000000000 : ℝ)|=(5434381349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s5_5 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059048067/2000000000 : ℝ)*x 0 + (-27934861/156250000 : ℝ)*x 1 + (5434381201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059048067/2000000000 : ℝ)^4487 ≤ (43877249577301/100000000000000 : ℝ)^3463 := by
    have hnat : (1059048067 : ℕ)^4487*100000000000000^3463 ≤ 43877249577301^3463*2000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059048067 2000000000 43877249577301 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27934861/156250000 : ℝ)^4487 ≤ (10745865393101/100000000000000 : ℝ)^3463 := by
    have hnat : (27934861 : ℕ)^4487*100000000000000^3463 ≤ 10745865393101^3463*156250000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27934861 156250000 10745865393101 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434381201/10000000000 : ℝ)^4487 ≤ (4537688501267/10000000000000 : ℝ)^3463 := by
    have hnat : (5434381201 : ℕ)^4487*10000000000000^3463 ≤ 4537688501267^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434381201 10000000000 4537688501267 10000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059048067/2000000000 : ℝ), (-27934861/156250000 : ℝ), (5434381201/10000000000 : ℝ)] ![(43877249577301/100000000000000 : ℝ), (10745865393101/100000000000000 : ℝ), (4537688501267/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059048067/2000000000 : ℝ)|^4487 ≤ (43877249577301/100000000000000 : ℝ)^3463
        have hw : |(1059048067/2000000000 : ℝ)|=(1059048067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-27934861/156250000 : ℝ)|^4487 ≤ (10745865393101/100000000000000 : ℝ)^3463
        have hw : |(-27934861/156250000 : ℝ)|=(27934861/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434381201/10000000000 : ℝ)|^4487 ≤ (4537688501267/10000000000000 : ℝ)^3463
        have hw : |(5434381201/10000000000 : ℝ)|=(5434381201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s5_6 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295240193/10000000000 : ℝ)*x 0 + (1358595317/2500000000 : ℝ)*x 1 + (-1787831207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295240193/10000000000 : ℝ)^4487 ≤ (43877248052737/100000000000000 : ℝ)^3463 := by
    have hnat : (5295240193 : ℕ)^4487*100000000000000^3463 ≤ 43877248052737^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295240193 10000000000 43877248052737 100000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358595317/2500000000 : ℝ)^4487 ≤ (5672110717193/12500000000000 : ℝ)^3463 := by
    have hnat : (1358595317 : ℕ)^4487*12500000000000^3463 ≤ 5672110717193^3463*2500000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358595317 2500000000 5672110717193 12500000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1787831207/10000000000 : ℝ)^4487 ≤ (2686466548813/25000000000000 : ℝ)^3463 := by
    have hnat : (1787831207 : ℕ)^4487*25000000000000^3463 ≤ 2686466548813^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1787831207 10000000000 2686466548813 25000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295240193/10000000000 : ℝ), (1358595317/2500000000 : ℝ), (-1787831207/10000000000 : ℝ)] ![(43877248052737/100000000000000 : ℝ), (5672110717193/12500000000000 : ℝ), (2686466548813/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295240193/10000000000 : ℝ)|^4487 ≤ (43877248052737/100000000000000 : ℝ)^3463
        have hw : |(5295240193/10000000000 : ℝ)|=(5295240193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358595317/2500000000 : ℝ)|^4487 ≤ (5672110717193/12500000000000 : ℝ)^3463
        have hw : |(1358595317/2500000000 : ℝ)|=(1358595317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1787831207/10000000000 : ℝ)|^4487 ≤ (2686466548813/25000000000000 : ℝ)^3463
        have hw : |(-1787831207/10000000000 : ℝ)|=(1787831207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1495_s5_7 (p : ℝ) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4277816387/10000000000 : ℝ)*x 0 + (905285103/2000000000 : ℝ)*x 1 + (808238037/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4277816387/10000000000 : ℝ)^4487 ≤ (6655880120669/20000000000000 : ℝ)^3463 := by
    have hnat : (4277816387 : ℕ)^4487*20000000000000^3463 ≤ 6655880120669^3463*10000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4277816387 10000000000 6655880120669 20000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (905285103/2000000000 : ℝ)^4487 ≤ (8951651306731/25000000000000 : ℝ)^3463 := by
    have hnat : (905285103 : ℕ)^4487*25000000000000^3463 ≤ 8951651306731^3463*2000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905285103 2000000000 8951651306731 25000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (808238037/2000000000 : ℝ)^4487 ≤ (7728498538301/25000000000000 : ℝ)^3463 := by
    have hnat : (808238037 : ℕ)^4487*25000000000000^3463 ≤ 7728498538301^3463*2000000000^4487 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808238037 2000000000 7728498538301 25000000000000 4487 3463 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4487/1024 : ℝ)) 4487 3463 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4277816387/10000000000 : ℝ), (905285103/2000000000 : ℝ), (808238037/2000000000 : ℝ)] ![(6655880120669/20000000000000 : ℝ), (8951651306731/25000000000000 : ℝ), (7728498538301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4277816387/10000000000 : ℝ)|^4487 ≤ (6655880120669/20000000000000 : ℝ)^3463
        have hw : |(4277816387/10000000000 : ℝ)|=(4277816387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(905285103/2000000000 : ℝ)|^4487 ≤ (8951651306731/25000000000000 : ℝ)^3463
        have hw : |(905285103/2000000000 : ℝ)|=(905285103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(808238037/2000000000 : ℝ)|^4487 ≤ (7728498538301/25000000000000 : ℝ)^3463
        have hw : |(808238037/2000000000 : ℝ)|=(808238037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1495_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40505603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10839/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10847/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (387/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10839/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10839/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10839/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10839/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10839/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10839/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10839/100000 : ℝ) ^ (4485/1024 : ℝ) ≤ (1483562554919137/25000000000000000000 : ℝ) := by
    have hpowers : (10839/100000 : ℝ)^4485 ≤ (1483562554919137/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10839 : ℕ)^4485*25000000000000000000^1024 ≤ 1483562554919137^1024*100000^4485 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10839 100000 1483562554919137 25000000000000000000 4485 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10839/100000 : ℝ)) (X := (1483562554919137/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4485/1024 : ℝ) ≤ (28347849971796939/100000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4485 ≤ (28347849971796939/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4485*100000000000000000000^1024 ≤ 28347849971796939^1024*10000^4485 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 28347849971796939 100000000000000000000 4485 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (28347849971796939/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501483562554919137/12500000000000000000 : ℝ) ≤ (10000270965171533/10000000000000000 : ℝ) ^ (4485/1024 : ℝ) := by
    have hpowers : (12501483562554919137/12500000000000000000 : ℝ)^1024 ≤ (10000270965171533/10000000000000000 : ℝ)^4485 := by
      have hnat : (12501483562554919137 : ℕ)^1024*10000000000000000^4485 ≤ 10000270965171533^4485*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501483562554919137 12500000000000000000 10000270965171533 10000000000000000 1024 4485 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000270965171533/10000000000000000 : ℝ)) (X := (12501483562554919137/12500000000000000000 : ℝ)) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034282100191473487/100000000000000000000 : ℝ) ≤ (10000782613780423/10000000000000000 : ℝ) ^ (4485/1024 : ℝ) := by
    have hpowers : (100034282100191473487/100000000000000000000 : ℝ)^1024 ≤ (10000782613780423/10000000000000000 : ℝ)^4485 := by
      have hnat : (100034282100191473487 : ℕ)^1024*10000000000000000^4485 ≤ 10000782613780423^4485*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034282100191473487 100000000000000000000 10000782613780423 10000000000000000 1024 4485 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000782613780423/10000000000000000 : ℝ)) (X := (100034282100191473487/100000000000000000000 : ℝ)) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028347849971796939/50000000000000000000 : ℝ) ≤ (10001294262389313/10000000000000000 : ℝ) ^ (4485/1024 : ℝ) := by
    have hpowers : (50028347849971796939/50000000000000000000 : ℝ)^1024 ≤ (10001294262389313/10000000000000000 : ℝ)^4485 := by
      have hnat : (50028347849971796939 : ℕ)^1024*10000000000000000^4485 ≤ 10001294262389313^4485*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028347849971796939 50000000000000000000 10001294262389313 10000000000000000 1024 4485 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001294262389313/10000000000000000 : ℝ)) (X := (50028347849971796939/50000000000000000000 : ℝ)) (by norm_num) 4485 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1483562554919137/25000000000000000000 : ℝ) ≤ ((46500168740469282563/46510000000000000000 : ℝ)+2*(51164860889/46510000000000 : ℝ)*(10839/100000 : ℝ))^(4485/1024 : ℝ) := by
    rw [show (46500168740469282563/46510000000000000000 : ℝ)+2*(51164860889/46510000000000 : ℝ)*(10839/100000 : ℝ)=(10000270965171533/10000000000000000 : ℝ) by norm_num, show 1+2*(1483562554919137/25000000000000000000 : ℝ)=(12501483562554919137/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28347849971796939/100000000000000000000 : ℝ)+(1483562554919137/25000000000000000000 : ℝ) ≤ ((46500168740469282563/46510000000000000000 : ℝ)+(51164860889/46510000000000 : ℝ)*((1549/10000 : ℝ)+(10839/100000 : ℝ)))^(4485/1024 : ℝ) := by
    rw [show (46500168740469282563/46510000000000000000 : ℝ)+(51164860889/46510000000000 : ℝ)*((1549/10000 : ℝ)+(10839/100000 : ℝ))=(10000782613780423/10000000000000000 : ℝ) by norm_num, show 1+(28347849971796939/100000000000000000000 : ℝ)+(1483562554919137/25000000000000000000 : ℝ)=(100034282100191473487/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28347849971796939/100000000000000000000 : ℝ) ≤ ((46500168740469282563/46510000000000000000 : ℝ)+2*(51164860889/46510000000000 : ℝ)*(1549/10000 : ℝ))^(4485/1024 : ℝ) := by
    rw [show (46500168740469282563/46510000000000000000 : ℝ)+2*(51164860889/46510000000000 : ℝ)*(1549/10000 : ℝ)=(10001294262389313/10000000000000000 : ℝ) by norm_num, show 1+2*(28347849971796939/100000000000000000000 : ℝ)=(50028347849971796939/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46500168740469282563/46510000000000000000 : ℝ)*(X 1 0+X 2 0)+(51164860889/46510000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4485/1024 : ℝ)) (lo := (10839/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (46500168740469282563/46510000000000000000 : ℝ)) (alpha := (51164860889/46510000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46500168740469282563/46510000000000000000 : ℝ)*(X 0 1+X 2 1)+(51164860889/46510000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4485/1024 : ℝ)) (lo := (10839/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (46500168740469282563/46510000000000000000 : ℝ)) (alpha := (51164860889/46510000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46500168740469282563/46510000000000000000 : ℝ)*(X 0 2+X 1 2)+(51164860889/46510000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4485/1024 : ℝ)) (lo := (10839/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (46500168740469282563/46510000000000000000 : ℝ)) (alpha := (51164860889/46510000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1893416693/10000000000 : ℝ)*X 0 0+(5435512749/10000000000 : ℝ)*X 0 1+(1304169627/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352534709/10000000000 : ℝ)*X 1 0+(-2005533667/10000000000 : ℝ)*X 1 1+(5216678543/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676267369/5000000000 : ℝ)*X 2 0+(5216678519/10000000000 : ℝ)*X 2 1+(-2005533661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4277749701/10000000000 : ℝ)*X 0 0+(403865521/1000000000 : ℝ)*X 0 1+(141529439/312500000 : ℝ)*X 0 2+(4277749701/10000000000 : ℝ)*X 1 0+(403865521/1000000000 : ℝ)*X 1 1+(141529439/312500000 : ℝ)*X 1 2+(4277749701/10000000000 : ℝ)*X 2 0+(403865521/1000000000 : ℝ)*X 2 1+(141529439/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1893446433/10000000000 : ℝ)*X 0 0+(5217801629/10000000000 : ℝ)*X 0 1+(5434381349/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1059048067/2000000000 : ℝ)*X 1 0+(-27934861/156250000 : ℝ)*X 1 1+(5434381201/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295240193/10000000000 : ℝ)*X 2 0+(1358595317/2500000000 : ℝ)*X 2 1+(-1787831207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4277816387/10000000000 : ℝ)*X 0 0+(905285103/2000000000 : ℝ)*X 0 1+(808238037/2000000000 : ℝ)*X 0 2+(4277816387/10000000000 : ℝ)*X 1 0+(905285103/2000000000 : ℝ)*X 1 1+(808238037/2000000000 : ℝ)*X 1 2+(4277816387/10000000000 : ℝ)*X 2 0+(905285103/2000000000 : ℝ)*X 2 1+(808238037/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1495_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3114983326476336107878176381/290687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1841525949/100000000000000 : ℝ)*(base19) + (218300211/12500000000000 : ℝ)*(base23) + (64167799/100000000000000 : ℝ)*(lower2) + (255873471/100000000000000 : ℝ)*(upper3) + (44488767/25000000000000 : ℝ)*(upper5) + (826172251616871/25000000000000 : ℝ)*(major0) + (826172251616871/25000000000000 : ℝ)*(major1) + (826172251616871/25000000000000 : ℝ)*(major2) + (913939780794209/20000000000000 : ℝ)*(sp0) + (456972650540657/10000000000000 : ℝ)*(sp1) + (4569726600530831/100000000000000 : ℝ)*(sp2) + (2039635135810541/100000000000000 : ℝ)*(sp3) + (14721480737/50000000000000 : ℝ)*(sp4) + (177162433/1250000000000 : ℝ)*(sp7) + (2039649308805181/100000000000000 : ℝ)*(f.failure) + (4569728346932519/100000000000000 : ℝ)*(f.sum) + (4107942315979/2325500000000000000000000000 : ℝ)*base65 + (6167507673008170373/1162750000000000000000000000000000 : ℝ)*base67 + (12112202400247420373/1162750000000000000000000000000000 : ℝ)*base69 + (1335136690364329627/1162750000000000000000000000000000 : ℝ)*base72 + (4075262589383/1162750000000000000000000000 : ℝ)*base73 + (3655198145291420373/1162750000000000000000000000000000 : ℝ)*base75 + (10192518957798670373/1162750000000000000000000000000000 : ℝ)*base77 + (10086992069973670373/1162750000000000000000000000000000 : ℝ)*base79 + (446557474977/186040000000000000000000000 : ℝ)*base81 + (34070857/2500000000000000000000 : ℝ)*base90 + (34070857/2500000000000000000000 : ℝ)*base92 + (34070857/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1824673626969162641859572589/290687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (157912853/20000000000000 : ℝ)*(base19) + (728055111/100000000000000 : ℝ)*(base23) + (64262133/50000000000000 : ℝ)*(lower1) + (54331091/50000000000000 : ℝ)*(upper3) + (23729617/50000000000000 : ℝ)*(lower4) + (20842453/12500000000000 : ℝ)*(upper5) + (417380222101367/12500000000000 : ℝ)*(major0) + (417380222101367/12500000000000 : ℝ)*(major1) + (417380222101367/12500000000000 : ℝ)*(major2) + (2524703659/100000000000000 : ℝ)*(sp1) + (4617231555059429/100000000000000 : ℝ)*(sp4) + (923445648158301/20000000000000 : ℝ)*(sp5) + (2308615413502159/50000000000000 : ℝ)*(sp6) + (128803236832867/6250000000000 : ℝ)*(sp7) + (128803236832867/6250000000000 : ℝ)*(f.failure) + (4617231555059429/100000000000000 : ℝ)*(f.sum) + (20089423171049/4651000000000000000000000000 : ℝ)*base66 + (7550722216806811379/581375000000000000000000000000000 : ℝ)*base68 + (2791192364321811379/581375000000000000000000000000000 : ℝ)*base70 + (1504297191531686379/581375000000000000000000000000000 : ℝ)*base72 + (30081014383349/4651000000000000000000000000 : ℝ)*base74 + (5074366299855686379/581375000000000000000000000000000 : ℝ)*base76 + (1574061591552686379/581375000000000000000000000000000 : ℝ)*base78 + (3170820508848436379/581375000000000000000000000000000 : ℝ)*base80 + (31175776307/2325500000000000000000000000 : ℝ)*base81 + (553801/156250000000000000000 : ℝ)*base89 + (553801/156250000000000000000 : ℝ)*base91 + (553801/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1495_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40505603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10839/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10847/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (387/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1495_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1495_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40505603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3213/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1031/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10847/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (387/2500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1495_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1495_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1495_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4485/1024 : ℝ) ≤ p) (hpb : p ≤ (4487/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40505603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3213/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1031/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10847/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (387/2500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1495_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
