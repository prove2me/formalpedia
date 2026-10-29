-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1469_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:10:12.423286+00:00
-- url     : https://prove2.me/submissions/1b4c328b-db7d-4c46-8d18-ced3d32730a3

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
theorem support_rectangle_w1469_s6_0 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-483365771/2500000000 : ℝ)*x 0 + (5438883547/10000000000 : ℝ)*x 1 + (5215153761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (483365771/2500000000 : ℝ)^4435 ≤ (5902828929383/50000000000000 : ℝ)^3411 := by
    have hnat : (483365771 : ℕ)^4435*50000000000000^3411 ≤ 5902828929383^3411*2500000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483365771 2500000000 5902828929383 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438883547/10000000000 : ℝ)^4435 ≤ (22650532385347/50000000000000 : ℝ)^3411 := by
    have hnat : (5438883547 : ℕ)^4435*50000000000000^3411 ≤ 22650532385347^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438883547 10000000000 22650532385347 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215153761/10000000000 : ℝ)^4435 ≤ (10723319338581/25000000000000 : ℝ)^3411 := by
    have hnat : (5215153761 : ℕ)^4435*25000000000000^3411 ≤ 10723319338581^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215153761 10000000000 10723319338581 25000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-483365771/2500000000 : ℝ), (5438883547/10000000000 : ℝ), (5215153761/10000000000 : ℝ)] ![(5902828929383/50000000000000 : ℝ), (22650532385347/50000000000000 : ℝ), (10723319338581/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-483365771/2500000000 : ℝ)|^4435 ≤ (5902828929383/50000000000000 : ℝ)^3411
        have hw : |(-483365771/2500000000 : ℝ)|=(483365771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438883547/10000000000 : ℝ)|^4435 ≤ (22650532385347/50000000000000 : ℝ)^3411
        have hw : |(5438883547/10000000000 : ℝ)|=(5438883547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215153761/10000000000 : ℝ)|^4435 ≤ (10723319338581/25000000000000 : ℝ)^3411
        have hw : |(5215153761/10000000000 : ℝ)|=(5215153761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s6_1 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214154723/400000000 : ℝ)*x 0 + (-102407587/500000000 : ℝ)*x 1 + (1303788437/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214154723/400000000 : ℝ)^4435 ≤ (88765106491/200000000000 : ℝ)^3411 := by
    have hnat : (214154723 : ℕ)^4435*200000000000^3411 ≤ 88765106491^3411*400000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214154723 400000000 88765106491 200000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (102407587/500000000 : ℝ)^4435 ≤ (12724169513929/100000000000000 : ℝ)^3411 := by
    have hnat : (102407587 : ℕ)^4435*100000000000000^3411 ≤ 12724169513929^3411*500000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102407587 500000000 12724169513929 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303788437/2500000000 : ℝ)^4435 ≤ (5361659651913/12500000000000 : ℝ)^3411 := by
    have hnat : (1303788437 : ℕ)^4435*12500000000000^3411 ≤ 5361659651913^3411*2500000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303788437 2500000000 5361659651913 12500000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214154723/400000000 : ℝ), (-102407587/500000000 : ℝ), (1303788437/2500000000 : ℝ)] ![(88765106491/200000000000 : ℝ), (12724169513929/100000000000000 : ℝ), (5361659651913/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214154723/400000000 : ℝ)|^4435 ≤ (88765106491/200000000000 : ℝ)^3411
        have hw : |(214154723/400000000 : ℝ)|=(214154723/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-102407587/500000000 : ℝ)|^4435 ≤ (12724169513929/100000000000000 : ℝ)^3411
        have hw : |(-102407587/500000000 : ℝ)|=(102407587/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303788437/2500000000 : ℝ)|^4435 ≤ (5361659651913/12500000000000 : ℝ)^3411
        have hw : |(1303788437/2500000000 : ℝ)|=(1303788437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s6_2 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535386863/1000000000 : ℝ)*x 0 + (2607576771/5000000000 : ℝ)*x 1 + (-1024075637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535386863/1000000000 : ℝ)^4435 ≤ (44382559227543/100000000000000 : ℝ)^3411 := by
    have hnat : (535386863 : ℕ)^4435*100000000000000^3411 ≤ 44382559227543^3411*1000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535386863 1000000000 44382559227543 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607576771/5000000000 : ℝ)^4435 ≤ (42893275012371/100000000000000 : ℝ)^3411 := by
    have hnat : (2607576771 : ℕ)^4435*100000000000000^3411 ≤ 42893275012371^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607576771 5000000000 42893275012371 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1024075637/5000000000 : ℝ)^4435 ≤ (2544833149959/20000000000000 : ℝ)^3411 := by
    have hnat : (1024075637 : ℕ)^4435*20000000000000^3411 ≤ 2544833149959^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024075637 5000000000 2544833149959 20000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535386863/1000000000 : ℝ), (2607576771/5000000000 : ℝ), (-1024075637/5000000000 : ℝ)] ![(44382559227543/100000000000000 : ℝ), (42893275012371/100000000000000 : ℝ), (2544833149959/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535386863/1000000000 : ℝ)|^4435 ≤ (44382559227543/100000000000000 : ℝ)^3411
        have hw : |(535386863/1000000000 : ℝ)|=(535386863/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607576771/5000000000 : ℝ)|^4435 ≤ (42893275012371/100000000000000 : ℝ)^3411
        have hw : |(2607576771/5000000000 : ℝ)|=(2607576771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1024075637/5000000000 : ℝ)|^4435 ≤ (2544833149959/20000000000000 : ℝ)^3411
        have hw : |(-1024075637/5000000000 : ℝ)|=(1024075637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s6_3 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2145113113/5000000000 : ℝ)*x 0 + (2025219221/5000000000 : ℝ)*x 1 + (4542430891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145113113/5000000000 : ℝ)^4435 ≤ (16638678641903/50000000000000 : ℝ)^3411 := by
    have hnat : (2145113113 : ℕ)^4435*50000000000000^3411 ≤ 16638678641903^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145113113 5000000000 16638678641903 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2025219221/5000000000 : ℝ)^4435 ≤ (15439815401423/50000000000000 : ℝ)^3411 := by
    have hnat : (2025219221 : ℕ)^4435*50000000000000^3411 ≤ 15439815401423^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025219221 5000000000 15439815401423 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4542430891/10000000000 : ℝ)^4435 ≤ (7168602380731/20000000000000 : ℝ)^3411 := by
    have hnat : (4542430891 : ℕ)^4435*20000000000000^3411 ≤ 7168602380731^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4542430891 10000000000 7168602380731 20000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2145113113/5000000000 : ℝ), (2025219221/5000000000 : ℝ), (4542430891/10000000000 : ℝ)] ![(16638678641903/50000000000000 : ℝ), (15439815401423/50000000000000 : ℝ), (7168602380731/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2145113113/5000000000 : ℝ)|^4435 ≤ (16638678641903/50000000000000 : ℝ)^3411
        have hw : |(2145113113/5000000000 : ℝ)|=(2145113113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2025219221/5000000000 : ℝ)|^4435 ≤ (15439815401423/50000000000000 : ℝ)^3411
        have hw : |(2025219221/5000000000 : ℝ)|=(2025219221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4542430891/10000000000 : ℝ)|^4435 ≤ (7168602380731/20000000000000 : ℝ)^3411
        have hw : |(4542430891/10000000000 : ℝ)|=(4542430891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s6_4 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1933494037/10000000000 : ℝ)*x 0 + (5216295859/10000000000 : ℝ)*x 1 + (1359433249/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1933494037/10000000000 : ℝ)^4435 ≤ (184467243679/1562500000000 : ℝ)^3411 := by
    have hnat : (1933494037 : ℕ)^4435*1562500000000^3411 ≤ 184467243679^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933494037 10000000000 184467243679 1562500000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216295859/10000000000 : ℝ)^4435 ≤ (42905491178509/100000000000000 : ℝ)^3411 := by
    have hnat : (5216295859 : ℕ)^4435*100000000000000^3411 ≤ 42905491178509^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216295859 10000000000 42905491178509 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359433249/2500000000 : ℝ)^4435 ≤ (5661075651581/12500000000000 : ℝ)^3411 := by
    have hnat : (1359433249 : ℕ)^4435*12500000000000^3411 ≤ 5661075651581^3411*2500000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359433249 2500000000 5661075651581 12500000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1933494037/10000000000 : ℝ), (5216295859/10000000000 : ℝ), (1359433249/2500000000 : ℝ)] ![(184467243679/1562500000000 : ℝ), (42905491178509/100000000000000 : ℝ), (5661075651581/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1933494037/10000000000 : ℝ)|^4435 ≤ (184467243679/1562500000000 : ℝ)^3411
        have hw : |(-1933494037/10000000000 : ℝ)|=(1933494037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216295859/10000000000 : ℝ)|^4435 ≤ (42905491178509/100000000000000 : ℝ)^3411
        have hw : |(5216295859/10000000000 : ℝ)|=(5216295859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359433249/2500000000 : ℝ)|^4435 ≤ (5661075651581/12500000000000 : ℝ)^3411
        have hw : |(1359433249/2500000000 : ℝ)|=(1359433249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s6_5 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647775437/5000000000 : ℝ)*x 0 + (-5704913/31250000 : ℝ)*x 1 + (2718866471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647775437/5000000000 : ℝ)^4435 ≤ (875100284773/2000000000000 : ℝ)^3411 := by
    have hnat : (2647775437 : ℕ)^4435*2000000000000^3411 ≤ 875100284773^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647775437 5000000000 875100284773 2000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5704913/31250000 : ℝ)^4435 ≤ (5478190559683/50000000000000 : ℝ)^3411 := by
    have hnat : (5704913 : ℕ)^4435*50000000000000^3411 ≤ 5478190559683^3411*31250000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5704913 31250000 5478190559683 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718866471/5000000000 : ℝ)^4435 ≤ (45288604627889/100000000000000 : ℝ)^3411 := by
    have hnat : (2718866471 : ℕ)^4435*100000000000000^3411 ≤ 45288604627889^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718866471 5000000000 45288604627889 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647775437/5000000000 : ℝ), (-5704913/31250000 : ℝ), (2718866471/5000000000 : ℝ)] ![(875100284773/2000000000000 : ℝ), (5478190559683/50000000000000 : ℝ), (45288604627889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647775437/5000000000 : ℝ)|^4435 ≤ (875100284773/2000000000000 : ℝ)^3411
        have hw : |(2647775437/5000000000 : ℝ)|=(2647775437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5704913/31250000 : ℝ)|^4435 ≤ (5478190559683/50000000000000 : ℝ)^3411
        have hw : |(-5704913/31250000 : ℝ)|=(5704913/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718866471/5000000000 : ℝ)|^4435 ≤ (45288604627889/100000000000000 : ℝ)^3411
        have hw : |(2718866471/5000000000 : ℝ)|=(2718866471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s6_6 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059110179/2000000000 : ℝ)*x 0 + (2718866481/5000000000 : ℝ)*x 1 + (-228196513/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059110179/2000000000 : ℝ)^4435 ≤ (21877507232127/50000000000000 : ℝ)^3411 := by
    have hnat : (1059110179 : ℕ)^4435*50000000000000^3411 ≤ 21877507232127^3411*2000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059110179 2000000000 21877507232127 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718866481/5000000000 : ℝ)^4435 ≤ (22644302422233/50000000000000 : ℝ)^3411 := by
    have hnat : (2718866481 : ℕ)^4435*50000000000000^3411 ≤ 22644302422233^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718866481 5000000000 22644302422233 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (228196513/1250000000 : ℝ)^4435 ≤ (547819034119/5000000000000 : ℝ)^3411 := by
    have hnat : (228196513 : ℕ)^4435*5000000000000^3411 ≤ 547819034119^3411*1250000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228196513 1250000000 547819034119 5000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059110179/2000000000 : ℝ), (2718866481/5000000000 : ℝ), (-228196513/1250000000 : ℝ)] ![(21877507232127/50000000000000 : ℝ), (22644302422233/50000000000000 : ℝ), (547819034119/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059110179/2000000000 : ℝ)|^4435 ≤ (21877507232127/50000000000000 : ℝ)^3411
        have hw : |(1059110179/2000000000 : ℝ)|=(1059110179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718866481/5000000000 : ℝ)|^4435 ≤ (22644302422233/50000000000000 : ℝ)^3411
        have hw : |(2718866481/5000000000 : ℝ)|=(2718866481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-228196513/1250000000 : ℝ)|^4435 ≤ (547819034119/5000000000000 : ℝ)^3411
        have hw : |(-228196513/1250000000 : ℝ)|=(228196513/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s6_7 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107257357/250000000 : ℝ)*x 0 + (453991947/1000000000 : ℝ)*x 1 + (506621013/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107257357/250000000 : ℝ)^4435 ≤ (415975545217/1250000000000 : ℝ)^3411 := by
    have hnat : (107257357 : ℕ)^4435*1250000000000^3411 ≤ 415975545217^3411*250000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107257357 250000000 415975545217 1250000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (453991947/1000000000 : ℝ)^4435 ≤ (17908624003563/50000000000000 : ℝ)^3411 := by
    have hnat : (453991947 : ℕ)^4435*50000000000000^3411 ≤ 17908624003563^3411*1000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453991947 1000000000 17908624003563 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (506621013/1250000000 : ℝ)^4435 ≤ (15452354178297/50000000000000 : ℝ)^3411 := by
    have hnat : (506621013 : ℕ)^4435*50000000000000^3411 ≤ 15452354178297^3411*1250000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506621013 1250000000 15452354178297 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107257357/250000000 : ℝ), (453991947/1000000000 : ℝ), (506621013/1250000000 : ℝ)] ![(415975545217/1250000000000 : ℝ), (17908624003563/50000000000000 : ℝ), (15452354178297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107257357/250000000 : ℝ)|^4435 ≤ (415975545217/1250000000000 : ℝ)^3411
        have hw : |(107257357/250000000 : ℝ)|=(107257357/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(453991947/1000000000 : ℝ)|^4435 ≤ (17908624003563/50000000000000 : ℝ)^3411
        have hw : |(453991947/1000000000 : ℝ)|=(453991947/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(506621013/1250000000 : ℝ)|^4435 ≤ (15452354178297/50000000000000 : ℝ)^3411
        have hw : |(506621013/1250000000 : ℝ)|=(506621013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1469_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79976261/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10737/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5369/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (967/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7737/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10737/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7737/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10737/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7737/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10737/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7737/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10737/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7737/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10737/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7737/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10737/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10737/100000 : ℝ) ^ (4433/1024 : ℝ) ≤ (6376669056354987/100000000000000000000 : ℝ) := by
    have hpowers : (10737/100000 : ℝ)^4433 ≤ (6376669056354987/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10737 : ℕ)^4433*100000000000000000000^1024 ≤ 6376669056354987^1024*100000^4433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10737 100000 6376669056354987 100000000000000000000 4433 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10737/100000 : ℝ)) (X := (6376669056354987/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7737/50000 : ℝ) ^ (4433/1024 : ℝ) ≤ (3878085056425677/12500000000000000000 : ℝ) := by
    have hpowers : (7737/50000 : ℝ)^4433 ≤ (3878085056425677/12500000000000000000 : ℝ)^1024 := by
      have hnat : (7737 : ℕ)^4433*12500000000000000000^1024 ≤ 3878085056425677^1024*50000^4433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7737 50000 3878085056425677 12500000000000000000 4433 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7737/50000 : ℝ)) (X := (3878085056425677/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006376669056354987/50000000000000000000 : ℝ) ≤ (2000058916209709/2000000000000000 : ℝ) ^ (4433/1024 : ℝ) := by
    have hpowers : (50006376669056354987/50000000000000000000 : ℝ)^1024 ≤ (2000058916209709/2000000000000000 : ℝ)^4433 := by
      have hnat : (50006376669056354987 : ℕ)^1024*2000000000000000^4433 ≤ 2000058916209709^4433*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006376669056354987 50000000000000000000 2000058916209709 2000000000000000 1024 4433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000058916209709/2000000000000000 : ℝ)) (X := (50006376669056354987/50000000000000000000 : ℝ)) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037401349507760403/100000000000000000000 : ℝ) ≤ (31252699461099/31250000000000 : ℝ) ^ (4433/1024 : ℝ) := by
    have hpowers : (100037401349507760403/100000000000000000000 : ℝ)^1024 ≤ (31252699461099/31250000000000 : ℝ)^4433 := by
      have hnat : (100037401349507760403 : ℕ)^1024*31250000000000^4433 ≤ 31252699461099^4433*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037401349507760403 100000000000000000000 31252699461099 31250000000000 1024 4433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31252699461099/31250000000000 : ℝ)) (X := (100037401349507760403/100000000000000000000 : ℝ)) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253878085056425677/6250000000000000000 : ℝ) ≤ (2000286614810963/2000000000000000 : ℝ) ^ (4433/1024 : ℝ) := by
    have hpowers : (6253878085056425677/6250000000000000000 : ℝ)^1024 ≤ (2000286614810963/2000000000000000 : ℝ)^4433 := by
      have hnat : (6253878085056425677 : ℕ)^1024*2000000000000000^4433 ≤ 2000286614810963^4433*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253878085056425677 6250000000000000000 2000286614810963 2000000000000000 1024 4433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000286614810963/2000000000000000 : ℝ)) (X := (6253878085056425677/6250000000000000000 : ℝ)) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6376669056354987/100000000000000000000 : ℝ) ≤ ((631455619080248489/631600000000000000 : ℝ)+2*(113849300627/94740000000000 : ℝ)*(10737/100000 : ℝ))^(4433/1024 : ℝ) := by
    rw [show (631455619080248489/631600000000000000 : ℝ)+2*(113849300627/94740000000000 : ℝ)*(10737/100000 : ℝ)=(2000058916209709/2000000000000000 : ℝ) by norm_num, show 1+2*(6376669056354987/100000000000000000000 : ℝ)=(50006376669056354987/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3878085056425677/12500000000000000000 : ℝ)+(6376669056354987/100000000000000000000 : ℝ) ≤ ((631455619080248489/631600000000000000 : ℝ)+(113849300627/94740000000000 : ℝ)*((7737/50000 : ℝ)+(10737/100000 : ℝ)))^(4433/1024 : ℝ) := by
    rw [show (631455619080248489/631600000000000000 : ℝ)+(113849300627/94740000000000 : ℝ)*((7737/50000 : ℝ)+(10737/100000 : ℝ))=(31252699461099/31250000000000 : ℝ) by norm_num, show 1+(3878085056425677/12500000000000000000 : ℝ)+(6376669056354987/100000000000000000000 : ℝ)=(100037401349507760403/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3878085056425677/12500000000000000000 : ℝ) ≤ ((631455619080248489/631600000000000000 : ℝ)+2*(113849300627/94740000000000 : ℝ)*(7737/50000 : ℝ))^(4433/1024 : ℝ) := by
    rw [show (631455619080248489/631600000000000000 : ℝ)+2*(113849300627/94740000000000 : ℝ)*(7737/50000 : ℝ)=(2000286614810963/2000000000000000 : ℝ) by norm_num, show 1+2*(3878085056425677/12500000000000000000 : ℝ)=(6253878085056425677/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (631455619080248489/631600000000000000 : ℝ)*(X 1 0+X 2 0)+(113849300627/94740000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4433/1024 : ℝ)) (lo := (10737/100000 : ℝ)) (hi := (7737/50000 : ℝ)) (c := (631455619080248489/631600000000000000 : ℝ)) (alpha := (113849300627/94740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (631455619080248489/631600000000000000 : ℝ)*(X 0 1+X 2 1)+(113849300627/94740000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4433/1024 : ℝ)) (lo := (10737/100000 : ℝ)) (hi := (7737/50000 : ℝ)) (c := (631455619080248489/631600000000000000 : ℝ)) (alpha := (113849300627/94740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (631455619080248489/631600000000000000 : ℝ)*(X 0 2+X 1 2)+(113849300627/94740000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4433/1024 : ℝ)) (lo := (10737/100000 : ℝ)) (hi := (7737/50000 : ℝ)) (c := (631455619080248489/631600000000000000 : ℝ)) (alpha := (113849300627/94740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-483365771/2500000000 : ℝ)*X 0 0+(5438883547/10000000000 : ℝ)*X 0 1+(5215153761/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((214154723/400000000 : ℝ)*X 1 0+(-102407587/500000000 : ℝ)*X 1 1+(1303788437/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535386863/1000000000 : ℝ)*X 2 0+(2607576771/5000000000 : ℝ)*X 2 1+(-1024075637/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2145113113/5000000000 : ℝ)*X 0 0+(2025219221/5000000000 : ℝ)*X 0 1+(4542430891/10000000000 : ℝ)*X 0 2+(2145113113/5000000000 : ℝ)*X 1 0+(2025219221/5000000000 : ℝ)*X 1 1+(4542430891/10000000000 : ℝ)*X 1 2+(2145113113/5000000000 : ℝ)*X 2 0+(2025219221/5000000000 : ℝ)*X 2 1+(4542430891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1933494037/10000000000 : ℝ)*X 0 0+(5216295859/10000000000 : ℝ)*X 0 1+(1359433249/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647775437/5000000000 : ℝ)*X 1 0+(-5704913/31250000 : ℝ)*X 1 1+(2718866471/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1059110179/2000000000 : ℝ)*X 2 0+(2718866481/5000000000 : ℝ)*X 2 1+(-228196513/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((107257357/250000000 : ℝ)*X 0 0+(453991947/1000000000 : ℝ)*X 0 1+(506621013/1250000000 : ℝ)*X 0 2+(107257357/250000000 : ℝ)*X 1 0+(453991947/1000000000 : ℝ)*X 1 1+(506621013/1250000000 : ℝ)*X 1 2+(107257357/250000000 : ℝ)*X 2 0+(453991947/1000000000 : ℝ)*X 2 1+(506621013/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8936047960623448038013311/789500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (162156817/10000000000000 : ℝ)*(base19) + (915644963/50000000000000 : ℝ)*(base23) + (4243361/3125000000000 : ℝ)*(lower2) + (11425123/25000000000000 : ℝ)*(upper3) + (92493441/25000000000000 : ℝ)*(upper5) + (81278758038411/2500000000000 : ℝ)*(major0) + (81278758038411/2500000000000 : ℝ)*(major1) + (81278758038411/2500000000000 : ℝ)*(major2) + (139677988420511/3125000000000 : ℝ)*(sp0) + (4469726552896247/100000000000000 : ℝ)*(sp1) + (1117431585793623/25000000000000 : ℝ)*(sp2) + (1016281249328191/50000000000000 : ℝ)*(sp3) + (16272504033/50000000000000 : ℝ)*(sp4) + (4796332421/50000000000000 : ℝ)*(sp7) + (254071511415153/12500000000000 : ℝ)*(f.failure) + (4469728174464417/100000000000000 : ℝ)*(f.sum) + (4279390936241/789500000000000000000000000 : ℝ)*base65 + (34200917924247021/1579000000000000000000000000000 : ℝ)*base68 + (23732198003811021/1579000000000000000000000000000 : ℝ)*base70 + (15443728697552021/1579000000000000000000000000000 : ℝ)*base72 + (209076790889/394750000000000000000000000 : ℝ)*base74 + (9054916379503021/1579000000000000000000000000000 : ℝ)*base76 + (2392301193417021/1579000000000000000000000000000 : ℝ)*base78 + (53516842965901021/1579000000000000000000000000000 : ℝ)*base80 + (1527172588161/789500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (5682933/625000000000000000000 : ℝ)*base89 + (5682933/625000000000000000000 : ℝ)*base91 + (5682933/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2210389267527242635845801/789500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (431519481/100000000000000 : ℝ)*(base19) + (316443833/50000000000000 : ℝ)*(base23) + (106773851/100000000000000 : ℝ)*(lower1) + (32855371/50000000000000 : ℝ)*(upper3) + (39428943/50000000000000 : ℝ)*(lower4) + (41633483/50000000000000 : ℝ)*(upper5) + (164238486497203/5000000000000 : ℝ)*(major0) + (164238486497203/5000000000000 : ℝ)*(major1) + (164238486497203/5000000000000 : ℝ)*(major2) + (1568490607/50000000000000 : ℝ)*(sp2) + (1128987227012487/25000000000000 : ℝ)*(sp4) + (4515948476530467/100000000000000 : ℝ)*(sp5) + (1128986284545267/25000000000000 : ℝ)*(sp6) + (2053590458513721/100000000000000 : ℝ)*(sp7) + (2053590458513721/100000000000000 : ℝ)*(f.failure) + (1128987227012487/25000000000000 : ℝ)*(f.sum) + (936970077241/592125000000000000000000000 : ℝ)*base66 + (6949782019699199/9474000000000000000000000000000 : ℝ)*base68 + (55722180248959199/9474000000000000000000000000000 : ℝ)*base70 + (563634261259963199/9474000000000000000000000000000 : ℝ)*base72 + (893502910207/473700000000000000000000000 : ℝ)*base73 + (493610090896396801/9474000000000000000000000000000 : ℝ)*base75 + (41085317961391199/9474000000000000000000000000000 : ℝ)*base78 + (121111084793827199/9474000000000000000000000000000 : ℝ)*base80 + (3718658142349/592125000000000000000000000 : ℝ)*base82 + (22777181/5000000000000000000000 : ℝ)*base89 + (22777181/5000000000000000000000 : ℝ)*base91 + (22777181/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1469_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79976261/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10737/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5369/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (967/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1469_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1469_s7_0 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1933466739/10000000000 : ℝ)*x 0 + (5438871987/10000000000 : ℝ)*x 1 + (1043032551/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1933466739/10000000000 : ℝ)^4435 ≤ (11805686875847/100000000000000 : ℝ)^3411 := by
    have hnat : (1933466739 : ℕ)^4435*100000000000000^3411 ≤ 11805686875847^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933466739 10000000000 11805686875847 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438871987/10000000000 : ℝ)^4435 ≤ (9060187916219/20000000000000 : ℝ)^3411 := by
    have hnat : (5438871987 : ℕ)^4435*20000000000000^3411 ≤ 9060187916219^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438871987 10000000000 9060187916219 20000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043032551/2000000000 : ℝ)^4435 ≤ (2144668676741/5000000000000 : ℝ)^3411 := by
    have hnat : (1043032551 : ℕ)^4435*5000000000000^3411 ≤ 2144668676741^3411*2000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043032551 2000000000 2144668676741 5000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1933466739/10000000000 : ℝ), (5438871987/10000000000 : ℝ), (1043032551/2000000000 : ℝ)] ![(11805686875847/100000000000000 : ℝ), (9060187916219/20000000000000 : ℝ), (2144668676741/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1933466739/10000000000 : ℝ)|^4435 ≤ (11805686875847/100000000000000 : ℝ)^3411
        have hw : |(-1933466739/10000000000 : ℝ)|=(1933466739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438871987/10000000000 : ℝ)|^4435 ≤ (9060187916219/20000000000000 : ℝ)^3411
        have hw : |(5438871987/10000000000 : ℝ)|=(5438871987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043032551/2000000000 : ℝ)|^4435 ≤ (2144668676741/5000000000000 : ℝ)^3411
        have hw : |(1043032551/2000000000 : ℝ)|=(1043032551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s7_1 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669233109/1250000000 : ℝ)*x 0 + (-1024072043/5000000000 : ℝ)*x 1 + (5215162759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669233109/1250000000 : ℝ)^4435 ≤ (693476855033/1562500000000 : ℝ)^3411 := by
    have hnat : (669233109 : ℕ)^4435*1562500000000^3411 ≤ 693476855033^3411*1250000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669233109 1250000000 693476855033 1562500000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1024072043/5000000000 : ℝ)^4435 ≤ (6362053844229/50000000000000 : ℝ)^3411 := by
    have hnat : (1024072043 : ℕ)^4435*50000000000000^3411 ≤ 6362053844229^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024072043 5000000000 6362053844229 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215162759/10000000000 : ℝ)^4435 ≤ (10723343394399/25000000000000 : ℝ)^3411 := by
    have hnat : (5215162759 : ℕ)^4435*25000000000000^3411 ≤ 10723343394399^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215162759 10000000000 10723343394399 25000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669233109/1250000000 : ℝ), (-1024072043/5000000000 : ℝ), (5215162759/10000000000 : ℝ)] ![(693476855033/1562500000000 : ℝ), (6362053844229/50000000000000 : ℝ), (10723343394399/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669233109/1250000000 : ℝ)|^4435 ≤ (693476855033/1562500000000 : ℝ)^3411
        have hw : |(669233109/1250000000 : ℝ)|=(669233109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1024072043/5000000000 : ℝ)|^4435 ≤ (6362053844229/50000000000000 : ℝ)^3411
        have hw : |(-1024072043/5000000000 : ℝ)|=(1024072043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215162759/10000000000 : ℝ)|^4435 ≤ (10723343394399/25000000000000 : ℝ)^3411
        have hw : |(5215162759/10000000000 : ℝ)|=(5215162759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s7_2 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353864871/10000000000 : ℝ)*x 0 + (130379069/250000000 : ℝ)*x 1 + (-1024072043/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353864871/10000000000 : ℝ)^4435 ≤ (44382518711333/100000000000000 : ℝ)^3411 := by
    have hnat : (5353864871 : ℕ)^4435*100000000000000^3411 ≤ 44382518711333^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353864871 10000000000 44382518711333 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130379069/250000000 : ℝ)^4435 ≤ (4289337358829/10000000000000 : ℝ)^3411 := by
    have hnat : (130379069 : ℕ)^4435*10000000000000^3411 ≤ 4289337358829^3411*250000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130379069 250000000 4289337358829 10000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1024072043/5000000000 : ℝ)^4435 ≤ (6362053844229/50000000000000 : ℝ)^3411 := by
    have hnat : (1024072043 : ℕ)^4435*50000000000000^3411 ≤ 6362053844229^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024072043 5000000000 6362053844229 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353864871/10000000000 : ℝ), (130379069/250000000 : ℝ), (-1024072043/5000000000 : ℝ)] ![(44382518711333/100000000000000 : ℝ), (4289337358829/10000000000000 : ℝ), (6362053844229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353864871/10000000000 : ℝ)|^4435 ≤ (44382518711333/100000000000000 : ℝ)^3411
        have hw : |(5353864871/10000000000 : ℝ)|=(5353864871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130379069/250000000 : ℝ)|^4435 ≤ (4289337358829/10000000000000 : ℝ)^3411
        have hw : |(130379069/250000000 : ℝ)|=(130379069/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1024072043/5000000000 : ℝ)|^4435 ≤ (6362053844229/50000000000000 : ℝ)^3411
        have hw : |(-1024072043/5000000000 : ℝ)|=(1024072043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s7_3 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4290227209/10000000000 : ℝ)*x 0 + (6480737/16000000 : ℝ)*x 1 + (4542408491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4290227209/10000000000 : ℝ)^4435 ≤ (33277367197467/100000000000000 : ℝ)^3411 := by
    have hnat : (4290227209 : ℕ)^4435*100000000000000^3411 ≤ 33277367197467^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4290227209 10000000000 33277367197467 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6480737/16000000 : ℝ)^4435 ≤ (3087985069139/10000000000000 : ℝ)^3411 := by
    have hnat : (6480737 : ℕ)^4435*10000000000000^3411 ≤ 3087985069139^3411*16000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6480737 16000000 3087985069139 10000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4542408491/10000000000 : ℝ)^4435 ≤ (2240173880627/6250000000000 : ℝ)^3411 := by
    have hnat : (4542408491 : ℕ)^4435*6250000000000^3411 ≤ 2240173880627^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4542408491 10000000000 2240173880627 6250000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4290227209/10000000000 : ℝ), (6480737/16000000 : ℝ), (4542408491/10000000000 : ℝ)] ![(33277367197467/100000000000000 : ℝ), (3087985069139/10000000000000 : ℝ), (2240173880627/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4290227209/10000000000 : ℝ)|^4435 ≤ (33277367197467/100000000000000 : ℝ)^3411
        have hw : |(4290227209/10000000000 : ℝ)|=(4290227209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6480737/16000000 : ℝ)|^4435 ≤ (3087985069139/10000000000000 : ℝ)^3411
        have hw : |(6480737/16000000 : ℝ)|=(6480737/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4542408491/10000000000 : ℝ)|^4435 ≤ (2240173880627/6250000000000 : ℝ)^3411
        have hw : |(4542408491/10000000000 : ℝ)|=(4542408491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s7_4 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-966748481/5000000000 : ℝ)*x 0 + (652038179/1250000000 : ℝ)*x 1 + (2718860699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (966748481/5000000000 : ℝ)^4435 ≤ (1180592681717/10000000000000 : ℝ)^3411 := by
    have hnat : (966748481 : ℕ)^4435*10000000000000^3411 ≤ 1180592681717^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966748481 5000000000 1180592681717 10000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652038179/1250000000 : ℝ)^4435 ≤ (10726398389369/25000000000000 : ℝ)^3411 := by
    have hnat : (652038179 : ℕ)^4435*25000000000000^3411 ≤ 10726398389369^3411*1250000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652038179 1250000000 10726398389369 25000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718860699/5000000000 : ℝ)^4435 ≤ (22644239809751/50000000000000 : ℝ)^3411 := by
    have hnat : (2718860699 : ℕ)^4435*50000000000000^3411 ≤ 22644239809751^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718860699 5000000000 22644239809751 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-966748481/5000000000 : ℝ), (652038179/1250000000 : ℝ), (2718860699/5000000000 : ℝ)] ![(1180592681717/10000000000000 : ℝ), (10726398389369/25000000000000 : ℝ), (22644239809751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-966748481/5000000000 : ℝ)|^4435 ≤ (1180592681717/10000000000000 : ℝ)^3411
        have hw : |(-966748481/5000000000 : ℝ)|=(966748481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652038179/1250000000 : ℝ)|^4435 ≤ (10726398389369/25000000000000 : ℝ)^3411
        have hw : |(652038179/1250000000 : ℝ)|=(652038179/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718860699/5000000000 : ℝ)|^4435 ≤ (22644239809751/50000000000000 : ℝ)^3411
        have hw : |(2718860699/5000000000 : ℝ)|=(2718860699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_s7_5 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072573669/2500000000 : ℝ)*x 0 + (2269948439/5000000000 : ℝ)*x 1 + (1013247769/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072573669/2500000000 : ℝ)^4435 ≤ (16639023805541/50000000000000 : ℝ)^3411 := by
    have hnat : (1072573669 : ℕ)^4435*50000000000000^3411 ≤ 16639023805541^3411*2500000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072573669 2500000000 16639023805541 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2269948439/5000000000 : ℝ)^4435 ≤ (4477127032769/12500000000000 : ℝ)^3411 := by
    have hnat : (2269948439 : ℕ)^4435*12500000000000^3411 ≤ 4477127032769^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269948439 5000000000 4477127032769 12500000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1013247769/2500000000 : ℝ)^4435 ≤ (3863117013597/12500000000000 : ℝ)^3411 := by
    have hnat : (1013247769 : ℕ)^4435*12500000000000^3411 ≤ 3863117013597^3411*2500000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013247769 2500000000 3863117013597 12500000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072573669/2500000000 : ℝ), (2269948439/5000000000 : ℝ), (1013247769/2500000000 : ℝ)] ![(16639023805541/50000000000000 : ℝ), (4477127032769/12500000000000 : ℝ), (3863117013597/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072573669/2500000000 : ℝ)|^4435 ≤ (16639023805541/50000000000000 : ℝ)^3411
        have hw : |(1072573669/2500000000 : ℝ)|=(1072573669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2269948439/5000000000 : ℝ)|^4435 ≤ (4477127032769/12500000000000 : ℝ)^3411
        have hw : |(2269948439/5000000000 : ℝ)|=(2269948439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1013247769/2500000000 : ℝ)|^4435 ≤ (3863117013597/12500000000000 : ℝ)^3411
        have hw : |(1013247769/2500000000 : ℝ)|=(1013247769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1469_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79976261/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (967/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5369/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10739/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (967/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (967/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5369/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (967/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5369/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (967/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5369/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (967/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5369/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (967/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5369/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (967/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5369/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5369/50000 : ℝ) ^ (4433/1024 : ℝ) ≤ (6379240494178419/100000000000000000000 : ℝ) := by
    have hpowers : (5369/50000 : ℝ)^4433 ≤ (6379240494178419/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5369 : ℕ)^4433*100000000000000000000^1024 ≤ 6379240494178419^1024*50000^4433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5369 50000 6379240494178419 100000000000000000000 4433 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5369/50000 : ℝ)) (X := (6379240494178419/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (967/6250 : ℝ) ^ (4433/1024 : ℝ) ≤ (3100732487430031/10000000000000000000 : ℝ) := by
    have hpowers : (967/6250 : ℝ)^4433 ≤ (3100732487430031/10000000000000000000 : ℝ)^1024 := by
      have hnat : (967 : ℕ)^4433*10000000000000000000^1024 ≤ 3100732487430031^1024*6250^4433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        967 6250 3100732487430031 10000000000000000000 4433 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (967/6250 : ℝ)) (X := (3100732487430031/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006379240494178419/50000000000000000000 : ℝ) ≤ (2500073674958663/2500000000000000 : ℝ) ^ (4433/1024 : ℝ) := by
    have hpowers : (50006379240494178419/50000000000000000000 : ℝ)^1024 ≤ (2500073674958663/2500000000000000 : ℝ)^4433 := by
      have hnat : (50006379240494178419 : ℕ)^1024*2500000000000000^4433 ≤ 2500073674958663^4433*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006379240494178419 50000000000000000000 2500073674958663 2500000000000000 1024 4433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500073674958663/2500000000000000 : ℝ)) (X := (50006379240494178419/50000000000000000000 : ℝ)) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037386565368478729/100000000000000000000 : ℝ) ≤ (2000172697228781/2000000000000000 : ℝ) ^ (4433/1024 : ℝ) := by
    have hpowers : (100037386565368478729/100000000000000000000 : ℝ)^1024 ≤ (2000172697228781/2000000000000000 : ℝ)^4433 := by
      have hnat : (100037386565368478729 : ℕ)^1024*2000000000000000^4433 ≤ 2000172697228781^4433*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037386565368478729 100000000000000000000 2000172697228781 2000000000000000 1024 4433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000172697228781/2000000000000000 : ℝ)) (X := (100037386565368478729/100000000000000000000 : ℝ)) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003100732487430031/5000000000000000000 : ℝ) ≤ (5000716136226579/5000000000000000 : ℝ) ^ (4433/1024 : ℝ) := by
    have hpowers : (5003100732487430031/5000000000000000000 : ℝ)^1024 ≤ (5000716136226579/5000000000000000 : ℝ)^4433 := by
      have hnat : (5003100732487430031 : ℕ)^1024*5000000000000000^4433 ≤ 5000716136226579^4433*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003100732487430031 5000000000000000000 5000716136226579 5000000000000000 1024 4433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000716136226579/5000000000000000 : ℝ)) (X := (5003100732487430031/5000000000000000000 : ℝ)) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6379240494178419/100000000000000000000 : ℝ) ≤ ((2366458992711986257/2367000000000000000 : ℝ)+2*(568786309253/473400000000000 : ℝ)*(5369/50000 : ℝ))^(4433/1024 : ℝ) := by
    rw [show (2366458992711986257/2367000000000000000 : ℝ)+2*(568786309253/473400000000000 : ℝ)*(5369/50000 : ℝ)=(2500073674958663/2500000000000000 : ℝ) by norm_num, show 1+2*(6379240494178419/100000000000000000000 : ℝ)=(50006379240494178419/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3100732487430031/10000000000000000000 : ℝ)+(6379240494178419/100000000000000000000 : ℝ) ≤ ((2366458992711986257/2367000000000000000 : ℝ)+(568786309253/473400000000000 : ℝ)*((967/6250 : ℝ)+(5369/50000 : ℝ)))^(4433/1024 : ℝ) := by
    rw [show (2366458992711986257/2367000000000000000 : ℝ)+(568786309253/473400000000000 : ℝ)*((967/6250 : ℝ)+(5369/50000 : ℝ))=(2000172697228781/2000000000000000 : ℝ) by norm_num, show 1+(3100732487430031/10000000000000000000 : ℝ)+(6379240494178419/100000000000000000000 : ℝ)=(100037386565368478729/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3100732487430031/10000000000000000000 : ℝ) ≤ ((2366458992711986257/2367000000000000000 : ℝ)+2*(568786309253/473400000000000 : ℝ)*(967/6250 : ℝ))^(4433/1024 : ℝ) := by
    rw [show (2366458992711986257/2367000000000000000 : ℝ)+2*(568786309253/473400000000000 : ℝ)*(967/6250 : ℝ)=(5000716136226579/5000000000000000 : ℝ) by norm_num, show 1+2*(3100732487430031/10000000000000000000 : ℝ)=(5003100732487430031/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2366458992711986257/2367000000000000000 : ℝ)*(X 1 0+X 2 0)+(568786309253/473400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4433/1024 : ℝ)) (lo := (5369/50000 : ℝ)) (hi := (967/6250 : ℝ)) (c := (2366458992711986257/2367000000000000000 : ℝ)) (alpha := (568786309253/473400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2366458992711986257/2367000000000000000 : ℝ)*(X 0 1+X 2 1)+(568786309253/473400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4433/1024 : ℝ)) (lo := (5369/50000 : ℝ)) (hi := (967/6250 : ℝ)) (c := (2366458992711986257/2367000000000000000 : ℝ)) (alpha := (568786309253/473400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2366458992711986257/2367000000000000000 : ℝ)*(X 0 2+X 1 2)+(568786309253/473400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4433/1024 : ℝ)) (lo := (5369/50000 : ℝ)) (hi := (967/6250 : ℝ)) (c := (2366458992711986257/2367000000000000000 : ℝ)) (alpha := (568786309253/473400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1933466739/10000000000 : ℝ)*X 0 0+(5438871987/10000000000 : ℝ)*X 0 1+(1043032551/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669233109/1250000000 : ℝ)*X 1 0+(-1024072043/5000000000 : ℝ)*X 1 1+(5215162759/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353864871/10000000000 : ℝ)*X 2 0+(130379069/250000000 : ℝ)*X 2 1+(-1024072043/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4290227209/10000000000 : ℝ)*X 0 0+(6480737/16000000 : ℝ)*X 0 1+(4542408491/10000000000 : ℝ)*X 0 2+(4290227209/10000000000 : ℝ)*X 1 0+(6480737/16000000 : ℝ)*X 1 1+(4542408491/10000000000 : ℝ)*X 1 2+(4290227209/10000000000 : ℝ)*X 2 0+(6480737/16000000 : ℝ)*X 2 1+(4542408491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-966748481/5000000000 : ℝ)*X 0 0+(652038179/1250000000 : ℝ)*X 0 1+(2718860699/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1072573669/2500000000 : ℝ)*X 0 0+(2269948439/5000000000 : ℝ)*X 0 1+(1013247769/2500000000 : ℝ)*X 0 2+(1072573669/2500000000 : ℝ)*X 1 0+(2269948439/5000000000 : ℝ)*X 1 1+(1013247769/2500000000 : ℝ)*X 1 2+(1072573669/2500000000 : ℝ)*X 2 0+(2269948439/5000000000 : ℝ)*X 2 1+(1013247769/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3626068542068453978501/1315000000000000000000000000 : ℝ) := by norm_num
    linear_combination (250756237/50000000000000 : ℝ)*(base19) + (235447891/50000000000000 : ℝ)*(base23) + (15944753/100000000000000 : ℝ)*(lower2) + (34249219/50000000000000 : ℝ)*(upper3) + (5787903/12500000000000 : ℝ)*(upper5) + (812855879618329/25000000000000 : ℝ)*(major0) + (812855879618329/25000000000000 : ℝ)*(major1) + (812855879618329/25000000000000 : ℝ)*(major2) + (4470096270244921/100000000000000 : ℝ)*(sp0) + (447010355342943/10000000000000 : ℝ)*(sp1) + (2235051792023061/50000000000000 : ℝ)*(sp2) + (1016369562152943/50000000000000 : ℝ)*(sp3) + (7784696983/100000000000000 : ℝ)*(sp4) + (941445821/25000000000000 : ℝ)*(sp5) + (203274289008917/10000000000000 : ℝ)*(f.failure) + (279381503433869/6250000000000 : ℝ)*(f.sum) + (62296915462819/11835000000000000000000000000 : ℝ)*base65 + (166870914817114553/59175000000000000000000000000000 : ℝ)*base67 + (152883885056335447/59175000000000000000000000000000 : ℝ)*base70 + (150688603736839553/59175000000000000000000000000000 : ℝ)*base71 + (12410510781901/2958750000000000000000000000 : ℝ)*base73 + (267585023247010447/59175000000000000000000000000000 : ℝ)*base76 + (256517333390989553/59175000000000000000000000000000 : ℝ)*base77 + (83082926347360447/59175000000000000000000000000000 : ℝ)*base80 + (1148342256559/739687500000000000000000000 : ℝ)*base81 + (2680663/500000000000000000000 : ℝ)*base90 + (2680663/500000000000000000000 : ℝ)*base92 + (2680663/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1469_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79976261/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (967/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5369/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10739/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (967/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1469_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1469_box_0 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1711813933/10000000000 : ℝ)*x 0 + (1081499217/2000000000 : ℝ)*x 1 + (2703747587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1711813933/10000000000 : ℝ)^4435 ≤ (5038557504727/50000000000000 : ℝ)^3411 := by
    have hnat : (1711813933 : ℕ)^4435*50000000000000^3411 ≤ 5038557504727^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1711813933 10000000000 5038557504727 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081499217/2000000000 : ℝ)^4435 ≤ (44961447409549/100000000000000 : ℝ)^3411 := by
    have hnat : (1081499217 : ℕ)^4435*100000000000000^3411 ≤ 44961447409549^3411*2000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081499217 2000000000 44961447409549 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703747587/5000000000 : ℝ)^4435 ≤ (44961437560953/100000000000000 : ℝ)^3411 := by
    have hnat : (2703747587 : ℕ)^4435*100000000000000^3411 ≤ 44961437560953^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703747587 5000000000 44961437560953 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1711813933/10000000000 : ℝ), (1081499217/2000000000 : ℝ), (2703747587/5000000000 : ℝ)] ![(5038557504727/50000000000000 : ℝ), (44961447409549/100000000000000 : ℝ), (44961437560953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1711813933/10000000000 : ℝ)|^4435 ≤ (5038557504727/50000000000000 : ℝ)^3411
        have hw : |(-1711813933/10000000000 : ℝ)|=(1711813933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081499217/2000000000 : ℝ)|^4435 ≤ (44961447409549/100000000000000 : ℝ)^3411
        have hw : |(1081499217/2000000000 : ℝ)|=(1081499217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703747587/5000000000 : ℝ)|^4435 ≤ (44961437560953/100000000000000 : ℝ)^3411
        have hw : |(2703747587/5000000000 : ℝ)|=(2703747587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_box_1 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5269982871/10000000000 : ℝ)*x 0 + (-1902195009/10000000000 : ℝ)*x 1 + (2703747707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5269982871/10000000000 : ℝ)^4435 ≤ (8696106913579/20000000000000 : ℝ)^3411 := by
    have hnat : (5269982871 : ℕ)^4435*20000000000000^3411 ≤ 8696106913579^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5269982871 10000000000 8696106913579 20000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1902195009/10000000000 : ℝ)^4435 ≤ (462321010153/4000000000000 : ℝ)^3411 := by
    have hnat : (1902195009 : ℕ)^4435*4000000000000^3411 ≤ 462321010153^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1902195009 10000000000 462321010153 4000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703747707/5000000000 : ℝ)^4435 ≤ (44961440155533/100000000000000 : ℝ)^3411 := by
    have hnat : (2703747707 : ℕ)^4435*100000000000000^3411 ≤ 44961440155533^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703747707 5000000000 44961440155533 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5269982871/10000000000 : ℝ), (-1902195009/10000000000 : ℝ), (2703747707/5000000000 : ℝ)] ![(8696106913579/20000000000000 : ℝ), (462321010153/4000000000000 : ℝ), (44961440155533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5269982871/10000000000 : ℝ)|^4435 ≤ (8696106913579/20000000000000 : ℝ)^3411
        have hw : |(5269982871/10000000000 : ℝ)|=(5269982871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1902195009/10000000000 : ℝ)|^4435 ≤ (462321010153/4000000000000 : ℝ)^3411
        have hw : |(-1902195009/10000000000 : ℝ)|=(1902195009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703747707/5000000000 : ℝ)|^4435 ≤ (44961440155533/100000000000000 : ℝ)^3411
        have hw : |(2703747707/5000000000 : ℝ)|=(2703747707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_box_2 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (263499159/500000000 : ℝ)*x 0 + (2703747577/5000000000 : ℝ)*x 1 + (-1902194947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263499159/500000000 : ℝ)^4435 ≤ (8696107576537/20000000000000 : ℝ)^3411 := by
    have hnat : (263499159 : ℕ)^4435*20000000000000^3411 ≤ 8696107576537^3411*500000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263499159 500000000 8696107576537 20000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703747577/5000000000 : ℝ)^4435 ≤ (22480718672369/50000000000000 : ℝ)^3411 := by
    have hnat : (2703747577 : ℕ)^4435*50000000000000^3411 ≤ 22480718672369^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703747577 5000000000 22480718672369 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1902194947/10000000000 : ℝ)^4435 ≤ (1155802476401/10000000000000 : ℝ)^3411 := by
    have hnat : (1902194947 : ℕ)^4435*10000000000000^3411 ≤ 1155802476401^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1902194947 10000000000 1155802476401 10000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263499159/500000000 : ℝ), (2703747577/5000000000 : ℝ), (-1902194947/10000000000 : ℝ)] ![(8696107576537/20000000000000 : ℝ), (22480718672369/50000000000000 : ℝ), (1155802476401/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263499159/500000000 : ℝ)|^4435 ≤ (8696107576537/20000000000000 : ℝ)^3411
        have hw : |(263499159/500000000 : ℝ)|=(263499159/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703747577/5000000000 : ℝ)|^4435 ≤ (22480718672369/50000000000000 : ℝ)^3411
        have hw : |(2703747577/5000000000 : ℝ)|=(2703747577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1902194947/10000000000 : ℝ)|^4435 ≤ (1155802476401/10000000000000 : ℝ)^3411
        have hw : |(-1902194947/10000000000 : ℝ)|=(1902194947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_box_3 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (280962281/625000000 : ℝ)*x 0 + (838983743/2000000000 : ℝ)*x 1 + (4194918957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (280962281/625000000 : ℝ)^4435 ≤ (2210075766163/6250000000000 : ℝ)^3411 := by
    have hnat : (280962281 : ℕ)^4435*6250000000000^3411 ≤ 2210075766163^3411*625000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280962281 625000000 2210075766163 6250000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (838983743/2000000000 : ℝ)^4435 ≤ (8079848161627/25000000000000 : ℝ)^3411 := by
    have hnat : (838983743 : ℕ)^4435*25000000000000^3411 ≤ 8079848161627^3411*2000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838983743 2000000000 8079848161627 25000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4194918957/10000000000 : ℝ)^4435 ≤ (323193950707/1000000000000 : ℝ)^3411 := by
    have hnat : (4194918957 : ℕ)^4435*1000000000000^3411 ≤ 323193950707^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4194918957 10000000000 323193950707 1000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(280962281/625000000 : ℝ), (838983743/2000000000 : ℝ), (4194918957/10000000000 : ℝ)] ![(2210075766163/6250000000000 : ℝ), (8079848161627/25000000000000 : ℝ), (323193950707/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(280962281/625000000 : ℝ)|^4435 ≤ (2210075766163/6250000000000 : ℝ)^3411
        have hw : |(280962281/625000000 : ℝ)|=(280962281/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(838983743/2000000000 : ℝ)|^4435 ≤ (8079848161627/25000000000000 : ℝ)^3411
        have hw : |(838983743/2000000000 : ℝ)|=(838983743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4194918957/10000000000 : ℝ)|^4435 ≤ (323193950707/1000000000000 : ℝ)^3411
        have hw : |(4194918957/10000000000 : ℝ)|=(4194918957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_box_4 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2160588749/10000000000 : ℝ)*x 0 + (5241955331/10000000000 : ℝ)*x 1 + (5241955839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160588749/10000000000 : ℝ)^4435 ≤ (272795486763/2000000000000 : ℝ)^3411 := by
    have hnat : (2160588749 : ℕ)^4435*2000000000000^3411 ≤ 272795486763^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160588749 10000000000 272795486763 2000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241955331/10000000000 : ℝ)^4435 ≤ (10795027526571/25000000000000 : ℝ)^3411 := by
    have hnat : (5241955331 : ℕ)^4435*25000000000000^3411 ≤ 10795027526571^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241955331 10000000000 10795027526571 25000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241955839/10000000000 : ℝ)^4435 ≤ (345440924377/800000000000 : ℝ)^3411 := by
    have hnat : (5241955839 : ℕ)^4435*800000000000^3411 ≤ 345440924377^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241955839 10000000000 345440924377 800000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2160588749/10000000000 : ℝ), (5241955331/10000000000 : ℝ), (5241955839/10000000000 : ℝ)] ![(272795486763/2000000000000 : ℝ), (10795027526571/25000000000000 : ℝ), (345440924377/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2160588749/10000000000 : ℝ)|^4435 ≤ (272795486763/2000000000000 : ℝ)^3411
        have hw : |(-2160588749/10000000000 : ℝ)|=(2160588749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241955331/10000000000 : ℝ)|^4435 ≤ (10795027526571/25000000000000 : ℝ)^3411
        have hw : |(5241955331/10000000000 : ℝ)|=(5241955331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241955839/10000000000 : ℝ)|^4435 ≤ (345440924377/800000000000 : ℝ)^3411
        have hw : |(5241955839/10000000000 : ℝ)|=(5241955839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_box_5 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5385625569/10000000000 : ℝ)*x 0 + (-196977313/1000000000 : ℝ)*x 1 + (5241955603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5385625569/10000000000 : ℝ)^4435 ≤ (22362577160093/50000000000000 : ℝ)^3411 := by
    have hnat : (5385625569 : ℕ)^4435*50000000000000^3411 ≤ 22362577160093^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385625569 10000000000 22362577160093 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (196977313/1000000000 : ℝ)^4435 ≤ (12094732646577/100000000000000 : ℝ)^3411 := by
    have hnat : (196977313 : ℕ)^4435*100000000000000^3411 ≤ 12094732646577^3411*1000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196977313 1000000000 12094732646577 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241955603/10000000000 : ℝ)^4435 ≤ (4318011301949/10000000000000 : ℝ)^3411 := by
    have hnat : (5241955603 : ℕ)^4435*10000000000000^3411 ≤ 4318011301949^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241955603 10000000000 4318011301949 10000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5385625569/10000000000 : ℝ), (-196977313/1000000000 : ℝ), (5241955603/10000000000 : ℝ)] ![(22362577160093/50000000000000 : ℝ), (12094732646577/100000000000000 : ℝ), (4318011301949/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5385625569/10000000000 : ℝ)|^4435 ≤ (22362577160093/50000000000000 : ℝ)^3411
        have hw : |(5385625569/10000000000 : ℝ)|=(5385625569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-196977313/1000000000 : ℝ)|^4435 ≤ (12094732646577/100000000000000 : ℝ)^3411
        have hw : |(-196977313/1000000000 : ℝ)|=(196977313/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241955603/10000000000 : ℝ)|^4435 ≤ (4318011301949/10000000000000 : ℝ)^3411
        have hw : |(5241955603/10000000000 : ℝ)|=(5241955603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_box_6 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (269281299/500000000 : ℝ)*x 0 + (2620977749/5000000000 : ℝ)*x 1 + (-393954543/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269281299/500000000 : ℝ)^4435 ≤ (44725158758003/100000000000000 : ℝ)^3411 := by
    have hnat : (269281299 : ℕ)^4435*100000000000000^3411 ≤ 44725158758003^3411*500000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269281299 500000000 44725158758003 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620977749/5000000000 : ℝ)^4435 ≤ (43180111894907/100000000000000 : ℝ)^3411 := by
    have hnat : (2620977749 : ℕ)^4435*100000000000000^3411 ≤ 43180111894907^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620977749 5000000000 43180111894907 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (393954543/2000000000 : ℝ)^4435 ≤ (2418945866687/20000000000000 : ℝ)^3411 := by
    have hnat : (393954543 : ℕ)^4435*20000000000000^3411 ≤ 2418945866687^3411*2000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393954543 2000000000 2418945866687 20000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269281299/500000000 : ℝ), (2620977749/5000000000 : ℝ), (-393954543/2000000000 : ℝ)] ![(44725158758003/100000000000000 : ℝ), (43180111894907/100000000000000 : ℝ), (2418945866687/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269281299/500000000 : ℝ)|^4435 ≤ (44725158758003/100000000000000 : ℝ)^3411
        have hw : |(269281299/500000000 : ℝ)|=(269281299/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620977749/5000000000 : ℝ)|^4435 ≤ (43180111894907/100000000000000 : ℝ)^3411
        have hw : |(2620977749/5000000000 : ℝ)|=(2620977749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-393954543/2000000000 : ℝ)|^4435 ≤ (2418945866687/20000000000000 : ℝ)^3411
        have hw : |(-393954543/2000000000 : ℝ)|=(393954543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_box_7 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1020713733/2500000000 : ℝ)*x 0 + (880209819/2000000000 : ℝ)*x 1 + (4401049599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1020713733/2500000000 : ℝ)^4435 ≤ (97504198879/312500000000 : ℝ)^3411 := by
    have hnat : (1020713733 : ℕ)^4435*312500000000^3411 ≤ 97504198879^3411*2500000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020713733 2500000000 97504198879 312500000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (880209819/2000000000 : ℝ)^4435 ≤ (34399325610379/100000000000000 : ℝ)^3411 := by
    have hnat : (880209819 : ℕ)^4435*100000000000000^3411 ≤ 34399325610379^3411*2000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880209819 2000000000 34399325610379 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4401049599/10000000000 : ℝ)^4435 ≤ (34399330732339/100000000000000 : ℝ)^3411 := by
    have hnat : (4401049599 : ℕ)^4435*100000000000000^3411 ≤ 34399330732339^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4401049599 10000000000 34399330732339 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1020713733/2500000000 : ℝ), (880209819/2000000000 : ℝ), (4401049599/10000000000 : ℝ)] ![(97504198879/312500000000 : ℝ), (34399325610379/100000000000000 : ℝ), (34399330732339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1020713733/2500000000 : ℝ)|^4435 ≤ (97504198879/312500000000 : ℝ)^3411
        have hw : |(1020713733/2500000000 : ℝ)|=(1020713733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(880209819/2000000000 : ℝ)|^4435 ≤ (34399325610379/100000000000000 : ℝ)^3411
        have hw : |(880209819/2000000000 : ℝ)|=(880209819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4401049599/10000000000 : ℝ)|^4435 ≤ (34399330732339/100000000000000 : ℝ)^3411
        have hw : |(4401049599/10000000000 : ℝ)|=(4401049599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_box_8 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2066006349/10000000000 : ℝ)*x 0 + (2563238703/5000000000 : ℝ)*x 1 + (339254439/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2066006349/10000000000 : ℝ)^4435 ≤ (6434289599821/50000000000000 : ℝ)^3411 := by
    have hnat : (2066006349 : ℕ)^4435*50000000000000^3411 ≤ 6434289599821^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066006349 10000000000 6434289599821 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2563238703/5000000000 : ℝ)^4435 ≤ (20973707923559/50000000000000 : ℝ)^3411 := by
    have hnat : (2563238703 : ℕ)^4435*50000000000000^3411 ≤ 20973707923559^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2563238703 5000000000 20973707923559 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339254439/625000000 : ℝ)^4435 ≤ (22592002465661/50000000000000 : ℝ)^3411 := by
    have hnat : (339254439 : ℕ)^4435*50000000000000^3411 ≤ 22592002465661^3411*625000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339254439 625000000 22592002465661 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2066006349/10000000000 : ℝ), (2563238703/5000000000 : ℝ), (339254439/625000000 : ℝ)] ![(6434289599821/50000000000000 : ℝ), (20973707923559/50000000000000 : ℝ), (22592002465661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2066006349/10000000000 : ℝ)|^4435 ≤ (6434289599821/50000000000000 : ℝ)^3411
        have hw : |(-2066006349/10000000000 : ℝ)|=(2066006349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2563238703/5000000000 : ℝ)|^4435 ≤ (20973707923559/50000000000000 : ℝ)^3411
        have hw : |(2563238703/5000000000 : ℝ)|=(2563238703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339254439/625000000 : ℝ)|^4435 ≤ (22592002465661/50000000000000 : ℝ)^3411
        have hw : |(339254439/625000000 : ℝ)|=(339254439/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_box_9 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5255600831/10000000000 : ℝ)*x 0 + (-236692219/1250000000 : ℝ)*x 1 + (542807127/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5255600831/10000000000 : ℝ)^4435 ≤ (43326314810653/100000000000000 : ℝ)^3411 := by
    have hnat : (5255600831 : ℕ)^4435*100000000000000^3411 ≤ 43326314810653^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255600831 10000000000 43326314810653 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (236692219/1250000000 : ℝ)^4435 ≤ (11489677584047/100000000000000 : ℝ)^3411 := by
    have hnat : (236692219 : ℕ)^4435*100000000000000^3411 ≤ 11489677584047^3411*1250000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236692219 1250000000 11489677584047 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542807127/1000000000 : ℝ)^4435 ≤ (45184007593801/100000000000000 : ℝ)^3411 := by
    have hnat : (542807127 : ℕ)^4435*100000000000000^3411 ≤ 45184007593801^3411*1000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542807127 1000000000 45184007593801 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5255600831/10000000000 : ℝ), (-236692219/1250000000 : ℝ), (542807127/1000000000 : ℝ)] ![(43326314810653/100000000000000 : ℝ), (11489677584047/100000000000000 : ℝ), (45184007593801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5255600831/10000000000 : ℝ)|^4435 ≤ (43326314810653/100000000000000 : ℝ)^3411
        have hw : |(5255600831/10000000000 : ℝ)|=(5255600831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-236692219/1250000000 : ℝ)|^4435 ≤ (11489677584047/100000000000000 : ℝ)^3411
        have hw : |(-236692219/1250000000 : ℝ)|=(236692219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542807127/1000000000 : ℝ)|^4435 ≤ (45184007593801/100000000000000 : ℝ)^3411
        have hw : |(542807127/1000000000 : ℝ)|=(542807127/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_box_10 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328475137/625000000 : ℝ)*x 0 + (5428070277/10000000000 : ℝ)*x 1 + (-378707453/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328475137/625000000 : ℝ)^4435 ≤ (43326329398777/100000000000000 : ℝ)^3411 := by
    have hnat : (328475137 : ℕ)^4435*100000000000000^3411 ≤ 43326329398777^3411*625000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328475137 625000000 43326329398777 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428070277/10000000000 : ℝ)^4435 ≤ (45183996846477/100000000000000 : ℝ)^3411 := by
    have hnat : (5428070277 : ℕ)^4435*100000000000000^3411 ≤ 45183996846477^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428070277 10000000000 45183996846477 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (378707453/2000000000 : ℝ)^4435 ≤ (11489673741893/100000000000000 : ℝ)^3411 := by
    have hnat : (378707453 : ℕ)^4435*100000000000000^3411 ≤ 11489673741893^3411*2000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378707453 2000000000 11489673741893 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328475137/625000000 : ℝ), (5428070277/10000000000 : ℝ), (-378707453/2000000000 : ℝ)] ![(43326329398777/100000000000000 : ℝ), (45183996846477/100000000000000 : ℝ), (11489673741893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328475137/625000000 : ℝ)|^4435 ≤ (43326329398777/100000000000000 : ℝ)^3411
        have hw : |(328475137/625000000 : ℝ)|=(328475137/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428070277/10000000000 : ℝ)|^4435 ≤ (45183996846477/100000000000000 : ℝ)^3411
        have hw : |(5428070277/10000000000 : ℝ)|=(5428070277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-378707453/2000000000 : ℝ)|^4435 ≤ (11489673741893/100000000000000 : ℝ)^3411
        have hw : |(-378707453/2000000000 : ℝ)|=(378707453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_box_11 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1136378573/2500000000 : ℝ)*x 0 + (4169267321/10000000000 : ℝ)*x 1 + (833853651/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1136378573/2500000000 : ℝ)^4435 ≤ (560541397119/1562500000000 : ℝ)^3411 := by
    have hnat : (1136378573 : ℕ)^4435*1562500000000^3411 ≤ 560541397119^3411*2500000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136378573 2500000000 560541397119 1562500000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4169267321/10000000000 : ℝ)^4435 ≤ (4007833826741/12500000000000 : ℝ)^3411 := by
    have hnat : (4169267321 : ℕ)^4435*12500000000000^3411 ≤ 4007833826741^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169267321 10000000000 4007833826741 12500000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (833853651/2000000000 : ℝ)^4435 ≤ (32062679952893/100000000000000 : ℝ)^3411 := by
    have hnat : (833853651 : ℕ)^4435*100000000000000^3411 ≤ 32062679952893^3411*2000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833853651 2000000000 32062679952893 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1136378573/2500000000 : ℝ), (4169267321/10000000000 : ℝ), (833853651/2000000000 : ℝ)] ![(560541397119/1562500000000 : ℝ), (4007833826741/12500000000000 : ℝ), (32062679952893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1136378573/2500000000 : ℝ)|^4435 ≤ (560541397119/1562500000000 : ℝ)^3411
        have hw : |(1136378573/2500000000 : ℝ)|=(1136378573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4169267321/10000000000 : ℝ)|^4435 ≤ (4007833826741/12500000000000 : ℝ)^3411
        have hw : |(4169267321/10000000000 : ℝ)|=(4169267321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(833853651/2000000000 : ℝ)|^4435 ≤ (32062679952893/100000000000000 : ℝ)^3411
        have hw : |(833853651/2000000000 : ℝ)|=(833853651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_box_12 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-56456079/312500000 : ℝ)*x 0 + (5519100923/10000000000 : ℝ)*x 1 + (5226978861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56456079/312500000 : ℝ)^4435 ≤ (10808524012477/100000000000000 : ℝ)^3411 := by
    have hnat : (56456079 : ℕ)^4435*100000000000000^3411 ≤ 10808524012477^3411*312500000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56456079 312500000 10808524012477 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5519100923/10000000000 : ℝ)^4435 ≤ (11542924943419/25000000000000 : ℝ)^3411 := by
    have hnat : (5519100923 : ℕ)^4435*25000000000000^3411 ≤ 11542924943419^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5519100923 10000000000 11542924943419 25000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5226978861/10000000000 : ℝ)^4435 ≤ (43019776196077/100000000000000 : ℝ)^3411 := by
    have hnat : (5226978861 : ℕ)^4435*100000000000000^3411 ≤ 43019776196077^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226978861 10000000000 43019776196077 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-56456079/312500000 : ℝ), (5519100923/10000000000 : ℝ), (5226978861/10000000000 : ℝ)] ![(10808524012477/100000000000000 : ℝ), (11542924943419/25000000000000 : ℝ), (43019776196077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-56456079/312500000 : ℝ)|^4435 ≤ (10808524012477/100000000000000 : ℝ)^3411
        have hw : |(-56456079/312500000 : ℝ)|=(56456079/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5519100923/10000000000 : ℝ)|^4435 ≤ (11542924943419/25000000000000 : ℝ)^3411
        have hw : |(5519100923/10000000000 : ℝ)|=(5519100923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5226978861/10000000000 : ℝ)|^4435 ≤ (43019776196077/100000000000000 : ℝ)^3411
        have hw : |(5226978861/10000000000 : ℝ)|=(5226978861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_box_13 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5396086153/10000000000 : ℝ)*x 0 + (-1975702033/10000000000 : ℝ)*x 1 + (5226978861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5396086153/10000000000 : ℝ)^4435 ≤ (22419068265533/50000000000000 : ℝ)^3411 := by
    have hnat : (5396086153 : ℕ)^4435*50000000000000^3411 ≤ 22419068265533^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396086153 10000000000 22419068265533 50000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1975702033/10000000000 : ℝ)^4435 ≤ (12142087265519/100000000000000 : ℝ)^3411 := by
    have hnat : (1975702033 : ℕ)^4435*100000000000000^3411 ≤ 12142087265519^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1975702033 10000000000 12142087265519 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5226978861/10000000000 : ℝ)^4435 ≤ (43019776196077/100000000000000 : ℝ)^3411 := by
    have hnat : (5226978861 : ℕ)^4435*100000000000000^3411 ≤ 43019776196077^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226978861 10000000000 43019776196077 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5396086153/10000000000 : ℝ), (-1975702033/10000000000 : ℝ), (5226978861/10000000000 : ℝ)] ![(22419068265533/50000000000000 : ℝ), (12142087265519/100000000000000 : ℝ), (43019776196077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5396086153/10000000000 : ℝ)|^4435 ≤ (22419068265533/50000000000000 : ℝ)^3411
        have hw : |(5396086153/10000000000 : ℝ)|=(5396086153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1975702033/10000000000 : ℝ)|^4435 ≤ (12142087265519/100000000000000 : ℝ)^3411
        have hw : |(-1975702033/10000000000 : ℝ)|=(1975702033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5226978861/10000000000 : ℝ)|^4435 ≤ (43019776196077/100000000000000 : ℝ)^3411
        have hw : |(5226978861/10000000000 : ℝ)|=(5226978861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_box_14 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079217241/2000000000 : ℝ)*x 0 + (2613489457/5000000000 : ℝ)*x 1 + (-493925473/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079217241/2000000000 : ℝ)^4435 ≤ (44838137092869/100000000000000 : ℝ)^3411 := by
    have hnat : (1079217241 : ℕ)^4435*100000000000000^3411 ≤ 44838137092869^3411*2000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079217241 2000000000 44838137092869 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2613489457/5000000000 : ℝ)^4435 ≤ (43019776763237/100000000000000 : ℝ)^3411 := by
    have hnat : (2613489457 : ℕ)^4435*100000000000000^3411 ≤ 43019776763237^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613489457 5000000000 43019776763237 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (493925473/2500000000 : ℝ)^4435 ≤ (12142086138833/100000000000000 : ℝ)^3411 := by
    have hnat : (493925473 : ℕ)^4435*100000000000000^3411 ≤ 12142086138833^3411*2500000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493925473 2500000000 12142086138833 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079217241/2000000000 : ℝ), (2613489457/5000000000 : ℝ), (-493925473/2500000000 : ℝ)] ![(44838137092869/100000000000000 : ℝ), (43019776763237/100000000000000 : ℝ), (12142086138833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079217241/2000000000 : ℝ)|^4435 ≤ (44838137092869/100000000000000 : ℝ)^3411
        have hw : |(1079217241/2000000000 : ℝ)|=(1079217241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2613489457/5000000000 : ℝ)|^4435 ≤ (43019776763237/100000000000000 : ℝ)^3411
        have hw : |(2613489457/5000000000 : ℝ)|=(2613489457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-493925473/2500000000 : ℝ)|^4435 ≤ (12142086138833/100000000000000 : ℝ)^3411
        have hw : |(-493925473/2500000000 : ℝ)|=(493925473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1469_box_15 (p : ℝ) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4044671731/10000000000 : ℝ)*x 0 + (220983881/500000000 : ℝ)*x 1 + (2209838741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4044671731/10000000000 : ℝ)^4435 ≤ (30822480662217/100000000000000 : ℝ)^3411 := by
    have hnat : (4044671731 : ℕ)^4435*100000000000000^3411 ≤ 30822480662217^3411*10000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4044671731 10000000000 30822480662217 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220983881/500000000 : ℝ)^4435 ≤ (8647190090937/25000000000000 : ℝ)^3411 := by
    have hnat : (220983881 : ℕ)^4435*25000000000000^3411 ≤ 8647190090937^3411*500000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220983881 500000000 8647190090937 25000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2209838741/5000000000 : ℝ)^4435 ≤ (34588758959527/100000000000000 : ℝ)^3411 := by
    have hnat : (2209838741 : ℕ)^4435*100000000000000^3411 ≤ 34588758959527^3411*5000000000^4435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209838741 5000000000 34588758959527 100000000000000 4435 3411 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4435/1024 : ℝ)) 4435 3411 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4044671731/10000000000 : ℝ), (220983881/500000000 : ℝ), (2209838741/5000000000 : ℝ)] ![(30822480662217/100000000000000 : ℝ), (8647190090937/25000000000000 : ℝ), (34588758959527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4044671731/10000000000 : ℝ)|^4435 ≤ (30822480662217/100000000000000 : ℝ)^3411
        have hw : |(4044671731/10000000000 : ℝ)|=(4044671731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(220983881/500000000 : ℝ)|^4435 ≤ (8647190090937/25000000000000 : ℝ)^3411
        have hw : |(220983881/500000000 : ℝ)|=(220983881/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2209838741/5000000000 : ℝ)|^4435 ≤ (34588758959527/100000000000000 : ℝ)^3411
        have hw : |(2209838741/5000000000 : ℝ)|=(2209838741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1469_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79976261/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (967/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10739/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63691/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58427/100000 : ℝ) ∧ (19961/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (85721/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (967/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10739/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (967/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10739/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (967/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10739/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (967/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10739/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (967/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10739/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (967/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10739/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10739/100000 : ℝ) ^ (4433/1024 : ℝ) ≤ (255272509173927/4000000000000000000 : ℝ) := by
    have hpowers : (10739/100000 : ℝ)^4433 ≤ (255272509173927/4000000000000000000 : ℝ)^1024 := by
      have hnat : (10739 : ℕ)^4433*4000000000000000000^1024 ≤ 255272509173927^1024*100000^4433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10739 100000 255272509173927 4000000000000000000 4433 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10739/100000 : ℝ)) (X := (255272509173927/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (967/6250 : ℝ) ^ (4433/1024 : ℝ) ≤ (3100732487430031/10000000000000000000 : ℝ) := by
    have hpowers : (967/6250 : ℝ)^4433 ≤ (3100732487430031/10000000000000000000 : ℝ)^1024 := by
      have hnat : (967 : ℕ)^4433*10000000000000000000^1024 ≤ 3100732487430031^1024*6250^4433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        967 6250 3100732487430031 10000000000000000000 4433 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (967/6250 : ℝ)) (X := (3100732487430031/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000255272509173927/2000000000000000000 : ℝ) ≤ (2500073704664397/2500000000000000 : ℝ) ^ (4433/1024 : ℝ) := by
    have hpowers : (2000255272509173927/2000000000000000000 : ℝ)^1024 ≤ (2500073704664397/2500000000000000 : ℝ)^4433 := by
      have hnat : (2000255272509173927 : ℕ)^1024*2500000000000000^4433 ≤ 2500073704664397^4433*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000255272509173927 2000000000000000000 2500073704664397 2500000000000000 1024 4433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500073704664397/2500000000000000 : ℝ)) (X := (2000255272509173927/2000000000000000000 : ℝ)) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007477827520729697/20000000000000000000 : ℝ) ≤ (80006908364353/80000000000000 : ℝ) ^ (4433/1024 : ℝ) := by
    have hpowers : (20007477827520729697/20000000000000000000 : ℝ)^1024 ≤ (80006908364353/80000000000000 : ℝ)^4433 := by
      have hnat : (20007477827520729697 : ℕ)^1024*80000000000000^4433 ≤ 80006908364353^4433*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007477827520729697 20000000000000000000 80006908364353 80000000000000 1024 4433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80006908364353/80000000000000 : ℝ)) (X := (20007477827520729697/20000000000000000000 : ℝ)) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003100732487430031/5000000000000000000 : ℝ) ≤ (5000716136215331/5000000000000000 : ℝ) ^ (4433/1024 : ℝ) := by
    have hpowers : (5003100732487430031/5000000000000000000 : ℝ)^1024 ≤ (5000716136215331/5000000000000000 : ℝ)^4433 := by
      have hnat : (5003100732487430031 : ℕ)^1024*5000000000000000^4433 ≤ 5000716136215331^4433*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003100732487430031 5000000000000000000 5000716136215331 5000000000000000 1024 4433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000716136215331/5000000000000000 : ℝ)) (X := (5003100732487430031/5000000000000000000 : ℝ)) (by norm_num) 4433 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(255272509173927/4000000000000000000 : ℝ) ≤ ((23659590130318661159/23665000000000000000 : ℝ)+2*(568726886537/473300000000000 : ℝ)*(10739/100000 : ℝ))^(4433/1024 : ℝ) := by
    rw [show (23659590130318661159/23665000000000000000 : ℝ)+2*(568726886537/473300000000000 : ℝ)*(10739/100000 : ℝ)=(2500073704664397/2500000000000000 : ℝ) by norm_num, show 1+2*(255272509173927/4000000000000000000 : ℝ)=(2000255272509173927/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3100732487430031/10000000000000000000 : ℝ)+(255272509173927/4000000000000000000 : ℝ) ≤ ((23659590130318661159/23665000000000000000 : ℝ)+(568726886537/473300000000000 : ℝ)*((967/6250 : ℝ)+(10739/100000 : ℝ)))^(4433/1024 : ℝ) := by
    rw [show (23659590130318661159/23665000000000000000 : ℝ)+(568726886537/473300000000000 : ℝ)*((967/6250 : ℝ)+(10739/100000 : ℝ))=(80006908364353/80000000000000 : ℝ) by norm_num, show 1+(3100732487430031/10000000000000000000 : ℝ)+(255272509173927/4000000000000000000 : ℝ)=(20007477827520729697/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3100732487430031/10000000000000000000 : ℝ) ≤ ((23659590130318661159/23665000000000000000 : ℝ)+2*(568726886537/473300000000000 : ℝ)*(967/6250 : ℝ))^(4433/1024 : ℝ) := by
    rw [show (23659590130318661159/23665000000000000000 : ℝ)+2*(568726886537/473300000000000 : ℝ)*(967/6250 : ℝ)=(5000716136215331/5000000000000000 : ℝ) by norm_num, show 1+2*(3100732487430031/10000000000000000000 : ℝ)=(5003100732487430031/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23659590130318661159/23665000000000000000 : ℝ)*(X 1 0+X 2 0)+(568726886537/473300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4433/1024 : ℝ)) (lo := (10739/100000 : ℝ)) (hi := (967/6250 : ℝ)) (c := (23659590130318661159/23665000000000000000 : ℝ)) (alpha := (568726886537/473300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23659590130318661159/23665000000000000000 : ℝ)*(X 0 1+X 2 1)+(568726886537/473300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4433/1024 : ℝ)) (lo := (10739/100000 : ℝ)) (hi := (967/6250 : ℝ)) (c := (23659590130318661159/23665000000000000000 : ℝ)) (alpha := (568726886537/473300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23659590130318661159/23665000000000000000 : ℝ)*(X 0 2+X 1 2)+(568726886537/473300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4433/1024 : ℝ)) (lo := (10739/100000 : ℝ)) (hi := (967/6250 : ℝ)) (c := (23659590130318661159/23665000000000000000 : ℝ)) (alpha := (568726886537/473300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1711813933/10000000000 : ℝ)*X 0 0+(1081499217/2000000000 : ℝ)*X 0 1+(2703747587/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5269982871/10000000000 : ℝ)*X 1 0+(-1902195009/10000000000 : ℝ)*X 1 1+(2703747707/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((263499159/500000000 : ℝ)*X 2 0+(2703747577/5000000000 : ℝ)*X 2 1+(-1902194947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((280962281/625000000 : ℝ)*X 0 0+(838983743/2000000000 : ℝ)*X 0 1+(4194918957/10000000000 : ℝ)*X 0 2+(280962281/625000000 : ℝ)*X 1 0+(838983743/2000000000 : ℝ)*X 1 1+(4194918957/10000000000 : ℝ)*X 1 2+(280962281/625000000 : ℝ)*X 2 0+(838983743/2000000000 : ℝ)*X 2 1+(4194918957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2160588749/10000000000 : ℝ)*X 0 0+(5241955331/10000000000 : ℝ)*X 0 1+(5241955839/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5385625569/10000000000 : ℝ)*X 1 0+(-196977313/1000000000 : ℝ)*X 1 1+(5241955603/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((269281299/500000000 : ℝ)*X 2 0+(2620977749/5000000000 : ℝ)*X 2 1+(-393954543/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1020713733/2500000000 : ℝ)*X 0 0+(880209819/2000000000 : ℝ)*X 0 1+(4401049599/10000000000 : ℝ)*X 0 2+(1020713733/2500000000 : ℝ)*X 1 0+(880209819/2000000000 : ℝ)*X 1 1+(4401049599/10000000000 : ℝ)*X 1 2+(1020713733/2500000000 : ℝ)*X 2 0+(880209819/2000000000 : ℝ)*X 2 1+(4401049599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2066006349/10000000000 : ℝ)*X 0 0+(2563238703/5000000000 : ℝ)*X 0 1+(339254439/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5255600831/10000000000 : ℝ)*X 1 0+(-236692219/1250000000 : ℝ)*X 1 1+(542807127/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((328475137/625000000 : ℝ)*X 2 0+(5428070277/10000000000 : ℝ)*X 2 1+(-378707453/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1136378573/2500000000 : ℝ)*X 0 0+(4169267321/10000000000 : ℝ)*X 0 1+(833853651/2000000000 : ℝ)*X 0 2+(1136378573/2500000000 : ℝ)*X 1 0+(4169267321/10000000000 : ℝ)*X 1 1+(833853651/2000000000 : ℝ)*X 1 2+(1136378573/2500000000 : ℝ)*X 2 0+(4169267321/10000000000 : ℝ)*X 2 1+(833853651/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-56456079/312500000 : ℝ)*X 0 0+(5519100923/10000000000 : ℝ)*X 0 1+(5226978861/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5396086153/10000000000 : ℝ)*X 1 0+(-1975702033/10000000000 : ℝ)*X 1 1+(5226978861/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1079217241/2000000000 : ℝ)*X 2 0+(2613489457/5000000000 : ℝ)*X 2 1+(-493925473/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4044671731/10000000000 : ℝ)*X 0 0+(220983881/500000000 : ℝ)*X 0 1+(2209838741/5000000000 : ℝ)*X 0 2+(4044671731/10000000000 : ℝ)*X 1 0+(220983881/500000000 : ℝ)*X 1 1+(2209838741/5000000000 : ℝ)*X 1 2+(4044671731/10000000000 : ℝ)*X 2 0+(220983881/500000000 : ℝ)*X 2 1+(2209838741/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1469_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63691/100000 : ℝ) ≤ (-15071985389372909313712515231/23665000000000000000000000000 : ℝ) := by norm_num
    linear_combination (170001/800000000000 : ℝ)*(lower1) + (34927201/25000000000000 : ℝ)*(lower2) + (37985223/20000000000000 : ℝ)*(lower3) + (25247559/50000000000000 : ℝ)*(lower4) + (2159148993933829/100000000000000 : ℝ)*(major0) + (2159148993933829/100000000000000 : ℝ)*(major1) + (2159148993933829/100000000000000 : ℝ)*(major2) + (2919588821761/97656250000 : ℝ)*(sp4) + (1494796719270189/50000000000000 : ℝ)*(sp5) + (298962561657229/10000000000000 : ℝ)*(sp6) + (1349788967711867/100000000000000 : ℝ)*(sp7) + (32757471443/50000000000000 : ℝ)*(sp13) + (16668455487/50000000000000 : ℝ)*(sp14) + (39855076787/50000000000000 : ℝ)*(sp15) + (1349868677865441/100000000000000 : ℝ)*(f.failure) + (2919588821761/97656250000 : ℝ)*(f.sum) + (104322007890657/23665000000000000000000000000 : ℝ)*base66 + (243554251398597811/2366500000000000000000000000000000 : ℝ)*base67 + (13484952105223402189/2366500000000000000000000000000000 : ℝ)*base70 + (22512408372459902189/2366500000000000000000000000000000 : ℝ)*base72 + (10618739048809/11832500000000000000000000000 : ℝ)*base73 + (9636717754690597811/2366500000000000000000000000000000 : ℝ)*base75 + (13426054679254902189/2366500000000000000000000000000000 : ℝ)*base78 + (5617704719710597811/2366500000000000000000000000000000 : ℝ)*base79 + (1742531427211/11832500000000000000000000000 : ℝ)*base82 + (17703899/5000000000000000000000 : ℝ)*base90 + (17703899/5000000000000000000000 : ℝ)*base92 + (17703899/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58427/100000 : ℝ) ≤ (691361585879760822902596422384843/1183250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2025923/2500000000000 : ℝ)*(upper0) + (4754199/25000000000000 : ℝ)*(upper3) + (15652749/20000000000000 : ℝ)*(upper4) + (2232488330747947/100000000000000 : ℝ)*(major0) + (2232488330747947/100000000000000 : ℝ)*(major1) + (2232488330747947/100000000000000 : ℝ)*(major2) + (1524886590501813/50000000000000 : ℝ)*(sp0) + (3049778639111967/100000000000000 : ℝ)*(sp1) + (3049780020478511/100000000000000 : ℝ)*(sp2) + (139571837532813/10000000000000 : ℝ)*(sp3) + (2307566413/100000000000000 : ℝ)*(sp5) + (926199869/100000000000000 : ℝ)*(sp6) + (993665593/100000000000000 : ℝ)*(sp7) + (3882837377/50000000000000 : ℝ)*(sp8) + (348929842248431/25000000000000 : ℝ)*(f.failure) + (152489047333919/5000000000000 : ℝ)*(f.sum) + (81390107580459/23665000000000000000000000000 : ℝ)*base65 + (17754898471241340573/2366500000000000000000000000000000 : ℝ)*base67 + (4692095309144340573/2366500000000000000000000000000000 : ℝ)*base69 + (7820178143339840573/2366500000000000000000000000000000 : ℝ)*base71 + (267796166555359/23665000000000000000000000000 : ℝ)*base73 + (3656154356303840573/2366500000000000000000000000000000 : ℝ)*base75 + (907843809530840573/2366500000000000000000000000000000 : ℝ)*base77 + (37033228358028340573/2366500000000000000000000000000000 : ℝ)*base79 + (30538078233407/11832500000000000000000000000 : ℝ)*base81 + (6996491/1250000000000000000000 : ℝ)*base89 + (6996491/1250000000000000000000 : ℝ)*base91 + (6996491/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (19961/25000 : ℝ) ≤ (944780325353987960225503501903821/1183250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11291437/12500000000000 : ℝ)*(upper0) + (342489891/100000000000000 : ℝ)*(lower3) + (23630647/10000000000000 : ℝ)*(upper4) + (2431126158619927/100000000000000 : ℝ)*(major0) + (2431126158619927/100000000000000 : ℝ)*(major1) + (2431126158619927/100000000000000 : ℝ)*(major2) + (14543092621/6250000000000 : ℝ)*(sp1) + (83228135817/100000000000000 : ℝ)*(sp2) + (2591584631/6250000000000 : ℝ)*(sp3) + (735050549/25000000000000 : ℝ)*(sp4) + (828932277628827/25000000000000 : ℝ)*(sp8) + (207218710077223/6250000000000 : ℝ)*(sp9) + (3315648822581687/100000000000000 : ℝ)*(sp10) + (759931698276159/50000000000000 : ℝ)*(sp11) + (759952430953207/50000000000000 : ℝ)*(f.failure) + (51808313292461/1562500000000 : ℝ)*(f.sum) + (152021097712759/23665000000000000000000000000 : ℝ)*base65 + (6300272180374734607/2366500000000000000000000000000000 : ℝ)*base68 + (6000853503548734607/2366500000000000000000000000000000 : ℝ)*base70 + (17336313031674265393/2366500000000000000000000000000000 : ℝ)*base71 + (10303411293729/23665000000000000000000000000 : ℝ)*base73 + (879236382689265393/2366500000000000000000000000000000 : ℝ)*base75 + (1503621765124265393/2366500000000000000000000000000000 : ℝ)*base77 + (18615872247890765393/2366500000000000000000000000000000 : ℝ)*base79 + (42123511100479/23665000000000000000000000000 : ℝ)*base81 + (13180973/2500000000000000000000 : ℝ)*base90 + (13180973/2500000000000000000000 : ℝ)*base92 + (13180973/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-85721/100000 : ℝ) ≤ (-3961959527889923688588994329933/4622070312500000000000000000000 : ℝ) := by norm_num
    linear_combination (3127757/6250000000000 : ℝ)*(lower2) + (25500469/50000000000000 : ℝ)*(upper3) + (59691873/100000000000000 : ℝ)*(upper5) + (77161605335081/3125000000000 : ℝ)*(major0) + (77161605335081/3125000000000 : ℝ)*(major1) + (77161605335081/3125000000000 : ℝ)*(major2) + (28055953/100000000000000 : ℝ)*(sp0) + (6878317601/20000000000000 : ℝ)*(sp5) + (713611691/20000000000000 : ℝ)*(sp6) + (19572041439/100000000000000 : ℝ)*(sp7) + (13692901193953/400000000000 : ℝ)*(sp12) + (855797733739049/25000000000000 : ℝ)*(sp13) + (1711610879242873/50000000000000 : ℝ)*(sp14) + (1543670605424217/100000000000000 : ℝ)*(sp15) + (192961272183207/12500000000000 : ℝ)*(f.failure) + (1711612663272101/50000000000000 : ℝ)*(f.sum) + (47752430487307/11832500000000000000000000000 : ℝ)*base65 + (786243833999081121/73953125000000000000000000000000 : ℝ)*base68 + (75115344021027531/4622070312500000000000000000000 : ℝ)*base70 + (257140329900081121/73953125000000000000000000000000 : ℝ)*base72 + (12891020403449/23665000000000000000000000000 : ℝ)*base73 + (674852629154674871/73953125000000000000000000000000 : ℝ)*base76 + (52677286346923373/36976562500000000000000000000000 : ℝ)*base78 + (70768480303313249/18488281250000000000000000000000 : ℝ)*base80 + (24691816147883/11832500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2849027/625000000000000000000 : ℝ)*base89 + (2849027/625000000000000000000 : ℝ)*base91 + (2849027/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1469_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79976261/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (967/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10739/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63691/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58427/100000 : ℝ) else (19961/25000 : ℝ) ≤ X j i ∧ X j i ≤ (85721/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1469_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1469_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79976261/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10737/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63691/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58427/100000 : ℝ) else (19961/25000 : ℝ) ≤ X j i ∧ X j i ≤ (85721/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1469_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1469_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1469_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4433/1024 : ℝ) ≤ p) (hpb : p ≤ (4435/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79976261/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10737/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63691/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58427/100000 : ℝ) else (19961/25000 : ℝ) ≤ X j i ∧ X j i ≤ (85721/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1469_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
