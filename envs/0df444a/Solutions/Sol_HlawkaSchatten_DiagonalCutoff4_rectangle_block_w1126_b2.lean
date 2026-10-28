-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1126_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:11:47.479438+00:00
-- url     : https://prove2.me/submissions/7167dc70-ffaa-48db-8dbb-27b175d742ec

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
theorem support_rectangle_w1126_s6_0 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2174527309/10000000000 : ℝ)*x 0 + (1348424723/2500000000 : ℝ)*x 1 + (5265122461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174527309/10000000000 : ℝ)^8319 ≤ (6605865260727/50000000000000 : ℝ)^6271 := by
    have hnat : (2174527309 : ℕ)^8319*50000000000000^6271 ≤ 6605865260727^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174527309 10000000000 6605865260727 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348424723/2500000000 : ℝ)^8319 ≤ (5511065206639/12500000000000 : ℝ)^6271 := by
    have hnat : (1348424723 : ℕ)^8319*12500000000000^6271 ≤ 5511065206639^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348424723 2500000000 5511065206639 12500000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265122461/10000000000 : ℝ)^8319 ≤ (42699747805597/100000000000000 : ℝ)^6271 := by
    have hnat : (5265122461 : ℕ)^8319*100000000000000^6271 ≤ 42699747805597^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265122461 10000000000 42699747805597 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2174527309/10000000000 : ℝ), (1348424723/2500000000 : ℝ), (5265122461/10000000000 : ℝ)] ![(6605865260727/50000000000000 : ℝ), (5511065206639/12500000000000 : ℝ), (42699747805597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2174527309/10000000000 : ℝ)|^8319 ≤ (6605865260727/50000000000000 : ℝ)^6271
        have hw : |(-2174527309/10000000000 : ℝ)|=(2174527309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348424723/2500000000 : ℝ)|^8319 ≤ (5511065206639/12500000000000 : ℝ)^6271
        have hw : |(1348424723/2500000000 : ℝ)|=(1348424723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265122461/10000000000 : ℝ)|^8319 ≤ (42699747805597/100000000000000 : ℝ)^6271
        have hw : |(5265122461/10000000000 : ℝ)|=(5265122461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s6_1 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344909511/10000000000 : ℝ)*x 0 + (-1119876459/5000000000 : ℝ)*x 1 + (5265122461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344909511/10000000000 : ℝ)^8319 ≤ (8712050512063/20000000000000 : ℝ)^6271 := by
    have hnat : (5344909511 : ℕ)^8319*20000000000000^6271 ≤ 8712050512063^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344909511 10000000000 8712050512063 20000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119876459/5000000000 : ℝ)^8319 ≤ (13739999612019/100000000000000 : ℝ)^6271 := by
    have hnat : (1119876459 : ℕ)^8319*100000000000000^6271 ≤ 13739999612019^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119876459 5000000000 13739999612019 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265122461/10000000000 : ℝ)^8319 ≤ (42699747805597/100000000000000 : ℝ)^6271 := by
    have hnat : (5265122461 : ℕ)^8319*100000000000000^6271 ≤ 42699747805597^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265122461 10000000000 42699747805597 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344909511/10000000000 : ℝ), (-1119876459/5000000000 : ℝ), (5265122461/10000000000 : ℝ)] ![(8712050512063/20000000000000 : ℝ), (13739999612019/100000000000000 : ℝ), (42699747805597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344909511/10000000000 : ℝ)|^8319 ≤ (8712050512063/20000000000000 : ℝ)^6271
        have hw : |(5344909511/10000000000 : ℝ)|=(5344909511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1119876459/5000000000 : ℝ)|^8319 ≤ (13739999612019/100000000000000 : ℝ)^6271
        have hw : |(-1119876459/5000000000 : ℝ)|=(1119876459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265122461/10000000000 : ℝ)|^8319 ≤ (42699747805597/100000000000000 : ℝ)^6271
        have hw : |(5265122461/10000000000 : ℝ)|=(5265122461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s6_2 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344909511/10000000000 : ℝ)*x 0 + (5265122461/10000000000 : ℝ)*x 1 + (-1119876459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344909511/10000000000 : ℝ)^8319 ≤ (8712050512063/20000000000000 : ℝ)^6271 := by
    have hnat : (5344909511 : ℕ)^8319*20000000000000^6271 ≤ 8712050512063^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344909511 10000000000 8712050512063 20000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265122461/10000000000 : ℝ)^8319 ≤ (42699747805597/100000000000000 : ℝ)^6271 := by
    have hnat : (5265122461 : ℕ)^8319*100000000000000^6271 ≤ 42699747805597^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265122461 10000000000 42699747805597 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119876459/5000000000 : ℝ)^8319 ≤ (13739999612019/100000000000000 : ℝ)^6271 := by
    have hnat : (1119876459 : ℕ)^8319*100000000000000^6271 ≤ 13739999612019^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119876459 5000000000 13739999612019 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344909511/10000000000 : ℝ), (5265122461/10000000000 : ℝ), (-1119876459/5000000000 : ℝ)] ![(8712050512063/20000000000000 : ℝ), (42699747805597/100000000000000 : ℝ), (13739999612019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344909511/10000000000 : ℝ)|^8319 ≤ (8712050512063/20000000000000 : ℝ)^6271
        have hw : |(5344909511/10000000000 : ℝ)|=(5344909511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265122461/10000000000 : ℝ)|^8319 ≤ (42699747805597/100000000000000 : ℝ)^6271
        have hw : |(5265122461/10000000000 : ℝ)|=(5265122461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1119876459/5000000000 : ℝ)|^8319 ≤ (13739999612019/100000000000000 : ℝ)^6271
        have hw : |(-1119876459/5000000000 : ℝ)|=(1119876459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s6_3 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4366913371/10000000000 : ℝ)*x 0 + (1060318491/2500000000 : ℝ)*x 1 + (4496270917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366913371/10000000000 : ℝ)^8319 ≤ (1665834411343/5000000000000 : ℝ)^6271 := by
    have hnat : (4366913371 : ℕ)^8319*5000000000000^6271 ≤ 1665834411343^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366913371 10000000000 1665834411343 5000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060318491/2500000000 : ℝ)^8319 ≤ (32051110222071/100000000000000 : ℝ)^6271 := by
    have hnat : (1060318491 : ℕ)^8319*100000000000000^6271 ≤ 32051110222071^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060318491 2500000000 32051110222071 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4496270917/10000000000 : ℝ)^8319 ≤ (865805038441/2500000000000 : ℝ)^6271 := by
    have hnat : (4496270917 : ℕ)^8319*2500000000000^6271 ≤ 865805038441^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496270917 10000000000 865805038441 2500000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366913371/10000000000 : ℝ), (1060318491/2500000000 : ℝ), (4496270917/10000000000 : ℝ)] ![(1665834411343/5000000000000 : ℝ), (32051110222071/100000000000000 : ℝ), (865805038441/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366913371/10000000000 : ℝ)|^8319 ≤ (1665834411343/5000000000000 : ℝ)^6271
        have hw : |(4366913371/10000000000 : ℝ)|=(4366913371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060318491/2500000000 : ℝ)|^8319 ≤ (32051110222071/100000000000000 : ℝ)^6271
        have hw : |(1060318491/2500000000 : ℝ)|=(1060318491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4496270917/10000000000 : ℝ)|^8319 ≤ (865805038441/2500000000000 : ℝ)^6271
        have hw : |(4496270917/10000000000 : ℝ)|=(4496270917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s6_4 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2174532311/10000000000 : ℝ)*x 0 + (1316361791/2500000000 : ℝ)*x 1 + (2696686507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174532311/10000000000 : ℝ)^8319 ≤ (3302942709261/25000000000000 : ℝ)^6271 := by
    have hnat : (2174532311 : ℕ)^8319*25000000000000^6271 ≤ 3302942709261^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174532311 10000000000 3302942709261 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316361791/2500000000 : ℝ)^8319 ≤ (8540648230687/20000000000000 : ℝ)^6271 := by
    have hnat : (1316361791 : ℕ)^8319*20000000000000^6271 ≤ 8540648230687^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316361791 2500000000 8540648230687 20000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696686507/5000000000 : ℝ)^8319 ≤ (2755311749997/6250000000000 : ℝ)^6271 := by
    have hnat : (2696686507 : ℕ)^8319*6250000000000^6271 ≤ 2755311749997^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696686507 5000000000 2755311749997 6250000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2174532311/10000000000 : ℝ), (1316361791/2500000000 : ℝ), (2696686507/5000000000 : ℝ)] ![(3302942709261/25000000000000 : ℝ), (8540648230687/20000000000000 : ℝ), (2755311749997/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2174532311/10000000000 : ℝ)|^8319 ≤ (3302942709261/25000000000000 : ℝ)^6271
        have hw : |(-2174532311/10000000000 : ℝ)|=(2174532311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316361791/2500000000 : ℝ)|^8319 ≤ (8540648230687/20000000000000 : ℝ)^6271
        have hw : |(1316361791/2500000000 : ℝ)|=(1316361791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696686507/5000000000 : ℝ)|^8319 ≤ (2755311749997/6250000000000 : ℝ)^6271
        have hw : |(2696686507/5000000000 : ℝ)|=(2696686507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s6_5 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656186509/5000000000 : ℝ)*x 0 + (-422300473/2000000000 : ℝ)*x 1 + (1078674603/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656186509/5000000000 : ℝ)^8319 ≤ (10802208925247/25000000000000 : ℝ)^6271 := by
    have hnat : (2656186509 : ℕ)^8319*25000000000000^6271 ≤ 10802208925247^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656186509 5000000000 10802208925247 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422300473/2000000000 : ℝ)^8319 ≤ (12706176280449/100000000000000 : ℝ)^6271 := by
    have hnat : (422300473 : ℕ)^8319*100000000000000^6271 ≤ 12706176280449^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422300473 2000000000 12706176280449 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078674603/2000000000 : ℝ)^8319 ≤ (11021247002699/25000000000000 : ℝ)^6271 := by
    have hnat : (1078674603 : ℕ)^8319*25000000000000^6271 ≤ 11021247002699^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078674603 2000000000 11021247002699 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656186509/5000000000 : ℝ), (-422300473/2000000000 : ℝ), (1078674603/2000000000 : ℝ)] ![(10802208925247/25000000000000 : ℝ), (12706176280449/100000000000000 : ℝ), (11021247002699/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656186509/5000000000 : ℝ)|^8319 ≤ (10802208925247/25000000000000 : ℝ)^6271
        have hw : |(2656186509/5000000000 : ℝ)|=(2656186509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-422300473/2000000000 : ℝ)|^8319 ≤ (12706176280449/100000000000000 : ℝ)^6271
        have hw : |(-422300473/2000000000 : ℝ)|=(422300473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078674603/2000000000 : ℝ)|^8319 ≤ (11021247002699/25000000000000 : ℝ)^6271
        have hw : |(1078674603/2000000000 : ℝ)|=(1078674603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s6_6 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664046627/1250000000 : ℝ)*x 0 + (2696686511/5000000000 : ℝ)*x 1 + (-2111502357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664046627/1250000000 : ℝ)^8319 ≤ (2700552229963/6250000000000 : ℝ)^6271 := by
    have hnat : (664046627 : ℕ)^8319*6250000000000^6271 ≤ 2700552229963^6271*1250000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664046627 1250000000 2700552229963 6250000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696686511/5000000000 : ℝ)^8319 ≤ (44084988086699/100000000000000 : ℝ)^6271 := by
    have hnat : (2696686511 : ℕ)^8319*100000000000000^6271 ≤ 44084988086699^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696686511 5000000000 44084988086699 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111502357/10000000000 : ℝ)^8319 ≤ (6353088108293/50000000000000 : ℝ)^6271 := by
    have hnat : (2111502357 : ℕ)^8319*50000000000000^6271 ≤ 6353088108293^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111502357 10000000000 6353088108293 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664046627/1250000000 : ℝ), (2696686511/5000000000 : ℝ), (-2111502357/10000000000 : ℝ)] ![(2700552229963/6250000000000 : ℝ), (44084988086699/100000000000000 : ℝ), (6353088108293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664046627/1250000000 : ℝ)|^8319 ≤ (2700552229963/6250000000000 : ℝ)^6271
        have hw : |(664046627/1250000000 : ℝ)|=(664046627/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696686511/5000000000 : ℝ)|^8319 ≤ (44084988086699/100000000000000 : ℝ)^6271
        have hw : |(2696686511/5000000000 : ℝ)|=(2696686511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2111502357/10000000000 : ℝ)|^8319 ≤ (6353088108293/50000000000000 : ℝ)^6271
        have hw : |(-2111502357/10000000000 : ℝ)|=(2111502357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s6_7 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2183461651/5000000000 : ℝ)*x 0 + (561953371/1250000000 : ℝ)*x 1 + (4241920251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183461651/5000000000 : ℝ)^8319 ≤ (33316788738119/100000000000000 : ℝ)^6271 := by
    have hnat : (2183461651 : ℕ)^8319*100000000000000^6271 ≤ 33316788738119^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183461651 5000000000 33316788738119 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561953371/1250000000 : ℝ)^8319 ≤ (4328202735053/12500000000000 : ℝ)^6271 := by
    have hnat : (561953371 : ℕ)^8319*12500000000000^6271 ≤ 4328202735053^6271*1250000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561953371 1250000000 4328202735053 12500000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4241920251/10000000000 : ℝ)^8319 ≤ (8014397340281/25000000000000 : ℝ)^6271 := by
    have hnat : (4241920251 : ℕ)^8319*25000000000000^6271 ≤ 8014397340281^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241920251 10000000000 8014397340281 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183461651/5000000000 : ℝ), (561953371/1250000000 : ℝ), (4241920251/10000000000 : ℝ)] ![(33316788738119/100000000000000 : ℝ), (4328202735053/12500000000000 : ℝ), (8014397340281/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183461651/5000000000 : ℝ)|^8319 ≤ (33316788738119/100000000000000 : ℝ)^6271
        have hw : |(2183461651/5000000000 : ℝ)|=(2183461651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561953371/1250000000 : ℝ)|^8319 ≤ (4328202735053/12500000000000 : ℝ)^6271
        have hw : |(561953371/1250000000 : ℝ)|=(561953371/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4241920251/10000000000 : ℝ)|^8319 ≤ (8014397340281/25000000000000 : ℝ)^6271
        have hw : |(4241920251/10000000000 : ℝ)|=(4241920251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1126_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2831/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (439/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7041/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2823/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7041/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2823/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7041/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2823/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7041/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2823/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7041/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2823/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7041/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2823/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2823/25000 : ℝ) ^ (4159/1024 : ℝ) ≤ (568678326899793/4000000000000000000 : ℝ) := by
    have hpowers : (2823/25000 : ℝ)^4159 ≤ (568678326899793/4000000000000000000 : ℝ)^1024 := by
      have hnat : (2823 : ℕ)^4159*4000000000000000000^1024 ≤ 568678326899793^1024*25000^4159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2823 25000 568678326899793 4000000000000000000 4159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2823/25000 : ℝ)) (X := (568678326899793/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7041/50000 : ℝ) ^ (4159/1024 : ℝ) ≤ (348562180425097/1000000000000000000 : ℝ) := by
    have hpowers : (7041/50000 : ℝ)^4159 ≤ (348562180425097/1000000000000000000 : ℝ)^1024 := by
      have hnat : (7041 : ℕ)^4159*1000000000000000000^1024 ≤ 348562180425097^1024*50000^4159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7041 50000 348562180425097 1000000000000000000 4159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7041/50000 : ℝ)) (X := (348562180425097/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000568678326899793/2000000000000000000 : ℝ) ≤ (1250087500632927/1250000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (2000568678326899793/2000000000000000000 : ℝ)^1024 ≤ (1250087500632927/1250000000000000 : ℝ)^4159 := by
      have hnat : (2000568678326899793 : ℕ)^1024*1250000000000000^4159 ≤ 1250087500632927^4159*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000568678326899793 2000000000000000000 1250087500632927 1250000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250087500632927/1250000000000000 : ℝ)) (X := (2000568678326899793/2000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001962927048600181/4000000000000000000 : ℝ) ≤ (1250151002768149/1250000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (4001962927048600181/4000000000000000000 : ℝ)^1024 ≤ (1250151002768149/1250000000000000 : ℝ)^4159 := by
      have hnat : (4001962927048600181 : ℕ)^1024*1250000000000000^4159 ≤ 1250151002768149^4159*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001962927048600181 4000000000000000000 1250151002768149 1250000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250151002768149/1250000000000000 : ℝ)) (X := (4001962927048600181/4000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (500348562180425097/500000000000000000 : ℝ) ≤ (1250214504903371/1250000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (500348562180425097/500000000000000000 : ℝ)^1024 ≤ (1250214504903371/1250000000000000 : ℝ)^4159 := by
      have hnat : (500348562180425097 : ℕ)^1024*1250000000000000^4159 ≤ 1250214504903371^4159*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500348562180425097 500000000000000000 1250214504903371 1250000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250214504903371/1250000000000000 : ℝ)) (X := (500348562180425097/500000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(568678326899793/4000000000000000000 : ℝ) ≤ ((581051665757335447/581250000000000000 : ℝ)+2*(31751067611/17437500000000 : ℝ)*(2823/25000 : ℝ))^(4159/1024 : ℝ) := by
    rw [show (581051665757335447/581250000000000000 : ℝ)+2*(31751067611/17437500000000 : ℝ)*(2823/25000 : ℝ)=(1250087500632927/1250000000000000 : ℝ) by norm_num, show 1+2*(568678326899793/4000000000000000000 : ℝ)=(2000568678326899793/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(348562180425097/1000000000000000000 : ℝ)+(568678326899793/4000000000000000000 : ℝ) ≤ ((581051665757335447/581250000000000000 : ℝ)+(31751067611/17437500000000 : ℝ)*((7041/50000 : ℝ)+(2823/25000 : ℝ)))^(4159/1024 : ℝ) := by
    rw [show (581051665757335447/581250000000000000 : ℝ)+(31751067611/17437500000000 : ℝ)*((7041/50000 : ℝ)+(2823/25000 : ℝ))=(1250151002768149/1250000000000000 : ℝ) by norm_num, show 1+(348562180425097/1000000000000000000 : ℝ)+(568678326899793/4000000000000000000 : ℝ)=(4001962927048600181/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(348562180425097/1000000000000000000 : ℝ) ≤ ((581051665757335447/581250000000000000 : ℝ)+2*(31751067611/17437500000000 : ℝ)*(7041/50000 : ℝ))^(4159/1024 : ℝ) := by
    rw [show (581051665757335447/581250000000000000 : ℝ)+2*(31751067611/17437500000000 : ℝ)*(7041/50000 : ℝ)=(1250214504903371/1250000000000000 : ℝ) by norm_num, show 1+2*(348562180425097/1000000000000000000 : ℝ)=(500348562180425097/500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (581051665757335447/581250000000000000 : ℝ)*(X 1 0+X 2 0)+(31751067611/17437500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (2823/25000 : ℝ)) (hi := (7041/50000 : ℝ)) (c := (581051665757335447/581250000000000000 : ℝ)) (alpha := (31751067611/17437500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (581051665757335447/581250000000000000 : ℝ)*(X 0 1+X 2 1)+(31751067611/17437500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (2823/25000 : ℝ)) (hi := (7041/50000 : ℝ)) (c := (581051665757335447/581250000000000000 : ℝ)) (alpha := (31751067611/17437500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (581051665757335447/581250000000000000 : ℝ)*(X 0 2+X 1 2)+(31751067611/17437500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (2823/25000 : ℝ)) (hi := (7041/50000 : ℝ)) (c := (581051665757335447/581250000000000000 : ℝ)) (alpha := (31751067611/17437500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2174527309/10000000000 : ℝ)*X 0 0+(1348424723/2500000000 : ℝ)*X 0 1+(5265122461/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344909511/10000000000 : ℝ)*X 1 0+(-1119876459/5000000000 : ℝ)*X 1 1+(5265122461/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344909511/10000000000 : ℝ)*X 2 0+(5265122461/10000000000 : ℝ)*X 2 1+(-1119876459/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4366913371/10000000000 : ℝ)*X 0 0+(1060318491/2500000000 : ℝ)*X 0 1+(4496270917/10000000000 : ℝ)*X 0 2+(4366913371/10000000000 : ℝ)*X 1 0+(1060318491/2500000000 : ℝ)*X 1 1+(4496270917/10000000000 : ℝ)*X 1 2+(4366913371/10000000000 : ℝ)*X 2 0+(1060318491/2500000000 : ℝ)*X 2 1+(4496270917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2174532311/10000000000 : ℝ)*X 0 0+(1316361791/2500000000 : ℝ)*X 0 1+(2696686507/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656186509/5000000000 : ℝ)*X 1 0+(-422300473/2000000000 : ℝ)*X 1 1+(1078674603/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664046627/1250000000 : ℝ)*X 2 0+(2696686511/5000000000 : ℝ)*X 2 1+(-2111502357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2183461651/5000000000 : ℝ)*X 0 0+(561953371/1250000000 : ℝ)*X 0 1+(4241920251/10000000000 : ℝ)*X 0 2+(2183461651/5000000000 : ℝ)*X 1 0+(561953371/1250000000 : ℝ)*X 1 1+(4241920251/10000000000 : ℝ)*X 1 2+(2183461651/5000000000 : ℝ)*X 2 0+(561953371/1250000000 : ℝ)*X 2 1+(4241920251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (488187661607139695966249/46875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16543817/800000000000 : ℝ)*(base19) + (481348799/25000000000000 : ℝ)*(base23) + (60967/80000000000 : ℝ)*(lower2) + (263792023/100000000000000 : ℝ)*(upper3) + (158063149/100000000000000 : ℝ)*(upper5) + (146240787760321/2500000000000 : ℝ)*(major0) + (146240787760321/2500000000000 : ℝ)*(major1) + (146240787760321/2500000000000 : ℝ)*(major2) + (1555506728550181/20000000000000 : ℝ)*(sp0) + (3888793676928219/50000000000000 : ℝ)*(sp1) + (243049609263699/3125000000000 : ℝ)*(sp2) + (196082142274469/5000000000000 : ℝ)*(sp3) + (55779082659/100000000000000 : ℝ)*(sp4) + (15203173529/50000000000000 : ℝ)*(sp7) + (1960836625918219/50000000000000 : ℝ)*(f.failure) + (1944397355458391/25000000000000 : ℝ)*(f.sum) + (1451376146453/697500000000000000000000000 : ℝ)*base66 + (32224555986704539/4359375000000000000000000000000 : ℝ)*base68 + (4121349837656957/2179687500000000000000000000000 : ℝ)*base70 + (58908882366326711/4359375000000000000000000000000 : ℝ)*base71 + (2428840252429/348750000000000000000000000 : ℝ)*base74 + (44049352548329539/4359375000000000000000000000000 : ℝ)*base76 + (1048811511329539/4359375000000000000000000000000 : ℝ)*base78 + (38220254268704539/4359375000000000000000000000000 : ℝ)*base80 + (4770143427623/697500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (4653457/625000000000000000000 : ℝ)*base89 + (4653457/625000000000000000000 : ℝ)*base91 + (4653457/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (105156785701437349451873213/14531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (82134701/6250000000000 : ℝ)*(base19) + (1441608831/100000000000000 : ℝ)*(base23) + (9125071/6250000000000 : ℝ)*(upper3) + (574591/1000000000000 : ℝ)*(lower4) + (71684873/50000000000000 : ℝ)*(upper5) + (2939646409583281/50000000000000 : ℝ)*(major0) + (2939646409583281/50000000000000 : ℝ)*(major1) + (2939646409583281/50000000000000 : ℝ)*(major2) + (1435199587/4000000000000 : ℝ)*(sp1) + (19755250579/50000000000000 : ℝ)*(sp2) + (977128349597683/12500000000000 : ℝ)*(sp4) + (7816989602636573/100000000000000 : ℝ)*(sp5) + (1954246461167869/25000000000000 : ℝ)*(sp6) + (3941558600331787/100000000000000 : ℝ)*(sp7) + (3941558600331787/100000000000000 : ℝ)*(f.failure) + (977128349597683/12500000000000 : ℝ)*(f.sum) + (10916265365653/3487500000000000000000000000 : ℝ)*base65 + (1218441116058815179/87187500000000000000000000000000 : ℝ)*base68 + (553543235671002679/87187500000000000000000000000000 : ℝ)*base70 + (43143763958502679/87187500000000000000000000000000 : ℝ)*base72 + (30905427884419/6975000000000000000000000000 : ℝ)*base74 + (27615617372877679/87187500000000000000000000000000 : ℝ)*base76 + (17294336797565179/87187500000000000000000000000000 : ℝ)*base78 + (1176334977841940179/87187500000000000000000000000000 : ℝ)*base80 + (2922115275919/6975000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (10967761/1250000000000000000000 : ℝ)*base89 + (10967761/1250000000000000000000 : ℝ)*base91 + (10967761/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1126_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2831/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (439/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1126_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1126_s7_0 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-271819811/1250000000 : ℝ)*x 0 + (539335697/1000000000 : ℝ)*x 1 + (5265443723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271819811/1250000000 : ℝ)^8319 ≤ (13211981821381/100000000000000 : ℝ)^6271 := by
    have hnat : (271819811 : ℕ)^8319*100000000000000^6271 ≤ 13211981821381^6271*1250000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271819811 1250000000 13211981821381 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539335697/1000000000 : ℝ)^8319 ≤ (22042407014441/50000000000000 : ℝ)^6271 := by
    have hnat : (539335697 : ℕ)^8319*50000000000000^6271 ≤ 22042407014441^6271*1000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539335697 1000000000 22042407014441 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265443723/10000000000 : ℝ)^8319 ≤ (5337900516593/12500000000000 : ℝ)^6271 := by
    have hnat : (5265443723 : ℕ)^8319*12500000000000^6271 ≤ 5337900516593^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265443723 10000000000 5337900516593 12500000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-271819811/1250000000 : ℝ), (539335697/1000000000 : ℝ), (5265443723/10000000000 : ℝ)] ![(13211981821381/100000000000000 : ℝ), (22042407014441/50000000000000 : ℝ), (5337900516593/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-271819811/1250000000 : ℝ)|^8319 ≤ (13211981821381/100000000000000 : ℝ)^6271
        have hw : |(-271819811/1250000000 : ℝ)|=(271819811/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539335697/1000000000 : ℝ)|^8319 ≤ (22042407014441/50000000000000 : ℝ)^6271
        have hw : |(539335697/1000000000 : ℝ)|=(539335697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265443723/10000000000 : ℝ)|^8319 ≤ (5337900516593/12500000000000 : ℝ)^6271
        have hw : |(5265443723/10000000000 : ℝ)|=(5265443723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s7_1 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344823197/10000000000 : ℝ)*x 0 + (-2239442867/10000000000 : ℝ)*x 1 + (1316360931/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344823197/10000000000 : ℝ)^8319 ≤ (10889829845599/25000000000000 : ℝ)^6271 := by
    have hnat : (5344823197 : ℕ)^8319*25000000000000^6271 ≤ 10889829845599^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344823197 10000000000 10889829845599 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2239442867/10000000000 : ℝ)^8319 ≤ (858592278447/6250000000000 : ℝ)^6271 := by
    have hnat : (2239442867 : ℕ)^8319*6250000000000^6271 ≤ 858592278447^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239442867 10000000000 858592278447 6250000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316360931/2500000000 : ℝ)^8319 ≤ (21351602071751/50000000000000 : ℝ)^6271 := by
    have hnat : (1316360931 : ℕ)^8319*50000000000000^6271 ≤ 21351602071751^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316360931 2500000000 21351602071751 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344823197/10000000000 : ℝ), (-2239442867/10000000000 : ℝ), (1316360931/2500000000 : ℝ)] ![(10889829845599/25000000000000 : ℝ), (858592278447/6250000000000 : ℝ), (21351602071751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344823197/10000000000 : ℝ)|^8319 ≤ (10889829845599/25000000000000 : ℝ)^6271
        have hw : |(5344823197/10000000000 : ℝ)|=(5344823197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2239442867/10000000000 : ℝ)|^8319 ≤ (858592278447/6250000000000 : ℝ)^6271
        have hw : |(-2239442867/10000000000 : ℝ)|=(2239442867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316360931/2500000000 : ℝ)|^8319 ≤ (21351602071751/50000000000000 : ℝ)^6271
        have hw : |(1316360931/2500000000 : ℝ)|=(1316360931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s7_2 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672411599/5000000000 : ℝ)*x 0 + (1316360931/2500000000 : ℝ)*x 1 + (-1119721433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672411599/5000000000 : ℝ)^8319 ≤ (5444914924151/12500000000000 : ℝ)^6271 := by
    have hnat : (2672411599 : ℕ)^8319*12500000000000^6271 ≤ 5444914924151^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672411599 5000000000 5444914924151 12500000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316360931/2500000000 : ℝ)^8319 ≤ (21351602071751/50000000000000 : ℝ)^6271 := by
    have hnat : (1316360931 : ℕ)^8319*50000000000000^6271 ≤ 21351602071751^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316360931 2500000000 21351602071751 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119721433/5000000000 : ℝ)^8319 ≤ (6868738223507/50000000000000 : ℝ)^6271 := by
    have hnat : (1119721433 : ℕ)^8319*50000000000000^6271 ≤ 6868738223507^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119721433 5000000000 6868738223507 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672411599/5000000000 : ℝ), (1316360931/2500000000 : ℝ), (-1119721433/5000000000 : ℝ)] ![(5444914924151/12500000000000 : ℝ), (21351602071751/50000000000000 : ℝ), (6868738223507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672411599/5000000000 : ℝ)|^8319 ≤ (5444914924151/12500000000000 : ℝ)^6271
        have hw : |(2672411599/5000000000 : ℝ)|=(2672411599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316360931/2500000000 : ℝ)|^8319 ≤ (21351602071751/50000000000000 : ℝ)^6271
        have hw : |(1316360931/2500000000 : ℝ)|=(1316360931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1119721433/5000000000 : ℝ)|^8319 ≤ (6868738223507/50000000000000 : ℝ)^6271
        have hw : |(-1119721433/5000000000 : ℝ)|=(1119721433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s7_3 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2183465141/5000000000 : ℝ)*x 0 + (4241929389/10000000000 : ℝ)*x 1 + (280975693/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183465141/5000000000 : ℝ)^8319 ≤ (33316859382469/100000000000000 : ℝ)^6271 := by
    have hnat : (2183465141 : ℕ)^8319*100000000000000^6271 ≤ 33316859382469^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183465141 5000000000 33316859382469 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4241929389/10000000000 : ℝ)^8319 ≤ (32057680973467/100000000000000 : ℝ)^6271 := by
    have hnat : (4241929389 : ℕ)^8319*100000000000000^6271 ≤ 32057680973467^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241929389 10000000000 32057680973467 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280975693/625000000 : ℝ)^8319 ≤ (34625459627741/100000000000000 : ℝ)^6271 := by
    have hnat : (280975693 : ℕ)^8319*100000000000000^6271 ≤ 34625459627741^6271*625000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280975693 625000000 34625459627741 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183465141/5000000000 : ℝ), (4241929389/10000000000 : ℝ), (280975693/625000000 : ℝ)] ![(33316859382469/100000000000000 : ℝ), (32057680973467/100000000000000 : ℝ), (34625459627741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183465141/5000000000 : ℝ)|^8319 ≤ (33316859382469/100000000000000 : ℝ)^6271
        have hw : |(2183465141/5000000000 : ℝ)|=(2183465141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4241929389/10000000000 : ℝ)|^8319 ≤ (32057680973467/100000000000000 : ℝ)^6271
        have hw : |(4241929389/10000000000 : ℝ)|=(4241929389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(280975693/625000000 : ℝ)|^8319 ≤ (34625459627741/100000000000000 : ℝ)^6271
        have hw : |(280975693/625000000 : ℝ)|=(280975693/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s7_4 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1087281669/5000000000 : ℝ)*x 0 + (5265765349/10000000000 : ℝ)*x 1 + (1348258561/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087281669/5000000000 : ℝ)^8319 ≤ (264240418241/2000000000000 : ℝ)^6271 := by
    have hnat : (1087281669 : ℕ)^8319*2000000000000^6271 ≤ 264240418241^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087281669 5000000000 264240418241 2000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265765349/10000000000 : ℝ)^8319 ≤ (21353332222503/50000000000000 : ℝ)^6271 := by
    have hnat : (5265765349 : ℕ)^8319*50000000000000^6271 ≤ 21353332222503^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265765349 10000000000 21353332222503 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348258561/2500000000 : ℝ)^8319 ≤ (22040657313253/50000000000000 : ℝ)^6271 := by
    have hnat : (1348258561 : ℕ)^8319*50000000000000^6271 ≤ 22040657313253^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348258561 2500000000 22040657313253 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1087281669/5000000000 : ℝ), (5265765349/10000000000 : ℝ), (1348258561/2500000000 : ℝ)] ![(264240418241/2000000000000 : ℝ), (21353332222503/50000000000000 : ℝ), (22040657313253/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1087281669/5000000000 : ℝ)|^8319 ≤ (264240418241/2000000000000 : ℝ)^6271
        have hw : |(-1087281669/5000000000 : ℝ)|=(1087281669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265765349/10000000000 : ℝ)|^8319 ≤ (21353332222503/50000000000000 : ℝ)^6271
        have hw : |(5265765349/10000000000 : ℝ)|=(5265765349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348258561/2500000000 : ℝ)|^8319 ≤ (22040657313253/50000000000000 : ℝ)^6271
        have hw : |(1348258561/2500000000 : ℝ)|=(1348258561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s7_5 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656226937/5000000000 : ℝ)*x 0 + (-2111852369/10000000000 : ℝ)*x 1 + (43144279/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656226937/5000000000 : ℝ)^8319 ≤ (4320970813313/10000000000000 : ℝ)^6271 := by
    have hnat : (2656226937 : ℕ)^8319*10000000000000^6271 ≤ 4320970813313^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656226937 5000000000 4320970813313 10000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2111852369/10000000000 : ℝ)^8319 ≤ (12708970383309/100000000000000 : ℝ)^6271 := by
    have hnat : (2111852369 : ℕ)^8319*100000000000000^6271 ≤ 12708970383309^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111852369 10000000000 12708970383309 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43144279/80000000 : ℝ)^8319 ≤ (22040660734269/50000000000000 : ℝ)^6271 := by
    have hnat : (43144279 : ℕ)^8319*50000000000000^6271 ≤ 22040660734269^6271*80000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43144279 80000000 22040660734269 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656226937/5000000000 : ℝ), (-2111852369/10000000000 : ℝ), (43144279/80000000 : ℝ)] ![(4320970813313/10000000000000 : ℝ), (12708970383309/100000000000000 : ℝ), (22040660734269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656226937/5000000000 : ℝ)|^8319 ≤ (4320970813313/10000000000000 : ℝ)^6271
        have hw : |(2656226937/5000000000 : ℝ)|=(2656226937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2111852369/10000000000 : ℝ)|^8319 ≤ (12708970383309/100000000000000 : ℝ)^6271
        have hw : |(-2111852369/10000000000 : ℝ)|=(2111852369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43144279/80000000 : ℝ)|^8319 ≤ (22040660734269/50000000000000 : ℝ)^6271
        have hw : |(43144279/80000000 : ℝ)|=(43144279/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s7_6 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312453711/10000000000 : ℝ)*x 0 + (168532347/312500000 : ℝ)*x 1 + (-1055926139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312453711/10000000000 : ℝ)^8319 ≤ (10802426593591/25000000000000 : ℝ)^6271 := by
    have hnat : (5312453711 : ℕ)^8319*25000000000000^6271 ≤ 10802426593591^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312453711 10000000000 10802426593591 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168532347/312500000 : ℝ)^8319 ≤ (2204066197581/5000000000000 : ℝ)^6271 := by
    have hnat : (168532347 : ℕ)^8319*5000000000000^6271 ≤ 2204066197581^6271*312500000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168532347 312500000 2204066197581 5000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055926139/5000000000 : ℝ)^8319 ≤ (12708969656831/100000000000000 : ℝ)^6271 := by
    have hnat : (1055926139 : ℕ)^8319*100000000000000^6271 ≤ 12708969656831^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055926139 5000000000 12708969656831 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312453711/10000000000 : ℝ), (168532347/312500000 : ℝ), (-1055926139/5000000000 : ℝ)] ![(10802426593591/25000000000000 : ℝ), (2204066197581/5000000000000 : ℝ), (12708969656831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312453711/10000000000 : ℝ)|^8319 ≤ (10802426593591/25000000000000 : ℝ)^6271
        have hw : |(5312453711/10000000000 : ℝ)|=(5312453711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168532347/312500000 : ℝ)|^8319 ≤ (2204066197581/5000000000000 : ℝ)^6271
        have hw : |(168532347/312500000 : ℝ)|=(168532347/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1055926139/5000000000 : ℝ)|^8319 ≤ (12708969656831/100000000000000 : ℝ)^6271
        have hw : |(-1055926139/5000000000 : ℝ)|=(1055926139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s7_7 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4366940471/10000000000 : ℝ)*x 0 + (4494973439/10000000000 : ℝ)*x 1 + (1060642233/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366940471/10000000000 : ℝ)^8319 ≤ (33316962505067/100000000000000 : ℝ)^6271 := by
    have hnat : (4366940471 : ℕ)^8319*100000000000000^6271 ≤ 33316962505067^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366940471 10000000000 33316962505067 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4494973439/10000000000 : ℝ)^8319 ≤ (17309472326317/50000000000000 : ℝ)^6271 := by
    have hnat : (4494973439 : ℕ)^8319*50000000000000^6271 ≤ 17309472326317^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494973439 10000000000 17309472326317 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060642233/2500000000 : ℝ)^8319 ≤ (16032046412313/50000000000000 : ℝ)^6271 := by
    have hnat : (1060642233 : ℕ)^8319*50000000000000^6271 ≤ 16032046412313^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060642233 2500000000 16032046412313 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366940471/10000000000 : ℝ), (4494973439/10000000000 : ℝ), (1060642233/2500000000 : ℝ)] ![(33316962505067/100000000000000 : ℝ), (17309472326317/50000000000000 : ℝ), (16032046412313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366940471/10000000000 : ℝ)|^8319 ≤ (33316962505067/100000000000000 : ℝ)^6271
        have hw : |(4366940471/10000000000 : ℝ)|=(4366940471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4494973439/10000000000 : ℝ)|^8319 ≤ (17309472326317/50000000000000 : ℝ)^6271
        have hw : |(4494973439/10000000000 : ℝ)|=(4494973439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1060642233/2500000000 : ℝ)|^8319 ≤ (16032046412313/50000000000000 : ℝ)^6271
        have hw : |(1060642233/2500000000 : ℝ)|=(1060642233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1126_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2831/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11331/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14041/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (439/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2831/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (439/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2831/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (439/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2831/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (439/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2831/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (439/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2831/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (439/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2831/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2831/25000 : ℝ) ^ (4159/1024 : ℝ) ≤ (7190651926971861/50000000000000000000 : ℝ) := by
    have hpowers : (2831/25000 : ℝ)^4159 ≤ (7190651926971861/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2831 : ℕ)^4159*50000000000000000000^1024 ≤ 7190651926971861^1024*25000^4159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2831 25000 7190651926971861 50000000000000000000 4159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2831/25000 : ℝ)) (X := (7190651926971861/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (439/3125 : ℝ) ^ (4159/1024 : ℝ) ≤ (34515670001802491/100000000000000000000 : ℝ) := by
    have hpowers : (439/3125 : ℝ)^4159 ≤ (34515670001802491/100000000000000000000 : ℝ)^1024 := by
      have hnat : (439 : ℕ)^4159*100000000000000000000^1024 ≤ 34515670001802491^1024*3125^4159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        439 3125 34515670001802491 100000000000000000000 4159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (439/3125 : ℝ)) (X := (34515670001802491/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007190651926971861/25000000000000000000 : ℝ) ≤ (10000708096128991/10000000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (25007190651926971861/25000000000000000000 : ℝ)^1024 ≤ (10000708096128991/10000000000000000 : ℝ)^4159 := by
      have hnat : (25007190651926971861 : ℕ)^1024*10000000000000000^4159 ≤ 10000708096128991^4159*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007190651926971861 25000000000000000000 10000708096128991 10000000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000708096128991/10000000000000000 : ℝ)) (X := (25007190651926971861/25000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048896973855746213/100000000000000000000 : ℝ) ≤ (2500300921353673/2500000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (100048896973855746213/100000000000000000000 : ℝ)^1024 ≤ (2500300921353673/2500000000000000 : ℝ)^4159 := by
      have hnat : (100048896973855746213 : ℕ)^1024*2500000000000000^4159 ≤ 2500300921353673^4159*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048896973855746213 100000000000000000000 2500300921353673 2500000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500300921353673/2500000000000000 : ℝ)) (X := (100048896973855746213/100000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034515670001802491/50000000000000000000 : ℝ) ≤ (10001699274700393/10000000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (50034515670001802491/50000000000000000000 : ℝ)^1024 ≤ (10001699274700393/10000000000000000 : ℝ)^4159 := by
      have hnat : (50034515670001802491 : ℕ)^1024*10000000000000000^4159 ≤ 10001699274700393^4159*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034515670001802491 50000000000000000000 10001699274700393 10000000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001699274700393/10000000000000000 : ℝ)) (X := (50034515670001802491/50000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7190651926971861/50000000000000000000 : ℝ) ≤ ((2269225395642734603/2270000000000000000 : ℝ)+2*(165196428567/90800000000000 : ℝ)*(2831/25000 : ℝ))^(4159/1024 : ℝ) := by
    rw [show (2269225395642734603/2270000000000000000 : ℝ)+2*(165196428567/90800000000000 : ℝ)*(2831/25000 : ℝ)=(10000708096128991/10000000000000000 : ℝ) by norm_num, show 1+2*(7190651926971861/50000000000000000000 : ℝ)=(25007190651926971861/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34515670001802491/100000000000000000000 : ℝ)+(7190651926971861/50000000000000000000 : ℝ) ≤ ((2269225395642734603/2270000000000000000 : ℝ)+(165196428567/90800000000000 : ℝ)*((439/3125 : ℝ)+(2831/25000 : ℝ)))^(4159/1024 : ℝ) := by
    rw [show (2269225395642734603/2270000000000000000 : ℝ)+(165196428567/90800000000000 : ℝ)*((439/3125 : ℝ)+(2831/25000 : ℝ))=(2500300921353673/2500000000000000 : ℝ) by norm_num, show 1+(34515670001802491/100000000000000000000 : ℝ)+(7190651926971861/50000000000000000000 : ℝ)=(100048896973855746213/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34515670001802491/100000000000000000000 : ℝ) ≤ ((2269225395642734603/2270000000000000000 : ℝ)+2*(165196428567/90800000000000 : ℝ)*(439/3125 : ℝ))^(4159/1024 : ℝ) := by
    rw [show (2269225395642734603/2270000000000000000 : ℝ)+2*(165196428567/90800000000000 : ℝ)*(439/3125 : ℝ)=(10001699274700393/10000000000000000 : ℝ) by norm_num, show 1+2*(34515670001802491/100000000000000000000 : ℝ)=(50034515670001802491/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2269225395642734603/2270000000000000000 : ℝ)*(X 1 0+X 2 0)+(165196428567/90800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (2831/25000 : ℝ)) (hi := (439/3125 : ℝ)) (c := (2269225395642734603/2270000000000000000 : ℝ)) (alpha := (165196428567/90800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2269225395642734603/2270000000000000000 : ℝ)*(X 0 1+X 2 1)+(165196428567/90800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (2831/25000 : ℝ)) (hi := (439/3125 : ℝ)) (c := (2269225395642734603/2270000000000000000 : ℝ)) (alpha := (165196428567/90800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2269225395642734603/2270000000000000000 : ℝ)*(X 0 2+X 1 2)+(165196428567/90800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (2831/25000 : ℝ)) (hi := (439/3125 : ℝ)) (c := (2269225395642734603/2270000000000000000 : ℝ)) (alpha := (165196428567/90800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-271819811/1250000000 : ℝ)*X 0 0+(539335697/1000000000 : ℝ)*X 0 1+(5265443723/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344823197/10000000000 : ℝ)*X 1 0+(-2239442867/10000000000 : ℝ)*X 1 1+(1316360931/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672411599/5000000000 : ℝ)*X 2 0+(1316360931/2500000000 : ℝ)*X 2 1+(-1119721433/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2183465141/5000000000 : ℝ)*X 0 0+(4241929389/10000000000 : ℝ)*X 0 1+(280975693/625000000 : ℝ)*X 0 2+(2183465141/5000000000 : ℝ)*X 1 0+(4241929389/10000000000 : ℝ)*X 1 1+(280975693/625000000 : ℝ)*X 1 2+(2183465141/5000000000 : ℝ)*X 2 0+(4241929389/10000000000 : ℝ)*X 2 1+(280975693/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1087281669/5000000000 : ℝ)*X 0 0+(5265765349/10000000000 : ℝ)*X 0 1+(1348258561/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656226937/5000000000 : ℝ)*X 1 0+(-2111852369/10000000000 : ℝ)*X 1 1+(43144279/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312453711/10000000000 : ℝ)*X 2 0+(168532347/312500000 : ℝ)*X 2 1+(-1055926139/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4366940471/10000000000 : ℝ)*X 0 0+(4494973439/10000000000 : ℝ)*X 0 1+(1060642233/2500000000 : ℝ)*X 0 2+(4366940471/10000000000 : ℝ)*X 1 0+(4494973439/10000000000 : ℝ)*X 1 1+(1060642233/2500000000 : ℝ)*X 1 2+(4366940471/10000000000 : ℝ)*X 2 0+(4494973439/10000000000 : ℝ)*X 2 1+(1060642233/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (255510106286099786433250131/28375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (894316463/50000000000000 : ℝ)*(base19) + (52124327/3125000000000 : ℝ)*(base23) + (32634733/50000000000000 : ℝ)*(lower2) + (227031643/100000000000000 : ℝ)*(upper3) + (34660837/25000000000000 : ℝ)*(upper5) + (1469987036485659/25000000000000 : ℝ)*(major0) + (1469987036485659/25000000000000 : ℝ)*(major1) + (1469987036485659/25000000000000 : ℝ)*(major2) + (7817849412256133/100000000000000 : ℝ)*(sp0) + (312715850507867/4000000000000 : ℝ)*(sp1) + (3908948191675569/50000000000000 : ℝ)*(sp2) + (1970985774347333/50000000000000 : ℝ)*(sp3) + (12159768367/25000000000000 : ℝ)*(sp4) + (659792557/2500000000000 : ℝ)*(sp7) + (1970998970198473/50000000000000 : ℝ)*(f.failure) + (7817898051329601/100000000000000 : ℝ)*(f.sum) + (1546436274887/1135000000000000000000000000 : ℝ)*base66 + (323875646749116623/56750000000000000000000000000000 : ℝ)*base68 + (1190733348584366623/56750000000000000000000000000000 : ℝ)*base70 + (683103030966633377/56750000000000000000000000000000 : ℝ)*base71 + (2634383286081/567500000000000000000000000 : ℝ)*base74 + (541824131390116623/56750000000000000000000000000000 : ℝ)*base76 + (169667090410883377/56750000000000000000000000000000 : ℝ)*base77 + (1122342504096616623/56750000000000000000000000000000 : ℝ)*base80 + (4860850452553/1135000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (4375019/625000000000000000000 : ℝ)*base89 + (4375019/625000000000000000000 : ℝ)*base91 + (4375019/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (663130078258690787821281/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (175088071/100000000000000 : ℝ)*(base19) + (144820383/20000000000000 : ℝ)*(base23) + (428391281/100000000000000 : ℝ)*(upper3) + (322085211/100000000000000 : ℝ)*(lower4) + (53002131/25000000000000 : ℝ)*(upper5) + (590962712962319/10000000000000 : ℝ)*(major0) + (590962712962319/10000000000000 : ℝ)*(major1) + (590962712962319/10000000000000 : ℝ)*(major2) + (2901269331/25000000000000 : ℝ)*(sp1) + (20886281611/50000000000000 : ℝ)*(sp2) + (982169834844227/12500000000000 : ℝ)*(sp4) + (392867344929421/5000000000000 : ℝ)*(sp5) + (196432904552217/2500000000000 : ℝ)*(sp6) + (1980947569202917/50000000000000 : ℝ)*(sp7) + (1980947569202917/50000000000000 : ℝ)*(f.failure) + (982169834844227/12500000000000 : ℝ)*(f.sum) + (9986682713/2000000000000000000000000 : ℝ)*base66 + (833266320578191/100000000000000000000000000000 : ℝ)*base67 + (1152000372378191/100000000000000000000000000000 : ℝ)*base69 + (203929639378191/100000000000000000000000000000 : ℝ)*base71 + (1523719177/2000000000000000000000000 : ℝ)*base74 + (3693201675178191/100000000000000000000000000000 : ℝ)*base75 + (462940486578191/100000000000000000000000000000 : ℝ)*base77 + (517284354178191/100000000000000000000000000000 : ℝ)*base79 + (4969013307/2000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (1842849/625000000000000000000 : ℝ)*base90 + (1842849/625000000000000000000 : ℝ)*base92 + (1842849/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1126_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2831/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11331/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14041/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1126_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1126_s8_0 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1087281819/5000000000 : ℝ)*x 0 + (5393285963/10000000000 : ℝ)*x 1 + (5265511431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087281819/5000000000 : ℝ)^8319 ≤ (1321202333003/10000000000000 : ℝ)^6271 := by
    have hnat : (1087281819 : ℕ)^8319*10000000000000^6271 ≤ 1321202333003^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087281819 5000000000 1321202333003 10000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393285963/10000000000 : ℝ)^8319 ≤ (44084044075553/100000000000000 : ℝ)^6271 := by
    have hnat : (5393285963 : ℕ)^8319*100000000000000^6271 ≤ 44084044075553^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393285963 10000000000 44084044075553 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265511431/10000000000 : ℝ)^8319 ≤ (21351966292177/50000000000000 : ℝ)^6271 := by
    have hnat : (5265511431 : ℕ)^8319*50000000000000^6271 ≤ 21351966292177^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265511431 10000000000 21351966292177 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1087281819/5000000000 : ℝ), (5393285963/10000000000 : ℝ), (5265511431/10000000000 : ℝ)] ![(1321202333003/10000000000000 : ℝ), (44084044075553/100000000000000 : ℝ), (21351966292177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1087281819/5000000000 : ℝ)|^8319 ≤ (1321202333003/10000000000000 : ℝ)^6271
        have hw : |(-1087281819/5000000000 : ℝ)|=(1087281819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393285963/10000000000 : ℝ)|^8319 ≤ (44084044075553/100000000000000 : ℝ)^6271
        have hw : |(5393285963/10000000000 : ℝ)|=(5393285963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265511431/10000000000 : ℝ)|^8319 ≤ (21351966292177/50000000000000 : ℝ)^6271
        have hw : |(5265511431/10000000000 : ℝ)|=(5265511431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s8_1 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672402827/5000000000 : ℝ)*x 0 + (-2239376631/10000000000 : ℝ)*x 1 + (5265511453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672402827/5000000000 : ℝ)^8319 ≤ (43559129718051/100000000000000 : ℝ)^6271 := by
    have hnat : (2672402827 : ℕ)^8319*100000000000000^6271 ≤ 43559129718051^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672402827 5000000000 43559129718051 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2239376631/10000000000 : ℝ)^8319 ≤ (13736937449527/100000000000000 : ℝ)^6271 := by
    have hnat : (2239376631 : ℕ)^8319*100000000000000^6271 ≤ 13736937449527^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239376631 10000000000 13736937449527 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265511453/10000000000 : ℝ)^8319 ≤ (42703932821047/100000000000000 : ℝ)^6271 := by
    have hnat : (5265511453 : ℕ)^8319*100000000000000^6271 ≤ 42703932821047^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265511453 10000000000 42703932821047 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672402827/5000000000 : ℝ), (-2239376631/10000000000 : ℝ), (5265511453/10000000000 : ℝ)] ![(43559129718051/100000000000000 : ℝ), (13736937449527/100000000000000 : ℝ), (42703932821047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672402827/5000000000 : ℝ)|^8319 ≤ (43559129718051/100000000000000 : ℝ)^6271
        have hw : |(2672402827/5000000000 : ℝ)|=(2672402827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2239376631/10000000000 : ℝ)|^8319 ≤ (13736937449527/100000000000000 : ℝ)^6271
        have hw : |(-2239376631/10000000000 : ℝ)|=(2239376631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265511453/10000000000 : ℝ)|^8319 ≤ (42703932821047/100000000000000 : ℝ)^6271
        have hw : |(5265511453/10000000000 : ℝ)|=(5265511453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s8_2 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068961133/2000000000 : ℝ)*x 0 + (5265511441/10000000000 : ℝ)*x 1 + (-279922079/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068961133/2000000000 : ℝ)^8319 ≤ (2722445614811/6250000000000 : ℝ)^6271 := by
    have hnat : (1068961133 : ℕ)^8319*6250000000000^6271 ≤ 2722445614811^6271*2000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068961133 2000000000 2722445614811 6250000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265511441/10000000000 : ℝ)^8319 ≤ (21351966345971/50000000000000 : ℝ)^6271 := by
    have hnat : (5265511441 : ℕ)^8319*50000000000000^6271 ≤ 21351966345971^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265511441 10000000000 21351966345971 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279922079/1250000000 : ℝ)^8319 ≤ (2747387491533/20000000000000 : ℝ)^6271 := by
    have hnat : (279922079 : ℕ)^8319*20000000000000^6271 ≤ 2747387491533^6271*1250000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279922079 1250000000 2747387491533 20000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068961133/2000000000 : ℝ), (5265511441/10000000000 : ℝ), (-279922079/1250000000 : ℝ)] ![(2722445614811/6250000000000 : ℝ), (21351966345971/50000000000000 : ℝ), (2747387491533/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068961133/2000000000 : ℝ)|^8319 ≤ (2722445614811/6250000000000 : ℝ)^6271
        have hw : |(1068961133/2000000000 : ℝ)|=(1068961133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265511441/10000000000 : ℝ)|^8319 ≤ (21351966345971/50000000000000 : ℝ)^6271
        have hw : |(5265511441/10000000000 : ℝ)|=(5265511441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-279922079/1250000000 : ℝ)|^8319 ≤ (2747387491533/20000000000000 : ℝ)^6271
        have hw : |(-279922079/1250000000 : ℝ)|=(279922079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s8_3 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (68233341/156250000 : ℝ)*x 0 + (1060516623/2500000000 : ℝ)*x 1 + (1123868263/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68233341/156250000 : ℝ)^8319 ≤ (8329223807737/25000000000000 : ℝ)^6271 := by
    have hnat : (68233341 : ℕ)^8319*25000000000000^6271 ≤ 8329223807737^6271*156250000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68233341 156250000 8329223807737 25000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060516623/2500000000 : ℝ)^8319 ≤ (16029527748597/50000000000000 : ℝ)^6271 := by
    have hnat : (1060516623 : ℕ)^8319*50000000000000^6271 ≤ 16029527748597^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060516623 2500000000 16029527748597 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123868263/2500000000 : ℝ)^8319 ≤ (1731202463169/5000000000000 : ℝ)^6271 := by
    have hnat : (1123868263 : ℕ)^8319*5000000000000^6271 ≤ 1731202463169^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123868263 2500000000 1731202463169 5000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(68233341/156250000 : ℝ), (1060516623/2500000000 : ℝ), (1123868263/2500000000 : ℝ)] ![(8329223807737/25000000000000 : ℝ), (16029527748597/50000000000000 : ℝ), (1731202463169/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(68233341/156250000 : ℝ)|^8319 ≤ (8329223807737/25000000000000 : ℝ)^6271
        have hw : |(68233341/156250000 : ℝ)|=(68233341/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060516623/2500000000 : ℝ)|^8319 ≤ (16029527748597/50000000000000 : ℝ)^6271
        have hw : |(1060516623/2500000000 : ℝ)|=(1060516623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1123868263/2500000000 : ℝ)|^8319 ≤ (1731202463169/5000000000000 : ℝ)^6271
        have hw : |(1123868263/2500000000 : ℝ)|=(1123868263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s8_4 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2174568489/10000000000 : ℝ)*x 0 + (1316457983/2500000000 : ℝ)*x 1 + (5392964349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174568489/10000000000 : ℝ)^8319 ≤ (13212062428789/100000000000000 : ℝ)^6271 := by
    have hnat : (2174568489 : ℕ)^8319*100000000000000^6271 ≤ 13212062428789^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174568489 10000000000 13212062428789 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316457983/2500000000 : ℝ)^8319 ≤ (42707380807319/100000000000000 : ℝ)^6271 := by
    have hnat : (1316457983 : ℕ)^8319*100000000000000^6271 ≤ 42707380807319^6271*2500000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316457983 2500000000 42707380807319 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392964349/10000000000 : ℝ)^8319 ≤ (44080556745761/100000000000000 : ℝ)^6271 := by
    have hnat : (5392964349 : ℕ)^8319*100000000000000^6271 ≤ 44080556745761^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392964349 10000000000 44080556745761 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2174568489/10000000000 : ℝ), (1316457983/2500000000 : ℝ), (5392964349/10000000000 : ℝ)] ![(13212062428789/100000000000000 : ℝ), (42707380807319/100000000000000 : ℝ), (44080556745761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2174568489/10000000000 : ℝ)|^8319 ≤ (13212062428789/100000000000000 : ℝ)^6271
        have hw : |(-2174568489/10000000000 : ℝ)|=(2174568489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316457983/2500000000 : ℝ)|^8319 ≤ (42707380807319/100000000000000 : ℝ)^6271
        have hw : |(1316457983/2500000000 : ℝ)|=(1316457983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392964349/10000000000 : ℝ)|^8319 ≤ (44080556745761/100000000000000 : ℝ)^6271
        have hw : |(5392964349/10000000000 : ℝ)|=(5392964349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s8_5 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656236171/5000000000 : ℝ)*x 0 + (-1055961539/5000000000 : ℝ)*x 1 + (2696482219/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656236171/5000000000 : ℝ)^8319 ≤ (21604953701261/50000000000000 : ℝ)^6271 := by
    have hnat : (2656236171 : ℕ)^8319*50000000000000^6271 ≤ 21604953701261^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656236171 5000000000 21604953701261 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055961539/5000000000 : ℝ)^8319 ≤ (12709534875847/100000000000000 : ℝ)^6271 := by
    have hnat : (1055961539 : ℕ)^8319*100000000000000^6271 ≤ 12709534875847^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055961539 5000000000 12709534875847 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696482219/5000000000 : ℝ)^8319 ≤ (22040278855399/50000000000000 : ℝ)^6271 := by
    have hnat : (2696482219 : ℕ)^8319*50000000000000^6271 ≤ 22040278855399^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696482219 5000000000 22040278855399 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656236171/5000000000 : ℝ), (-1055961539/5000000000 : ℝ), (2696482219/5000000000 : ℝ)] ![(21604953701261/50000000000000 : ℝ), (12709534875847/100000000000000 : ℝ), (22040278855399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656236171/5000000000 : ℝ)|^8319 ≤ (21604953701261/50000000000000 : ℝ)^6271
        have hw : |(2656236171/5000000000 : ℝ)|=(2656236171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1055961539/5000000000 : ℝ)|^8319 ≤ (12709534875847/100000000000000 : ℝ)^6271
        have hw : |(-1055961539/5000000000 : ℝ)|=(1055961539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696482219/5000000000 : ℝ)|^8319 ≤ (22040278855399/50000000000000 : ℝ)^6271
        have hw : |(2696482219/5000000000 : ℝ)|=(2696482219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s8_6 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656235619/5000000000 : ℝ)*x 0 + (2696482147/5000000000 : ℝ)*x 1 + (-1055962383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656235619/5000000000 : ℝ)^8319 ≤ (5401236936297/12500000000000 : ℝ)^6271 := by
    have hnat : (2656235619 : ℕ)^8319*12500000000000^6271 ≤ 5401236936297^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656235619 5000000000 5401236936297 12500000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696482147/5000000000 : ℝ)^8319 ≤ (4408055614939/10000000000000 : ℝ)^6271 := by
    have hnat : (2696482147 : ℕ)^8319*10000000000000^6271 ≤ 4408055614939^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696482147 5000000000 4408055614939 10000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055962383/5000000000 : ℝ)^8319 ≤ (6354774175883/50000000000000 : ℝ)^6271 := by
    have hnat : (1055962383 : ℕ)^8319*50000000000000^6271 ≤ 6354774175883^6271*5000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055962383 5000000000 6354774175883 50000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656235619/5000000000 : ℝ), (2696482147/5000000000 : ℝ), (-1055962383/5000000000 : ℝ)] ![(5401236936297/12500000000000 : ℝ), (4408055614939/10000000000000 : ℝ), (6354774175883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656235619/5000000000 : ℝ)|^8319 ≤ (5401236936297/12500000000000 : ℝ)^6271
        have hw : |(2656235619/5000000000 : ℝ)|=(2656235619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696482147/5000000000 : ℝ)|^8319 ≤ (4408055614939/10000000000000 : ℝ)^6271
        have hw : |(2696482147/5000000000 : ℝ)|=(2696482147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1055962383/5000000000 : ℝ)|^8319 ≤ (6354774175883/50000000000000 : ℝ)^6271
        have hw : |(-1055962383/5000000000 : ℝ)|=(1055962383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1126_s8_7 (p : ℝ) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (174677703/400000000 : ℝ)*x 0 + (4494837253/10000000000 : ℝ)*x 1 + (4242705587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174677703/400000000 : ℝ)^8319 ≤ (6663396759921/20000000000000 : ℝ)^6271 := by
    have hnat : (174677703 : ℕ)^8319*20000000000000^6271 ≤ 6663396759921^6271*400000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174677703 400000000 6663396759921 20000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4494837253/10000000000 : ℝ)^8319 ≤ (6923510650953/20000000000000 : ℝ)^6271 := by
    have hnat : (4494837253 : ℕ)^8319*20000000000000^6271 ≤ 6923510650953^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494837253 10000000000 6923510650953 20000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4242705587/10000000000 : ℝ)^8319 ≤ (32065462924367/100000000000000 : ℝ)^6271 := by
    have hnat : (4242705587 : ℕ)^8319*100000000000000^6271 ≤ 32065462924367^6271*10000000000^8319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242705587 10000000000 32065462924367 100000000000000 8319 6271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8319/2048 : ℝ)) 8319 6271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174677703/400000000 : ℝ), (4494837253/10000000000 : ℝ), (4242705587/10000000000 : ℝ)] ![(6663396759921/20000000000000 : ℝ), (6923510650953/20000000000000 : ℝ), (32065462924367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174677703/400000000 : ℝ)|^8319 ≤ (6663396759921/20000000000000 : ℝ)^6271
        have hw : |(174677703/400000000 : ℝ)|=(174677703/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4494837253/10000000000 : ℝ)|^8319 ≤ (6923510650953/20000000000000 : ℝ)^6271
        have hw : |(4494837253/10000000000 : ℝ)|=(4494837253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4242705587/10000000000 : ℝ)|^8319 ≤ (32065462924367/100000000000000 : ℝ)^6271
        have hw : |(4242705587/10000000000 : ℝ)|=(4242705587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1126_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14041/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11331/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11333/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14039/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14041/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11331/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14041/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11331/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14041/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11331/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14041/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11331/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14041/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11331/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14041/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11331/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11331/100000 : ℝ) ^ (4159/1024 : ℝ) ≤ (450545141729487/3125000000000000000 : ℝ) := by
    have hpowers : (11331/100000 : ℝ)^4159 ≤ (450545141729487/3125000000000000000 : ℝ)^1024 := by
      have hnat : (11331 : ℕ)^4159*3125000000000000000^1024 ≤ 450545141729487^1024*100000^4159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11331 100000 450545141729487 3125000000000000000 4159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11331/100000 : ℝ)) (X := (450545141729487/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14041/100000 : ℝ) ^ (4159/1024 : ℝ) ≤ (17222934831111071/50000000000000000000 : ℝ) := by
    have hpowers : (14041/100000 : ℝ)^4159 ≤ (17222934831111071/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14041 : ℕ)^4159*50000000000000000000^1024 ≤ 17222934831111071^1024*100000^4159 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14041 100000 17222934831111071 50000000000000000000 4159 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14041/100000 : ℝ)) (X := (17222934831111071/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562950545141729487/1562500000000000000 : ℝ) ≤ (10000709875404107/10000000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (1562950545141729487/1562500000000000000 : ℝ)^1024 ≤ (10000709875404107/10000000000000000 : ℝ)^4159 := by
      have hnat : (1562950545141729487 : ℕ)^1024*10000000000000000^4159 ≤ 10000709875404107^4159*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562950545141729487 1562500000000000000 10000709875404107 10000000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000709875404107/10000000000000000 : ℝ)) (X := (1562950545141729487/1562500000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024431657098782863/50000000000000000000 : ℝ) ≤ (312537589280477/312500000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (50024431657098782863/50000000000000000000 : ℝ)^1024 ≤ (312537589280477/312500000000000 : ℝ)^4159 := by
      have hnat : (50024431657098782863 : ℕ)^1024*312500000000000^4159 ≤ 312537589280477^4159*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024431657098782863 50000000000000000000 312537589280477 312500000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312537589280477/312500000000000 : ℝ)) (X := (50024431657098782863/50000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017222934831111071/25000000000000000000 : ℝ) ≤ (10001695838546421/10000000000000000 : ℝ) ^ (4159/1024 : ℝ) := by
    have hpowers : (25017222934831111071/25000000000000000000 : ℝ)^1024 ≤ (10001695838546421/10000000000000000 : ℝ)^4159 := by
      have hnat : (25017222934831111071 : ℕ)^1024*10000000000000000^4159 ≤ 10001695838546421^4159*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017222934831111071 25000000000000000000 10001695838546421 10000000000000000 1024 4159 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001695838546421/10000000000000000 : ℝ)) (X := (25017222934831111071/25000000000000000000 : ℝ)) (by norm_num) 4159 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(450545141729487/3125000000000000000 : ℝ) ≤ ((6772687953494892509/6775000000000000000 : ℝ)+2*(492981571157/271000000000000 : ℝ)*(11331/100000 : ℝ))^(4159/1024 : ℝ) := by
    rw [show (6772687953494892509/6775000000000000000 : ℝ)+2*(492981571157/271000000000000 : ℝ)*(11331/100000 : ℝ)=(10000709875404107/10000000000000000 : ℝ) by norm_num, show 1+2*(450545141729487/3125000000000000000 : ℝ)=(1562950545141729487/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17222934831111071/50000000000000000000 : ℝ)+(450545141729487/3125000000000000000 : ℝ) ≤ ((6772687953494892509/6775000000000000000 : ℝ)+(492981571157/271000000000000 : ℝ)*((14041/100000 : ℝ)+(11331/100000 : ℝ)))^(4159/1024 : ℝ) := by
    rw [show (6772687953494892509/6775000000000000000 : ℝ)+(492981571157/271000000000000 : ℝ)*((14041/100000 : ℝ)+(11331/100000 : ℝ))=(312537589280477/312500000000000 : ℝ) by norm_num, show 1+(17222934831111071/50000000000000000000 : ℝ)+(450545141729487/3125000000000000000 : ℝ)=(50024431657098782863/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17222934831111071/50000000000000000000 : ℝ) ≤ ((6772687953494892509/6775000000000000000 : ℝ)+2*(492981571157/271000000000000 : ℝ)*(14041/100000 : ℝ))^(4159/1024 : ℝ) := by
    rw [show (6772687953494892509/6775000000000000000 : ℝ)+2*(492981571157/271000000000000 : ℝ)*(14041/100000 : ℝ)=(10001695838546421/10000000000000000 : ℝ) by norm_num, show 1+2*(17222934831111071/50000000000000000000 : ℝ)=(25017222934831111071/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6772687953494892509/6775000000000000000 : ℝ)*(X 1 0+X 2 0)+(492981571157/271000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (11331/100000 : ℝ)) (hi := (14041/100000 : ℝ)) (c := (6772687953494892509/6775000000000000000 : ℝ)) (alpha := (492981571157/271000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6772687953494892509/6775000000000000000 : ℝ)*(X 0 1+X 2 1)+(492981571157/271000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (11331/100000 : ℝ)) (hi := (14041/100000 : ℝ)) (c := (6772687953494892509/6775000000000000000 : ℝ)) (alpha := (492981571157/271000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6772687953494892509/6775000000000000000 : ℝ)*(X 0 2+X 1 2)+(492981571157/271000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4159/1024 : ℝ)) (lo := (11331/100000 : ℝ)) (hi := (14041/100000 : ℝ)) (c := (6772687953494892509/6775000000000000000 : ℝ)) (alpha := (492981571157/271000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1087281819/5000000000 : ℝ)*X 0 0+(5393285963/10000000000 : ℝ)*X 0 1+(5265511431/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672402827/5000000000 : ℝ)*X 1 0+(-2239376631/10000000000 : ℝ)*X 1 1+(5265511453/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068961133/2000000000 : ℝ)*X 2 0+(5265511441/10000000000 : ℝ)*X 2 1+(-279922079/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((68233341/156250000 : ℝ)*X 0 0+(1060516623/2500000000 : ℝ)*X 0 1+(1123868263/2500000000 : ℝ)*X 0 2+(68233341/156250000 : ℝ)*X 1 0+(1060516623/2500000000 : ℝ)*X 1 1+(1123868263/2500000000 : ℝ)*X 1 2+(68233341/156250000 : ℝ)*X 2 0+(1060516623/2500000000 : ℝ)*X 2 1+(1123868263/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2174568489/10000000000 : ℝ)*X 0 0+(1316457983/2500000000 : ℝ)*X 0 1+(5392964349/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656236171/5000000000 : ℝ)*X 1 0+(-1055961539/5000000000 : ℝ)*X 1 1+(2696482219/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656235619/5000000000 : ℝ)*X 2 0+(2696482147/5000000000 : ℝ)*X 2 1+(-1055962383/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174677703/400000000 : ℝ)*X 0 0+(4494837253/10000000000 : ℝ)*X 0 1+(4242705587/10000000000 : ℝ)*X 0 2+(174677703/400000000 : ℝ)*X 1 0+(4494837253/10000000000 : ℝ)*X 1 1+(4242705587/10000000000 : ℝ)*X 1 2+(174677703/400000000 : ℝ)*X 2 0+(4494837253/10000000000 : ℝ)*X 2 1+(4242705587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1126_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1277763573270909009411501501/338750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (383631847/50000000000000 : ℝ)*(base19) + (730023891/100000000000000 : ℝ)*(base23) + (14256457/50000000000000 : ℝ)*(lower2) + (101550697/100000000000000 : ℝ)*(upper3) + (15815097/25000000000000 : ℝ)*(upper5) + (5886290023503321/100000000000000 : ℝ)*(major0) + (5886290023503321/100000000000000 : ℝ)*(major1) + (5886290023503321/100000000000000 : ℝ)*(major2) + (978288551797541/12500000000000 : ℝ)*(sp0) + (7826329531852699/100000000000000 : ℝ)*(sp1) + (3913164784546251/50000000000000 : ℝ)*(sp2) + (1973119041648413/50000000000000 : ℝ)*(sp3) + (341949001/1562500000000 : ℝ)*(sp4) + (461554409/4000000000000 : ℝ)*(sp7) + (3946249622157051/100000000000000 : ℝ)*(f.failure) + (7826330299116393/100000000000000 : ℝ)*(f.sum) + (723513186053/13550000000000000000000000000 : ℝ)*base66 + (1964447830838052611/677500000000000000000000000000000 : ℝ)*base68 + (3740767399443052611/677500000000000000000000000000000 : ℝ)*base70 + (5642618579928052611/677500000000000000000000000000000 : ℝ)*base72 + (98334875501997/13550000000000000000000000000 : ℝ)*base73 + (5503181985825552611/677500000000000000000000000000000 : ℝ)*base76 + (2179417225838052611/677500000000000000000000000000000 : ℝ)*base78 + (1774330402763052611/677500000000000000000000000000000 : ℝ)*base80 + (20898556173747/13550000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1276353/1250000000000000000000 : ℝ)*base89 + (1276353/1250000000000000000000 : ℝ)*base91 + (1276353/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (523621321118699573800832253/84687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49479341/50000000000000 : ℝ)*(base8) + (269233477/100000000000000 : ℝ)*(upper1) + (360263243/50000000000000 : ℝ)*(upper2) + (172087371/50000000000000 : ℝ)*(lower4) + (18901181/50000000000000 : ℝ)*(lower5) + (1479001607717713/25000000000000 : ℝ)*(major0) + (1479001607717713/25000000000000 : ℝ)*(major1) + (1479001607717713/25000000000000 : ℝ)*(major2) + (29911128223/100000000000000 : ℝ)*(sp0) + (1517880459/2500000000000 : ℝ)*(sp1) + (196645268400901/2500000000000 : ℝ)*(sp4) + (1573156006180917/20000000000000 : ℝ)*(sp5) + (3932920373061473/50000000000000 : ℝ)*(sp6) + (495771488689917/12500000000000 : ℝ)*(sp7) + (495771488689917/12500000000000 : ℝ)*(f.failure) + (3932920373061473/50000000000000 : ℝ)*(f.sum) + (411206181439/13232421875000000000000000 : ℝ)*base66 + (827155205043038083/169375000000000000000000000000000 : ℝ)*base68 + (1600961536685538083/169375000000000000000000000000000 : ℝ)*base70 + (84723380282413083/169375000000000000000000000000000 : ℝ)*base72 + (2357377870233/1693750000000000000000000000 : ℝ)*base73 + (1302805683077413083/169375000000000000000000000000000 : ℝ)*base76 + (628541051468663083/169375000000000000000000000000000 : ℝ)*base78 + (1094467419258663083/169375000000000000000000000000000 : ℝ)*base80 + (11013868297491/3387500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (268151/156250000000000000000 : ℝ)*base89 + (268151/156250000000000000000 : ℝ)*base91 + (268151/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1126_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14041/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11331/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11333/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14039/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1126_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1126_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11333/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14039/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1126_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1126_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1126_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4159/1024 : ℝ) ≤ p) (hpb : p ≤ (8319/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18645203/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2823/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11333/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14039/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1126_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
