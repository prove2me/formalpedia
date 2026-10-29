-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1657_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:18:12.651991+00:00
-- url     : https://prove2.me/submissions/5e44b4b7-44de-4edb-b458-2642caf1d49d

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
theorem support_rectangle_w1657_s0_0 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-740225979/5000000000 : ℝ)*x 0 + (5776691513/10000000000 : ℝ)*x 1 + (4926274729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (740225979/5000000000 : ℝ)^4947 ≤ (561987609393/6250000000000 : ℝ)^3923 := by
    have hnat : (740225979 : ℕ)^4947*6250000000000^3923 ≤ 561987609393^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      740225979 5000000000 561987609393 6250000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5776691513/10000000000 : ℝ)^4947 ≤ (3128610982637/6250000000000 : ℝ)^3923 := by
    have hnat : (5776691513 : ℕ)^4947*6250000000000^3923 ≤ 3128610982637^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5776691513 10000000000 3128610982637 6250000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4926274729/10000000000 : ℝ)^4947 ≤ (5118802814729/12500000000000 : ℝ)^3923 := by
    have hnat : (4926274729 : ℕ)^4947*12500000000000^3923 ≤ 5118802814729^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4926274729 10000000000 5118802814729 12500000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-740225979/5000000000 : ℝ), (5776691513/10000000000 : ℝ), (4926274729/10000000000 : ℝ)] ![(561987609393/6250000000000 : ℝ), (3128610982637/6250000000000 : ℝ), (5118802814729/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-740225979/5000000000 : ℝ)|^4947 ≤ (561987609393/6250000000000 : ℝ)^3923
        have hw : |(-740225979/5000000000 : ℝ)|=(740225979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5776691513/10000000000 : ℝ)|^4947 ≤ (3128610982637/6250000000000 : ℝ)^3923
        have hw : |(5776691513/10000000000 : ℝ)|=(5776691513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4926274729/10000000000 : ℝ)|^4947 ≤ (5118802814729/12500000000000 : ℝ)^3923
        have hw : |(4926274729/10000000000 : ℝ)|=(4926274729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s0_1 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (543477107/1000000000 : ℝ)*x 0 + (-486651903/2500000000 : ℝ)*x 1 + (4926275297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543477107/1000000000 : ℝ)^4947 ≤ (5793847068167/12500000000000 : ℝ)^3923 := by
    have hnat : (543477107 : ℕ)^4947*12500000000000^3923 ≤ 5793847068167^3923*1000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543477107 1000000000 5793847068167 12500000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (486651903/2500000000 : ℝ)^4947 ≤ (793674684973/6250000000000 : ℝ)^3923 := by
    have hnat : (486651903 : ℕ)^4947*6250000000000^3923 ≤ 793674684973^3923*2500000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486651903 2500000000 793674684973 6250000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4926275297/10000000000 : ℝ)^4947 ≤ (639850444873/1562500000000 : ℝ)^3923 := by
    have hnat : (4926275297 : ℕ)^4947*1562500000000^3923 ≤ 639850444873^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4926275297 10000000000 639850444873 1562500000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543477107/1000000000 : ℝ), (-486651903/2500000000 : ℝ), (4926275297/10000000000 : ℝ)] ![(5793847068167/12500000000000 : ℝ), (793674684973/6250000000000 : ℝ), (639850444873/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543477107/1000000000 : ℝ)|^4947 ≤ (5793847068167/12500000000000 : ℝ)^3923
        have hw : |(543477107/1000000000 : ℝ)|=(543477107/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-486651903/2500000000 : ℝ)|^4947 ≤ (793674684973/6250000000000 : ℝ)^3923
        have hw : |(-486651903/2500000000 : ℝ)|=(486651903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4926275297/10000000000 : ℝ)|^4947 ≤ (639850444873/1562500000000 : ℝ)^3923
        have hw : |(4926275297/10000000000 : ℝ)|=(4926275297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s0_2 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1086954439/2000000000 : ℝ)*x 0 + (2463137241/5000000000 : ℝ)*x 1 + (-97330359/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086954439/2000000000 : ℝ)^4947 ≤ (11587697161101/25000000000000 : ℝ)^3923 := by
    have hnat : (1086954439 : ℕ)^4947*25000000000000^3923 ≤ 11587697161101^3923*2000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086954439 2000000000 11587697161101 25000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2463137241/5000000000 : ℝ)^4947 ≤ (5118802491083/12500000000000 : ℝ)^3923 := by
    have hnat : (2463137241 : ℕ)^4947*12500000000000^3923 ≤ 5118802491083^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2463137241 5000000000 5118802491083 12500000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (97330359/500000000 : ℝ)^4947 ≤ (12698791405781/100000000000000 : ℝ)^3923 := by
    have hnat : (97330359 : ℕ)^4947*100000000000000^3923 ≤ 12698791405781^3923*500000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97330359 500000000 12698791405781 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086954439/2000000000 : ℝ), (2463137241/5000000000 : ℝ), (-97330359/500000000 : ℝ)] ![(11587697161101/25000000000000 : ℝ), (5118802491083/12500000000000 : ℝ), (12698791405781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086954439/2000000000 : ℝ)|^4947 ≤ (11587697161101/25000000000000 : ℝ)^3923
        have hw : |(1086954439/2000000000 : ℝ)|=(1086954439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2463137241/5000000000 : ℝ)|^4947 ≤ (5118802491083/12500000000000 : ℝ)^3923
        have hw : |(2463137241/5000000000 : ℝ)|=(2463137241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-97330359/500000000 : ℝ)|^4947 ≤ (12698791405781/100000000000000 : ℝ)^3923
        have hw : |(-97330359/500000000 : ℝ)|=(97330359/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s0_3 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2043675601/5000000000 : ℝ)*x 0 + (771099579/2500000000 : ℝ)*x 1 + (5304055637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2043675601/5000000000 : ℝ)^4947 ≤ (1011273717561/3125000000000 : ℝ)^3923 := by
    have hnat : (2043675601 : ℕ)^4947*3125000000000^3923 ≤ 1011273717561^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043675601 5000000000 1011273717561 3125000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (771099579/2500000000 : ℝ)^4947 ≤ (22689833862651/100000000000000 : ℝ)^3923 := by
    have hnat : (771099579 : ℕ)^4947*100000000000000^3923 ≤ 22689833862651^3923*2500000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771099579 2500000000 22689833862651 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5304055637/10000000000 : ℝ)^4947 ≤ (44949407157233/100000000000000 : ℝ)^3923 := by
    have hnat : (5304055637 : ℕ)^4947*100000000000000^3923 ≤ 44949407157233^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304055637 10000000000 44949407157233 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2043675601/5000000000 : ℝ), (771099579/2500000000 : ℝ), (5304055637/10000000000 : ℝ)] ![(1011273717561/3125000000000 : ℝ), (22689833862651/100000000000000 : ℝ), (44949407157233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2043675601/5000000000 : ℝ)|^4947 ≤ (1011273717561/3125000000000 : ℝ)^3923
        have hw : |(2043675601/5000000000 : ℝ)|=(2043675601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(771099579/2500000000 : ℝ)|^4947 ≤ (22689833862651/100000000000000 : ℝ)^3923
        have hw : |(771099579/2500000000 : ℝ)|=(771099579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5304055637/10000000000 : ℝ)|^4947 ≤ (44949407157233/100000000000000 : ℝ)^3923
        have hw : |(5304055637/10000000000 : ℝ)|=(5304055637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s0_4 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-741335237/5000000000 : ℝ)*x 0 + (4947290581/10000000000 : ℝ)*x 1 + (5754954159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (741335237/5000000000 : ℝ)^4947 ≤ (9008796840359/100000000000000 : ℝ)^3923 := by
    have hnat : (741335237 : ℕ)^4947*100000000000000^3923 ≤ 9008796840359^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      741335237 5000000000 9008796840359 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4947290581/10000000000 : ℝ)^4947 ≤ (10292710737101/25000000000000 : ℝ)^3923 := by
    have hnat : (4947290581 : ℕ)^4947*25000000000000^3923 ≤ 10292710737101^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4947290581 10000000000 10292710737101 25000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5754954159/10000000000 : ℝ)^4947 ≤ (24910180098417/50000000000000 : ℝ)^3923 := by
    have hnat : (5754954159 : ℕ)^4947*50000000000000^3923 ≤ 24910180098417^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5754954159 10000000000 24910180098417 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-741335237/5000000000 : ℝ), (4947290581/10000000000 : ℝ), (5754954159/10000000000 : ℝ)] ![(9008796840359/100000000000000 : ℝ), (10292710737101/25000000000000 : ℝ), (24910180098417/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-741335237/5000000000 : ℝ)|^4947 ≤ (9008796840359/100000000000000 : ℝ)^3923
        have hw : |(-741335237/5000000000 : ℝ)|=(741335237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4947290581/10000000000 : ℝ)|^4947 ≤ (10292710737101/25000000000000 : ℝ)^3923
        have hw : |(4947290581/10000000000 : ℝ)|=(4947290581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5754954159/10000000000 : ℝ)|^4947 ≤ (24910180098417/50000000000000 : ℝ)^3923
        have hw : |(5754954159/10000000000 : ℝ)|=(5754954159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s0_5 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16258643/31250000 : ℝ)*x 0 + (-1117929161/10000000000 : ℝ)*x 1 + (5754954363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16258643/31250000 : ℝ)^4947 ≤ (21934836762257/50000000000000 : ℝ)^3923 := by
    have hnat : (16258643 : ℕ)^4947*50000000000000^3923 ≤ 21934836762257^3923*31250000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16258643 31250000 21934836762257 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1117929161/10000000000 : ℝ)^4947 ≤ (3154982020069/50000000000000 : ℝ)^3923 := by
    have hnat : (1117929161 : ℕ)^4947*50000000000000^3923 ≤ 3154982020069^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117929161 10000000000 3154982020069 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5754954363/10000000000 : ℝ)^4947 ≤ (49820362423827/100000000000000 : ℝ)^3923 := by
    have hnat : (5754954363 : ℕ)^4947*100000000000000^3923 ≤ 49820362423827^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5754954363 10000000000 49820362423827 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16258643/31250000 : ℝ), (-1117929161/10000000000 : ℝ), (5754954363/10000000000 : ℝ)] ![(21934836762257/50000000000000 : ℝ), (3154982020069/50000000000000 : ℝ), (49820362423827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16258643/31250000 : ℝ)|^4947 ≤ (21934836762257/50000000000000 : ℝ)^3923
        have hw : |(16258643/31250000 : ℝ)|=(16258643/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1117929161/10000000000 : ℝ)|^4947 ≤ (3154982020069/50000000000000 : ℝ)^3923
        have hw : |(-1117929161/10000000000 : ℝ)|=(1117929161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5754954363/10000000000 : ℝ)|^4947 ≤ (49820362423827/100000000000000 : ℝ)^3923
        have hw : |(5754954363/10000000000 : ℝ)|=(5754954363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s0_6 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5202766059/10000000000 : ℝ)*x 0 + (1150990967/2000000000 : ℝ)*x 1 + (-111792799/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5202766059/10000000000 : ℝ)^4947 ≤ (8773935340753/20000000000000 : ℝ)^3923 := by
    have hnat : (5202766059 : ℕ)^4947*20000000000000^3923 ≤ 8773935340753^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202766059 10000000000 8773935340753 20000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1150990967/2000000000 : ℝ)^4947 ≤ (12455091894119/25000000000000 : ℝ)^3923 := by
    have hnat : (1150990967 : ℕ)^4947*25000000000000^3923 ≤ 12455091894119^3923*2000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1150990967 2000000000 12455091894119 25000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111792799/1000000000 : ℝ)^4947 ≤ (6309955705379/100000000000000 : ℝ)^3923 := by
    have hnat : (111792799 : ℕ)^4947*100000000000000^3923 ≤ 6309955705379^3923*1000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111792799 1000000000 6309955705379 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5202766059/10000000000 : ℝ), (1150990967/2000000000 : ℝ), (-111792799/1000000000 : ℝ)] ![(8773935340753/20000000000000 : ℝ), (12455091894119/25000000000000 : ℝ), (6309955705379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5202766059/10000000000 : ℝ)|^4947 ≤ (8773935340753/20000000000000 : ℝ)^3923
        have hw : |(5202766059/10000000000 : ℝ)|=(5202766059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1150990967/2000000000 : ℝ)|^4947 ≤ (12455091894119/25000000000000 : ℝ)^3923
        have hw : |(1150990967/2000000000 : ℝ)|=(1150990967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-111792799/1000000000 : ℝ)|^4947 ≤ (6309955705379/100000000000000 : ℝ)^3923
        have hw : |(-111792799/1000000000 : ℝ)|=(111792799/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s0_7 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4093140871/10000000000 : ℝ)*x 0 + (2624601163/5000000000 : ℝ)*x 1 + (785284067/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4093140871/10000000000 : ℝ)^4947 ≤ (16209286568477/50000000000000 : ℝ)^3923 := by
    have hnat : (4093140871 : ℕ)^4947*50000000000000^3923 ≤ 16209286568477^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4093140871 10000000000 16209286568477 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2624601163/5000000000 : ℝ)^4947 ≤ (22182002533407/50000000000000 : ℝ)^3923 := by
    have hnat : (2624601163 : ℕ)^4947*50000000000000^3923 ≤ 22182002533407^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2624601163 5000000000 22182002533407 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (785284067/2500000000 : ℝ)^4947 ≤ (23217421781843/100000000000000 : ℝ)^3923 := by
    have hnat : (785284067 : ℕ)^4947*100000000000000^3923 ≤ 23217421781843^3923*2500000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      785284067 2500000000 23217421781843 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4093140871/10000000000 : ℝ), (2624601163/5000000000 : ℝ), (785284067/2500000000 : ℝ)] ![(16209286568477/50000000000000 : ℝ), (22182002533407/50000000000000 : ℝ), (23217421781843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4093140871/10000000000 : ℝ)|^4947 ≤ (16209286568477/50000000000000 : ℝ)^3923
        have hw : |(4093140871/10000000000 : ℝ)|=(4093140871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2624601163/5000000000 : ℝ)|^4947 ≤ (22182002533407/50000000000000 : ℝ)^3923
        have hw : |(2624601163/5000000000 : ℝ)|=(2624601163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(785284067/2500000000 : ℝ)|^4947 ≤ (23217421781843/100000000000000 : ℝ)^3923
        have hw : |(785284067/2500000000 : ℝ)|=(785284067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1657_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180504009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2489/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (23209/100000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4943/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4943 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4943*1^1024 ≤ 0^1024*1^4943 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4943 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4943/1024 : ℝ) ≤ (1199732735205609091/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4943 ≤ (1199732735205609091/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4943*100000000000000000000^1024 ≤ 1199732735205609091^1024*5^4943 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1199732735205609091 100000000000000000000 4943 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1199732735205609091/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4943/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4943 := by
      have hnat : (1 : ℕ)^1024*1^4943 ≤ 1^4943*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4943 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101199732735205609091/100000000000000000000 : ℝ) ≤ (5012368248327683/5000000000000000 : ℝ) ^ (4943/1024 : ℝ) := by
    have hpowers : (101199732735205609091/100000000000000000000 : ℝ)^1024 ≤ (5012368248327683/5000000000000000 : ℝ)^4943 := by
      have hnat : (101199732735205609091 : ℕ)^1024*5000000000000000^4943 ≤ 5012368248327683^4943*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101199732735205609091 100000000000000000000 5012368248327683 5000000000000000 1024 4943 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5012368248327683/5000000000000000 : ℝ)) (X := (101199732735205609091/100000000000000000000 : ℝ)) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51199732735205609091/50000000000000000000 : ℝ) ≤ (2512368248327683/2500000000000000 : ℝ) ^ (4943/1024 : ℝ) := by
    have hpowers : (51199732735205609091/50000000000000000000 : ℝ)^1024 ≤ (2512368248327683/2500000000000000 : ℝ)^4943 := by
      have hnat : (51199732735205609091 : ℕ)^1024*2500000000000000^4943 ≤ 2512368248327683^4943*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51199732735205609091 50000000000000000000 2512368248327683 2500000000000000 1024 4943 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2512368248327683/2500000000000000 : ℝ)) (X := (51199732735205609091/50000000000000000000 : ℝ)) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(12368248327683/2000000000000000 : ℝ)*(0 : ℝ))^(4943/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(12368248327683/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1199732735205609091/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(12368248327683/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4943/1024 : ℝ) := by
    rw [show (1 : ℝ)+(12368248327683/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5012368248327683/5000000000000000 : ℝ) by norm_num, show 1+(1199732735205609091/100000000000000000000 : ℝ)+(0 : ℝ)=(101199732735205609091/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1199732735205609091/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(12368248327683/2000000000000000 : ℝ)*(2/5 : ℝ))^(4943/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(12368248327683/2000000000000000 : ℝ)*(2/5 : ℝ)=(2512368248327683/2500000000000000 : ℝ) by norm_num, show 1+2*(1199732735205609091/100000000000000000000 : ℝ)=(51199732735205609091/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(12368248327683/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4943/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12368248327683/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(12368248327683/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4943/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12368248327683/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(12368248327683/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4943/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12368248327683/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-740225979/5000000000 : ℝ)*X 0 0+(5776691513/10000000000 : ℝ)*X 0 1+(4926274729/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((543477107/1000000000 : ℝ)*X 1 0+(-486651903/2500000000 : ℝ)*X 1 1+(4926275297/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1086954439/2000000000 : ℝ)*X 2 0+(2463137241/5000000000 : ℝ)*X 2 1+(-97330359/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2043675601/5000000000 : ℝ)*X 0 0+(771099579/2500000000 : ℝ)*X 0 1+(5304055637/10000000000 : ℝ)*X 0 2+(2043675601/5000000000 : ℝ)*X 1 0+(771099579/2500000000 : ℝ)*X 1 1+(5304055637/10000000000 : ℝ)*X 1 2+(2043675601/5000000000 : ℝ)*X 2 0+(771099579/2500000000 : ℝ)*X 2 1+(5304055637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-741335237/5000000000 : ℝ)*X 0 0+(4947290581/10000000000 : ℝ)*X 0 1+(5754954159/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((16258643/31250000 : ℝ)*X 1 0+(-1117929161/10000000000 : ℝ)*X 1 1+(5754954363/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5202766059/10000000000 : ℝ)*X 2 0+(1150990967/2000000000 : ℝ)*X 2 1+(-111792799/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4093140871/10000000000 : ℝ)*X 0 0+(2624601163/5000000000 : ℝ)*X 0 1+(785284067/2500000000 : ℝ)*X 0 2+(4093140871/10000000000 : ℝ)*X 1 0+(2624601163/5000000000 : ℝ)*X 1 1+(785284067/2500000000 : ℝ)*X 1 2+(4093140871/10000000000 : ℝ)*X 2 0+(2624601163/5000000000 : ℝ)*X 2 1+(785284067/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (680772604942262386600011/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28906963/20000000000000 : ℝ)*(base1) + (1262182869/100000000000000 : ℝ)*(base19) + (752797743/50000000000000 : ℝ)*(base23) + (55935851/100000000000000 : ℝ)*(upper3) + (26568023/10000000000000 : ℝ)*(upper5) + (813215149211313/100000000000000 : ℝ)*(major0) + (813215149211313/100000000000000 : ℝ)*(major1) + (813215149211313/100000000000000 : ℝ)*(major2) + (587949257010713/50000000000000 : ℝ)*(sp0) + (1175904107001977/100000000000000 : ℝ)*(sp1) + (14698798294867/1250000000000 : ℝ)*(sp2) + (225261237078403/50000000000000 : ℝ)*(sp3) + (3499849117/50000000000000 : ℝ)*(sp4) + (32556593/1562500000000 : ℝ)*(sp7) + (112631175578393/25000000000000 : ℝ)*(f.failure) + (587952684592423/50000000000000 : ℝ)*(f.sum) + (431389963322221/100000000000000000000000000000 : ℝ)*base66 + (328470526677779/200000000000000000000000000000 : ℝ)*base67 + (1193865228922221/200000000000000000000000000000 : ℝ)*base70 + (1780068644122221/200000000000000000000000000000 : ℝ)*base72 + (107113622277779/100000000000000000000000000000 : ℝ)*base73 + (684597910722221/200000000000000000000000000000 : ℝ)*base76 + (1298756606122221/200000000000000000000000000000 : ℝ)*base78 + (1093493478922221/200000000000000000000000000000 : ℝ)*base80 + (413347941122221/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (5277537/2500000000000000000000 : ℝ)*base89 + (5277537/2500000000000000000000 : ℝ)*base91 + (5277537/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (87827986360292649998643/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (200882673/25000000000000 : ℝ)*(base19) + (19215099/2000000000000 : ℝ)*(base23) + (54738163/50000000000000 : ℝ)*(base32) + (4644173/3125000000000 : ℝ)*(upper3) + (47521119/50000000000000 : ℝ)*(upper5) + (107031723335069/12500000000000 : ℝ)*(major0) + (107031723335069/12500000000000 : ℝ)*(major1) + (107031723335069/12500000000000 : ℝ)*(major2) + (525527809/20000000000000 : ℝ)*(sp1) + (284858819/6250000000000 : ℝ)*(sp2) + (619069522968347/50000000000000 : ℝ)*(sp4) + (309533903691739/25000000000000 : ℝ)*(sp5) + (967291818313/78125000000 : ℝ)*(sp6) + (118592045935029/25000000000000 : ℝ)*(sp7) + (237184146608221/50000000000000 : ℝ)*(f.failure) + (619069522968347/50000000000000 : ℝ)*(f.sum) + (10499633584873/12500000000000000000000000000 : ℝ)*base66 + (24193008334873/25000000000000000000000000000 : ℝ)*base68 + (89316718434873/25000000000000000000000000000 : ℝ)*base70 + (5023323765127/25000000000000000000000000000 : ℝ)*base71 + (45434474584873/12500000000000000000000000000 : ℝ)*base74 + (203418530390127/25000000000000000000000000000 : ℝ)*base75 + (61713665515127/25000000000000000000000000000 : ℝ)*base77 + (24011091184873/25000000000000000000000000000 : ℝ)*base80 + (54651867184873/12500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (42857989/5000000000000000000000 : ℝ)*base89 + (42857989/5000000000000000000000 : ℝ)*base91 + (42857989/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1657_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180504009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2489/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (23209/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1657_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1657_s1_0 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1583471957/10000000000 : ℝ)*x 0 + (2745558163/5000000000 : ℝ)*x 1 + (5144829873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1583471957/10000000000 : ℝ)^4947 ≤ (1223485727161/12500000000000 : ℝ)^3923 := by
    have hnat : (1583471957 : ℕ)^4947*12500000000000^3923 ≤ 1223485727161^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583471957 10000000000 1223485727161 12500000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2745558163/5000000000 : ℝ)^4947 ≤ (2934848263197/6250000000000 : ℝ)^3923 := by
    have hnat : (2745558163 : ℕ)^4947*6250000000000^3923 ≤ 2934848263197^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745558163 5000000000 2934848263197 6250000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5144829873/10000000000 : ℝ)^4947 ≤ (10813635488879/25000000000000 : ℝ)^3923 := by
    have hnat : (5144829873 : ℕ)^4947*25000000000000^3923 ≤ 10813635488879^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5144829873 10000000000 10813635488879 25000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1583471957/10000000000 : ℝ), (2745558163/5000000000 : ℝ), (5144829873/10000000000 : ℝ)] ![(1223485727161/12500000000000 : ℝ), (2934848263197/6250000000000 : ℝ), (10813635488879/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1583471957/10000000000 : ℝ)|^4947 ≤ (1223485727161/12500000000000 : ℝ)^3923
        have hw : |(-1583471957/10000000000 : ℝ)|=(1583471957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2745558163/5000000000 : ℝ)|^4947 ≤ (2934848263197/6250000000000 : ℝ)^3923
        have hw : |(2745558163/5000000000 : ℝ)|=(2745558163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5144829873/10000000000 : ℝ)|^4947 ≤ (10813635488879/25000000000000 : ℝ)^3923
        have hw : |(5144829873/10000000000 : ℝ)|=(5144829873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s1_1 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358809943/10000000000 : ℝ)*x 0 + (-440834581/2500000000 : ℝ)*x 1 + (5144829693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358809943/10000000000 : ℝ)^4947 ≤ (45535330805483/100000000000000 : ℝ)^3923 := by
    have hnat : (5358809943 : ℕ)^4947*100000000000000^3923 ≤ 45535330805483^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358809943 10000000000 45535330805483 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440834581/2500000000 : ℝ)^4947 ≤ (11210129125753/100000000000000 : ℝ)^3923 := by
    have hnat : (440834581 : ℕ)^4947*100000000000000^3923 ≤ 11210129125753^3923*2500000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440834581 2500000000 11210129125753 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5144829693/10000000000 : ℝ)^4947 ≤ (43254540047171/100000000000000 : ℝ)^3923 := by
    have hnat : (5144829693 : ℕ)^4947*100000000000000^3923 ≤ 43254540047171^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5144829693 10000000000 43254540047171 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358809943/10000000000 : ℝ), (-440834581/2500000000 : ℝ), (5144829693/10000000000 : ℝ)] ![(45535330805483/100000000000000 : ℝ), (11210129125753/100000000000000 : ℝ), (43254540047171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358809943/10000000000 : ℝ)|^4947 ≤ (45535330805483/100000000000000 : ℝ)^3923
        have hw : |(5358809943/10000000000 : ℝ)|=(5358809943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-440834581/2500000000 : ℝ)|^4947 ≤ (11210129125753/100000000000000 : ℝ)^3923
        have hw : |(-440834581/2500000000 : ℝ)|=(440834581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5144829693/10000000000 : ℝ)|^4947 ≤ (43254540047171/100000000000000 : ℝ)^3923
        have hw : |(5144829693/10000000000 : ℝ)|=(5144829693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s1_2 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2679404697/5000000000 : ℝ)*x 0 + (5144830277/10000000000 : ℝ)*x 1 + (-881669143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679404697/5000000000 : ℝ)^4947 ≤ (45535324922791/100000000000000 : ℝ)^3923 := by
    have hnat : (2679404697 : ℕ)^4947*100000000000000^3923 ≤ 45535324922791^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679404697 5000000000 45535324922791 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5144830277/10000000000 : ℝ)^4947 ≤ (43254546238689/100000000000000 : ℝ)^3923 := by
    have hnat : (5144830277 : ℕ)^4947*100000000000000^3923 ≤ 43254546238689^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5144830277 10000000000 43254546238689 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (881669143/5000000000 : ℝ)^4947 ≤ (2802532205279/25000000000000 : ℝ)^3923 := by
    have hnat : (881669143 : ℕ)^4947*25000000000000^3923 ≤ 2802532205279^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881669143 5000000000 2802532205279 25000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679404697/5000000000 : ℝ), (5144830277/10000000000 : ℝ), (-881669143/5000000000 : ℝ)] ![(45535324922791/100000000000000 : ℝ), (43254546238689/100000000000000 : ℝ), (2802532205279/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679404697/5000000000 : ℝ)|^4947 ≤ (45535324922791/100000000000000 : ℝ)^3923
        have hw : |(2679404697/5000000000 : ℝ)|=(2679404697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5144830277/10000000000 : ℝ)|^4947 ≤ (43254546238689/100000000000000 : ℝ)^3923
        have hw : |(5144830277/10000000000 : ℝ)|=(5144830277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-881669143/5000000000 : ℝ)|^4947 ≤ (2802532205279/25000000000000 : ℝ)^3923
        have hw : |(-881669143/5000000000 : ℝ)|=(881669143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s1_3 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4168513193/10000000000 : ℝ)*x 0 + (466768071/1250000000 : ℝ)*x 1 + (1811711/3906250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4168513193/10000000000 : ℝ)^4947 ≤ (4146645273809/12500000000000 : ℝ)^3923 := by
    have hnat : (4168513193 : ℕ)^4947*12500000000000^3923 ≤ 4146645273809^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4168513193 10000000000 4146645273809 12500000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (466768071/1250000000 : ℝ)^4947 ≤ (28875029331563/100000000000000 : ℝ)^3923 := by
    have hnat : (466768071 : ℕ)^4947*100000000000000^3923 ≤ 28875029331563^3923*1250000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466768071 1250000000 28875029331563 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1811711/3906250 : ℝ)^4947 ≤ (37951808464303/100000000000000 : ℝ)^3923 := by
    have hnat : (1811711 : ℕ)^4947*100000000000000^3923 ≤ 37951808464303^3923*3906250^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1811711 3906250 37951808464303 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4168513193/10000000000 : ℝ), (466768071/1250000000 : ℝ), (1811711/3906250 : ℝ)] ![(4146645273809/12500000000000 : ℝ), (28875029331563/100000000000000 : ℝ), (37951808464303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4168513193/10000000000 : ℝ)|^4947 ≤ (4146645273809/12500000000000 : ℝ)^3923
        have hw : |(4168513193/10000000000 : ℝ)|=(4168513193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(466768071/1250000000 : ℝ)|^4947 ≤ (28875029331563/100000000000000 : ℝ)^3923
        have hw : |(466768071/1250000000 : ℝ)|=(466768071/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1811711/3906250 : ℝ)|^4947 ≤ (37951808464303/100000000000000 : ℝ)^3923
        have hw : |(1811711/3906250 : ℝ)|=(1811711/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s1_4 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-791809563/5000000000 : ℝ)*x 0 + (5148305917/10000000000 : ℝ)*x 1 + (548759191/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (791809563/5000000000 : ℝ)^4947 ≤ (4894516488289/50000000000000 : ℝ)^3923 := by
    have hnat : (791809563 : ℕ)^4947*50000000000000^3923 ≤ 4894516488289^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      791809563 5000000000 4894516488289 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5148305917/10000000000 : ℝ)^4947 ≤ (43291397926231/100000000000000 : ℝ)^3923 := by
    have hnat : (5148305917 : ℕ)^4947*100000000000000^3923 ≤ 43291397926231^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5148305917 10000000000 43291397926231 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548759191/1000000000 : ℝ)^4947 ≤ (46919569080907/100000000000000 : ℝ)^3923 := by
    have hnat : (548759191 : ℕ)^4947*100000000000000^3923 ≤ 46919569080907^3923*1000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548759191 1000000000 46919569080907 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-791809563/5000000000 : ℝ), (5148305917/10000000000 : ℝ), (548759191/1000000000 : ℝ)] ![(4894516488289/50000000000000 : ℝ), (43291397926231/100000000000000 : ℝ), (46919569080907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-791809563/5000000000 : ℝ)|^4947 ≤ (4894516488289/50000000000000 : ℝ)^3923
        have hw : |(-791809563/5000000000 : ℝ)|=(791809563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5148305917/10000000000 : ℝ)|^4947 ≤ (43291397926231/100000000000000 : ℝ)^3923
        have hw : |(5148305917/10000000000 : ℝ)|=(5148305917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(548759191/1000000000 : ℝ)|^4947 ≤ (46919569080907/100000000000000 : ℝ)^3923
        have hw : |(548759191/1000000000 : ℝ)|=(548759191/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s1_5 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266156751/10000000000 : ℝ)*x 0 + (-44393009/312500000 : ℝ)*x 1 + (5487591959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266156751/10000000000 : ℝ)^4947 ≤ (22272387665141/50000000000000 : ℝ)^3923 := by
    have hnat : (5266156751 : ℕ)^4947*50000000000000^3923 ≤ 22272387665141^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266156751 10000000000 22272387665141 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44393009/312500000 : ℝ)^4947 ≤ (8535655047507/100000000000000 : ℝ)^3923 := by
    have hnat : (44393009 : ℕ)^4947*100000000000000^3923 ≤ 8535655047507^3923*312500000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44393009 312500000 8535655047507 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5487591959/10000000000 : ℝ)^4947 ≤ (2345978480461/5000000000000 : ℝ)^3923 := by
    have hnat : (5487591959 : ℕ)^4947*5000000000000^3923 ≤ 2345978480461^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487591959 10000000000 2345978480461 5000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266156751/10000000000 : ℝ), (-44393009/312500000 : ℝ), (5487591959/10000000000 : ℝ)] ![(22272387665141/50000000000000 : ℝ), (8535655047507/100000000000000 : ℝ), (2345978480461/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266156751/10000000000 : ℝ)|^4947 ≤ (22272387665141/50000000000000 : ℝ)^3923
        have hw : |(5266156751/10000000000 : ℝ)|=(5266156751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44393009/312500000 : ℝ)|^4947 ≤ (8535655047507/100000000000000 : ℝ)^3923
        have hw : |(-44393009/312500000 : ℝ)|=(44393009/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5487591959/10000000000 : ℝ)|^4947 ≤ (2345978480461/5000000000000 : ℝ)^3923
        have hw : |(5487591959/10000000000 : ℝ)|=(5487591959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s1_6 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266156529/10000000000 : ℝ)*x 0 + (2743796127/5000000000 : ℝ)*x 1 + (-1420576181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266156529/10000000000 : ℝ)^4947 ≤ (44544772962293/100000000000000 : ℝ)^3923 := by
    have hnat : (5266156529 : ℕ)^4947*100000000000000^3923 ≤ 44544772962293^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266156529 10000000000 44544772962293 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2743796127/5000000000 : ℝ)^4947 ≤ (9383914557977/20000000000000 : ℝ)^3923 := by
    have hnat : (2743796127 : ℕ)^4947*20000000000000^3923 ≤ 9383914557977^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743796127 5000000000 9383914557977 20000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1420576181/10000000000 : ℝ)^4947 ≤ (853565423677/10000000000000 : ℝ)^3923 := by
    have hnat : (1420576181 : ℕ)^4947*10000000000000^3923 ≤ 853565423677^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1420576181 10000000000 853565423677 10000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266156529/10000000000 : ℝ), (2743796127/5000000000 : ℝ), (-1420576181/10000000000 : ℝ)] ![(44544772962293/100000000000000 : ℝ), (9383914557977/20000000000000 : ℝ), (853565423677/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266156529/10000000000 : ℝ)|^4947 ≤ (44544772962293/100000000000000 : ℝ)^3923
        have hw : |(5266156529/10000000000 : ℝ)|=(5266156529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2743796127/5000000000 : ℝ)|^4947 ≤ (9383914557977/20000000000000 : ℝ)^3923
        have hw : |(2743796127/5000000000 : ℝ)|=(2743796127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1420576181/10000000000 : ℝ)|^4947 ≤ (853565423677/10000000000000 : ℝ)^3923
        have hw : |(-1420576181/10000000000 : ℝ)|=(1420576181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s1_7 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1042224421/2500000000 : ℝ)*x 0 + (231445393/500000000 : ℝ)*x 1 + (3743343867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042224421/2500000000 : ℝ)^4947 ≤ (1658851035499/5000000000000 : ℝ)^3923 := by
    have hnat : (1042224421 : ℕ)^4947*5000000000000^3923 ≤ 1658851035499^3923*2500000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042224421 2500000000 1658851035499 5000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (231445393/500000000 : ℝ)^4947 ≤ (37858217557781/100000000000000 : ℝ)^3923 := by
    have hnat : (231445393 : ℕ)^4947*100000000000000^3923 ≤ 37858217557781^3923*500000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231445393 500000000 37858217557781 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3743343867/10000000000 : ℝ)^4947 ≤ (14482380854347/50000000000000 : ℝ)^3923 := by
    have hnat : (3743343867 : ℕ)^4947*50000000000000^3923 ≤ 14482380854347^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3743343867 10000000000 14482380854347 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1042224421/2500000000 : ℝ), (231445393/500000000 : ℝ), (3743343867/10000000000 : ℝ)] ![(1658851035499/5000000000000 : ℝ), (37858217557781/100000000000000 : ℝ), (14482380854347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1042224421/2500000000 : ℝ)|^4947 ≤ (1658851035499/5000000000000 : ℝ)^3923
        have hw : |(1042224421/2500000000 : ℝ)|=(1042224421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(231445393/500000000 : ℝ)|^4947 ≤ (37858217557781/100000000000000 : ℝ)^3923
        have hw : |(231445393/500000000 : ℝ)|=(231445393/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3743343867/10000000000 : ℝ)|^4947 ≤ (14482380854347/50000000000000 : ℝ)^3923
        have hw : |(3743343867/10000000000 : ℝ)|=(3743343867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1657_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180504009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23209/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2489/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (197/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17211/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (23209/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2489/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (23209/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2489/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (23209/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2489/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (23209/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2489/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (23209/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2489/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (23209/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2489/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2489/50000 : ℝ) ^ (4943/1024 : ℝ) ≤ (25672050796963/50000000000000000000 : ℝ) := by
    have hpowers : (2489/50000 : ℝ)^4943 ≤ (25672050796963/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2489 : ℕ)^4943*50000000000000000000^1024 ≤ 25672050796963^1024*50000^4943 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2489 50000 25672050796963 50000000000000000000 4943 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2489/50000 : ℝ)) (X := (25672050796963/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (23209/100000 : ℝ) ^ (4943/1024 : ℝ) ≤ (86682099189985363/100000000000000000000 : ℝ) := by
    have hpowers : (23209/100000 : ℝ)^4943 ≤ (86682099189985363/100000000000000000000 : ℝ)^1024 := by
      have hnat : (23209 : ℕ)^4943*100000000000000000000^1024 ≤ 86682099189985363^1024*100000^4943 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23209 100000 86682099189985363 100000000000000000000 4943 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23209/100000 : ℝ)) (X := (86682099189985363/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000025672050796963/25000000000000000000 : ℝ) ≤ (10000002127304821/10000000000000000 : ℝ) ^ (4943/1024 : ℝ) := by
    have hpowers : (25000025672050796963/25000000000000000000 : ℝ)^1024 ≤ (10000002127304821/10000000000000000 : ℝ)^4943 := by
      have hnat : (25000025672050796963 : ℕ)^1024*10000000000000000^4943 ≤ 10000002127304821^4943*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000025672050796963 25000000000000000000 10000002127304821 10000000000000000 1024 4943 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002127304821/10000000000000000 : ℝ)) (X := (25000025672050796963/25000000000000000000 : ℝ)) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100086733443291579289/100000000000000000000 : ℝ) ≤ (2000359233358889/2000000000000000 : ℝ) ^ (4943/1024 : ℝ) := by
    have hpowers : (100086733443291579289/100000000000000000000 : ℝ)^1024 ≤ (2000359233358889/2000000000000000 : ℝ)^4943 := by
      have hnat : (100086733443291579289 : ℕ)^1024*2000000000000000^4943 ≤ 2000359233358889^4943*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100086733443291579289 100000000000000000000 2000359233358889 2000000000000000 1024 4943 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000359233358889/2000000000000000 : ℝ)) (X := (100086733443291579289/100000000000000000000 : ℝ)) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50086682099189985363/50000000000000000000 : ℝ) ≤ (10003590206284069/10000000000000000 : ℝ) ^ (4943/1024 : ℝ) := by
    have hpowers : (50086682099189985363/50000000000000000000 : ℝ)^1024 ≤ (10003590206284069/10000000000000000 : ℝ)^4943 := by
      have hnat : (50086682099189985363 : ℕ)^1024*10000000000000000^4943 ≤ 10003590206284069^4943*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50086682099189985363 50000000000000000000 10003590206284069 10000000000000000 1024 4943 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003590206284069/10000000000000000 : ℝ)) (X := (50086682099189985363/50000000000000000000 : ℝ)) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(25672050796963/50000000000000000000 : ℝ) ≤ ((60764059108578498369/60770000000000000000 : ℝ)+2*(74751645401/75962500000000 : ℝ)*(2489/50000 : ℝ))^(4943/1024 : ℝ) := by
    rw [show (60764059108578498369/60770000000000000000 : ℝ)+2*(74751645401/75962500000000 : ℝ)*(2489/50000 : ℝ)=(10000002127304821/10000000000000000 : ℝ) by norm_num, show 1+2*(25672050796963/50000000000000000000 : ℝ)=(25000025672050796963/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(86682099189985363/100000000000000000000 : ℝ)+(25672050796963/50000000000000000000 : ℝ) ≤ ((60764059108578498369/60770000000000000000 : ℝ)+(74751645401/75962500000000 : ℝ)*((23209/100000 : ℝ)+(2489/50000 : ℝ)))^(4943/1024 : ℝ) := by
    rw [show (60764059108578498369/60770000000000000000 : ℝ)+(74751645401/75962500000000 : ℝ)*((23209/100000 : ℝ)+(2489/50000 : ℝ))=(2000359233358889/2000000000000000 : ℝ) by norm_num, show 1+(86682099189985363/100000000000000000000 : ℝ)+(25672050796963/50000000000000000000 : ℝ)=(100086733443291579289/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(86682099189985363/100000000000000000000 : ℝ) ≤ ((60764059108578498369/60770000000000000000 : ℝ)+2*(74751645401/75962500000000 : ℝ)*(23209/100000 : ℝ))^(4943/1024 : ℝ) := by
    rw [show (60764059108578498369/60770000000000000000 : ℝ)+2*(74751645401/75962500000000 : ℝ)*(23209/100000 : ℝ)=(10003590206284069/10000000000000000 : ℝ) by norm_num, show 1+2*(86682099189985363/100000000000000000000 : ℝ)=(50086682099189985363/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (60764059108578498369/60770000000000000000 : ℝ)*(X 1 0+X 2 0)+(74751645401/75962500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4943/1024 : ℝ)) (lo := (2489/50000 : ℝ)) (hi := (23209/100000 : ℝ)) (c := (60764059108578498369/60770000000000000000 : ℝ)) (alpha := (74751645401/75962500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (60764059108578498369/60770000000000000000 : ℝ)*(X 0 1+X 2 1)+(74751645401/75962500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4943/1024 : ℝ)) (lo := (2489/50000 : ℝ)) (hi := (23209/100000 : ℝ)) (c := (60764059108578498369/60770000000000000000 : ℝ)) (alpha := (74751645401/75962500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (60764059108578498369/60770000000000000000 : ℝ)*(X 0 2+X 1 2)+(74751645401/75962500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4943/1024 : ℝ)) (lo := (2489/50000 : ℝ)) (hi := (23209/100000 : ℝ)) (c := (60764059108578498369/60770000000000000000 : ℝ)) (alpha := (74751645401/75962500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1583471957/10000000000 : ℝ)*X 0 0+(2745558163/5000000000 : ℝ)*X 0 1+(5144829873/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5358809943/10000000000 : ℝ)*X 1 0+(-440834581/2500000000 : ℝ)*X 1 1+(5144829693/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2679404697/5000000000 : ℝ)*X 2 0+(5144830277/10000000000 : ℝ)*X 2 1+(-881669143/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4168513193/10000000000 : ℝ)*X 0 0+(466768071/1250000000 : ℝ)*X 0 1+(1811711/3906250 : ℝ)*X 0 2+(4168513193/10000000000 : ℝ)*X 1 0+(466768071/1250000000 : ℝ)*X 1 1+(1811711/3906250 : ℝ)*X 1 2+(4168513193/10000000000 : ℝ)*X 2 0+(466768071/1250000000 : ℝ)*X 2 1+(1811711/3906250 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-791809563/5000000000 : ℝ)*X 0 0+(5148305917/10000000000 : ℝ)*X 0 1+(548759191/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5266156751/10000000000 : ℝ)*X 1 0+(-44393009/312500000 : ℝ)*X 1 1+(5487591959/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5266156529/10000000000 : ℝ)*X 2 0+(2743796127/5000000000 : ℝ)*X 2 1+(-1420576181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1042224421/2500000000 : ℝ)*X 0 0+(231445393/500000000 : ℝ)*X 0 1+(3743343867/10000000000 : ℝ)*X 0 2+(1042224421/2500000000 : ℝ)*X 1 0+(231445393/500000000 : ℝ)*X 1 1+(3743343867/10000000000 : ℝ)*X 1 2+(1042224421/2500000000 : ℝ)*X 2 0+(231445393/500000000 : ℝ)*X 2 1+(3743343867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (67647741827563209130059/7596250000000000000000000000 : ℝ) := by norm_num
    linear_combination (2145594209/100000000000000 : ℝ)*(base19) + (873089491/50000000000000 : ℝ)*(base23) + (80089063/25000000000000 : ℝ)*(upper3) + (13874407/25000000000000 : ℝ)*(upper4) + (113395059/50000000000000 : ℝ)*(upper5) + (998558841670147/50000000000000 : ℝ)*(major0) + (998558841670147/50000000000000 : ℝ)*(major1) + (998558841670147/50000000000000 : ℝ)*(major2) + (1443901862500121/50000000000000 : ℝ)*(sp0) + (2887821108565811/100000000000000 : ℝ)*(sp1) + (2887821507981039/100000000000000 : ℝ)*(sp2) + (1106403589724647/100000000000000 : ℝ)*(sp3) + (9764579889/50000000000000 : ℝ)*(sp4) + (4112974409/50000000000000 : ℝ)*(sp7) + (138301476959183/12500000000000 : ℝ)*(f.failure) + (144391162708001/5000000000000 : ℝ)*(f.sum) + (60795814435167/30385000000000000000000000000 : ℝ)*base65 + (3377197318114090243/3038500000000000000000000000000000 : ℝ)*base67 + (2821323472488909757/3038500000000000000000000000000000 : ℝ)*base70 + (37048852032427090243/3038500000000000000000000000000000 : ℝ)*base71 + (41413303149617/7596250000000000000000000000 : ℝ)*base74 + (9668281733403409757/3038500000000000000000000000000000 : ℝ)*base76 + (14836136022096590243/3038500000000000000000000000000000 : ℝ)*base77 + (9606800815558409757/3038500000000000000000000000000000 : ℝ)*base80 + (30309160808017/7596250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (14135353/1250000000000000000000 : ℝ)*base90 + (14135353/1250000000000000000000 : ℝ)*base92 + (14135353/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3541386251608538393594292057/759625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (194981023/20000000000000 : ℝ)*(base19) + (954385077/100000000000000 : ℝ)*(base23) + (9617/25000000000 : ℝ)*(upper2) + (33498569/25000000000000 : ℝ)*(upper3) + (52564513/50000000000000 : ℝ)*(upper5) + (1019147155366149/50000000000000 : ℝ)*(major0) + (1019147155366149/50000000000000 : ℝ)*(major1) + (1019147155366149/50000000000000 : ℝ)*(major2) + (9346559133/100000000000000 : ℝ)*(sp1) + (5545222633/50000000000000 : ℝ)*(sp2) + (2947364621106413/100000000000000 : ℝ)*(sp4) + (589470859928433/20000000000000 : ℝ)*(sp5) + (294735257627607/10000000000000 : ℝ)*(sp6) + (35288245154923/3125000000000 : ℝ)*(sp7) + (35288245154923/3125000000000 : ℝ)*(f.failure) + (2947364621106413/100000000000000 : ℝ)*(f.sum) + (97094428525687/15192500000000000000000000000 : ℝ)*base65 + (5305484078824989019/3038500000000000000000000000000000 : ℝ)*base68 + (26529573621526510981/3038500000000000000000000000000000 : ℝ)*base69 + (15226167009010510981/3038500000000000000000000000000000 : ℝ)*base71 + (16179252760499/7596250000000000000000000000 : ℝ)*base74 + (30047644409427510981/3038500000000000000000000000000000 : ℝ)*base75 + (37213590115760510981/3038500000000000000000000000000000 : ℝ)*base77 + (4748503010646510981/3038500000000000000000000000000000 : ℝ)*base79 + (2706504330037/15192500000000000000000000000 : ℝ)*base81 + (3663693/312500000000000000000 : ℝ)*base90 + (3663693/312500000000000000000 : ℝ)*base92 + (3663693/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1657_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180504009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23209/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2489/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (197/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17211/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1657_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1657_s2_0 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-497541/3125000 : ℝ)*x 0 + (2724312527/5000000000 : ℝ)*x 1 + (2590800417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (497541/3125000 : ℝ)^4947 ≤ (1971086109781/20000000000000 : ℝ)^3923 := by
    have hnat : (497541 : ℕ)^4947*20000000000000^3923 ≤ 1971086109781^3923*3125000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497541 3125000 1971086109781 20000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2724312527/5000000000 : ℝ)^4947 ≤ (363279858517/781250000000 : ℝ)^3923 := by
    have hnat : (2724312527 : ℕ)^4947*781250000000^3923 ≤ 363279858517^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724312527 5000000000 363279858517 781250000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590800417/5000000000 : ℝ)^4947 ≤ (10911186887023/25000000000000 : ℝ)^3923 := by
    have hnat : (2590800417 : ℕ)^4947*25000000000000^3923 ≤ 10911186887023^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590800417 5000000000 10911186887023 25000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-497541/3125000 : ℝ), (2724312527/5000000000 : ℝ), (2590800417/5000000000 : ℝ)] ![(1971086109781/20000000000000 : ℝ), (363279858517/781250000000 : ℝ), (10911186887023/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-497541/3125000 : ℝ)|^4947 ≤ (1971086109781/20000000000000 : ℝ)^3923
        have hw : |(-497541/3125000 : ℝ)|=(497541/3125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2724312527/5000000000 : ℝ)|^4947 ≤ (363279858517/781250000000 : ℝ)^3923
        have hw : |(2724312527/5000000000 : ℝ)|=(2724312527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590800417/5000000000 : ℝ)|^4947 ≤ (10911186887023/25000000000000 : ℝ)^3923
        have hw : |(2590800417/5000000000 : ℝ)|=(2590800417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s2_1 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133688427/250000000 : ℝ)*x 0 + (-1729642473/10000000000 : ℝ)*x 1 + (5181601373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133688427/250000000 : ℝ)^4947 ≤ (22707286020633/50000000000000 : ℝ)^3923 := by
    have hnat : (133688427 : ℕ)^4947*50000000000000^3923 ≤ 22707286020633^3923*250000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133688427 250000000 22707286020633 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1729642473/10000000000 : ℝ)^4947 ≤ (5470337334041/50000000000000 : ℝ)^3923 := by
    have hnat : (1729642473 : ℕ)^4947*50000000000000^3923 ≤ 5470337334041^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1729642473 10000000000 5470337334041 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181601373/10000000000 : ℝ)^4947 ≤ (43644753273157/100000000000000 : ℝ)^3923 := by
    have hnat : (5181601373 : ℕ)^4947*100000000000000^3923 ≤ 43644753273157^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181601373 10000000000 43644753273157 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133688427/250000000 : ℝ), (-1729642473/10000000000 : ℝ), (5181601373/10000000000 : ℝ)] ![(22707286020633/50000000000000 : ℝ), (5470337334041/50000000000000 : ℝ), (43644753273157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133688427/250000000 : ℝ)|^4947 ≤ (22707286020633/50000000000000 : ℝ)^3923
        have hw : |(133688427/250000000 : ℝ)|=(133688427/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1729642473/10000000000 : ℝ)|^4947 ≤ (5470337334041/50000000000000 : ℝ)^3923
        have hw : |(-1729642473/10000000000 : ℝ)|=(1729642473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181601373/10000000000 : ℝ)|^4947 ≤ (43644753273157/100000000000000 : ℝ)^3923
        have hw : |(5181601373/10000000000 : ℝ)|=(5181601373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s2_2 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069507443/2000000000 : ℝ)*x 0 + (5181600979/10000000000 : ℝ)*x 1 + (-27025669/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069507443/2000000000 : ℝ)^4947 ≤ (22707286743517/50000000000000 : ℝ)^3923 := by
    have hnat : (1069507443 : ℕ)^4947*50000000000000^3923 ≤ 22707286743517^3923*2000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069507443 2000000000 22707286743517 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181600979/10000000000 : ℝ)^4947 ≤ (4364474908823/10000000000000 : ℝ)^3923 := by
    have hnat : (5181600979 : ℕ)^4947*10000000000000^3923 ≤ 4364474908823^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181600979 10000000000 4364474908823 10000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27025669/156250000 : ℝ)^4947 ≤ (2188135480803/20000000000000 : ℝ)^3923 := by
    have hnat : (27025669 : ℕ)^4947*20000000000000^3923 ≤ 2188135480803^3923*156250000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27025669 156250000 2188135480803 20000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069507443/2000000000 : ℝ), (5181600979/10000000000 : ℝ), (-27025669/156250000 : ℝ)] ![(22707286743517/50000000000000 : ℝ), (4364474908823/10000000000000 : ℝ), (2188135480803/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069507443/2000000000 : ℝ)|^4947 ≤ (22707286743517/50000000000000 : ℝ)^3923
        have hw : |(1069507443/2000000000 : ℝ)|=(1069507443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181600979/10000000000 : ℝ)|^4947 ≤ (4364474908823/10000000000000 : ℝ)^3923
        have hw : |(5181600979/10000000000 : ℝ)|=(5181600979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-27025669/156250000 : ℝ)|^4947 ≤ (2188135480803/20000000000000 : ℝ)^3923
        have hw : |(-27025669/156250000 : ℝ)|=(27025669/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s2_3 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83499577/200000000 : ℝ)*x 0 + (1918471087/5000000000 : ℝ)*x 1 + (906778957/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83499577/200000000 : ℝ)^4947 ≤ (33238059968727/100000000000000 : ℝ)^3923 := by
    have hnat : (83499577 : ℕ)^4947*100000000000000^3923 ≤ 33238059968727^3923*200000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83499577 200000000 33238059968727 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1918471087/5000000000 : ℝ)^4947 ≤ (29880999413521/100000000000000 : ℝ)^3923 := by
    have hnat : (1918471087 : ℕ)^4947*100000000000000^3923 ≤ 29880999413521^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918471087 5000000000 29880999413521 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (906778957/2000000000 : ℝ)^4947 ≤ (9220235150327/25000000000000 : ℝ)^3923 := by
    have hnat : (906778957 : ℕ)^4947*25000000000000^3923 ≤ 9220235150327^3923*2000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906778957 2000000000 9220235150327 25000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83499577/200000000 : ℝ), (1918471087/5000000000 : ℝ), (906778957/2000000000 : ℝ)] ![(33238059968727/100000000000000 : ℝ), (29880999413521/100000000000000 : ℝ), (9220235150327/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83499577/200000000 : ℝ)|^4947 ≤ (33238059968727/100000000000000 : ℝ)^3923
        have hw : |(83499577/200000000 : ℝ)|=(83499577/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1918471087/5000000000 : ℝ)|^4947 ≤ (29880999413521/100000000000000 : ℝ)^3923
        have hw : |(1918471087/5000000000 : ℝ)|=(1918471087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(906778957/2000000000 : ℝ)|^4947 ≤ (9220235150327/25000000000000 : ℝ)^3923
        have hw : |(906778957/2000000000 : ℝ)|=(906778957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s2_4 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-796099397/5000000000 : ℝ)*x 0 + (41469387/80000000 : ℝ)*x 1 + (5446530279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (796099397/5000000000 : ℝ)^4947 ≤ (1971191636127/20000000000000 : ℝ)^3923 := by
    have hnat : (796099397 : ℕ)^4947*20000000000000^3923 ≤ 1971191636127^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796099397 5000000000 1971191636127 20000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41469387/80000000 : ℝ)^4947 ≤ (43666762484393/100000000000000 : ℝ)^3923 := by
    have hnat : (41469387 : ℕ)^4947*100000000000000^3923 ≤ 43666762484393^3923*80000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41469387 80000000 43666762484393 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5446530279/10000000000 : ℝ)^4947 ≤ (46477279313441/100000000000000 : ℝ)^3923 := by
    have hnat : (5446530279 : ℕ)^4947*100000000000000^3923 ≤ 46477279313441^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446530279 10000000000 46477279313441 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-796099397/5000000000 : ℝ), (41469387/80000000 : ℝ), (5446530279/10000000000 : ℝ)] ![(1971191636127/20000000000000 : ℝ), (43666762484393/100000000000000 : ℝ), (46477279313441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-796099397/5000000000 : ℝ)|^4947 ≤ (1971191636127/20000000000000 : ℝ)^3923
        have hw : |(-796099397/5000000000 : ℝ)|=(796099397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41469387/80000000 : ℝ)|^4947 ≤ (43666762484393/100000000000000 : ℝ)^3923
        have hw : |(41469387/80000000 : ℝ)|=(41469387/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5446530279/10000000000 : ℝ)|^4947 ≤ (46477279313441/100000000000000 : ℝ)^3923
        have hw : |(5446530279/10000000000 : ℝ)|=(5446530279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s2_5 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638070259/5000000000 : ℝ)*x 0 + (-146471313/1000000000 : ℝ)*x 1 + (5446530403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638070259/5000000000 : ℝ)^4947 ≤ (44651294659771/100000000000000 : ℝ)^3923 := by
    have hnat : (2638070259 : ℕ)^4947*100000000000000^3923 ≤ 44651294659771^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638070259 5000000000 44651294659771 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (146471313/1000000000 : ℝ)^4947 ≤ (8871424668491/100000000000000 : ℝ)^3923 := by
    have hnat : (146471313 : ℕ)^4947*100000000000000^3923 ≤ 8871424668491^3923*1000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146471313 1000000000 8871424668491 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5446530403/10000000000 : ℝ)^4947 ≤ (46477280647779/100000000000000 : ℝ)^3923 := by
    have hnat : (5446530403 : ℕ)^4947*100000000000000^3923 ≤ 46477280647779^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446530403 10000000000 46477280647779 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638070259/5000000000 : ℝ), (-146471313/1000000000 : ℝ), (5446530403/10000000000 : ℝ)] ![(44651294659771/100000000000000 : ℝ), (8871424668491/100000000000000 : ℝ), (46477280647779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638070259/5000000000 : ℝ)|^4947 ≤ (44651294659771/100000000000000 : ℝ)^3923
        have hw : |(2638070259/5000000000 : ℝ)|=(2638070259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-146471313/1000000000 : ℝ)|^4947 ≤ (8871424668491/100000000000000 : ℝ)^3923
        have hw : |(-146471313/1000000000 : ℝ)|=(146471313/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5446530403/10000000000 : ℝ)|^4947 ≤ (46477280647779/100000000000000 : ℝ)^3923
        have hw : |(5446530403/10000000000 : ℝ)|=(5446530403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s2_6 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164879399/312500000 : ℝ)*x 0 + (5446530037/10000000000 : ℝ)*x 1 + (-1464713297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164879399/312500000 : ℝ)^4947 ≤ (44651297327743/100000000000000 : ℝ)^3923 := by
    have hnat : (164879399 : ℕ)^4947*100000000000000^3923 ≤ 44651297327743^3923*312500000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164879399 312500000 44651297327743 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5446530037/10000000000 : ℝ)^4947 ≤ (2904829794333/6250000000000 : ℝ)^3923 := by
    have hnat : (5446530037 : ℕ)^4947*6250000000000^3923 ≤ 2904829794333^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446530037 10000000000 2904829794333 6250000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1464713297/10000000000 : ℝ)^4947 ≤ (8871425943993/100000000000000 : ℝ)^3923 := by
    have hnat : (1464713297 : ℕ)^4947*100000000000000^3923 ≤ 8871425943993^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1464713297 10000000000 8871425943993 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164879399/312500000 : ℝ), (5446530037/10000000000 : ℝ), (-1464713297/10000000000 : ℝ)] ![(44651297327743/100000000000000 : ℝ), (2904829794333/6250000000000 : ℝ), (8871425943993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164879399/312500000 : ℝ)|^4947 ≤ (44651297327743/100000000000000 : ℝ)^3923
        have hw : |(164879399/312500000 : ℝ)|=(164879399/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5446530037/10000000000 : ℝ)|^4947 ≤ (2904829794333/6250000000000 : ℝ)^3923
        have hw : |(5446530037/10000000000 : ℝ)|=(5446530037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1464713297/10000000000 : ℝ)|^4947 ≤ (8871425943993/100000000000000 : ℝ)^3923
        have hw : |(-1464713297/10000000000 : ℝ)|=(1464713297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1657_s2_7 (p : ℝ) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2087578031/5000000000 : ℝ)*x 0 + (4528486451/10000000000 : ℝ)*x 1 + (3842408281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2087578031/5000000000 : ℝ)^4947 ≤ (16619919534697/50000000000000 : ℝ)^3923 := by
    have hnat : (2087578031 : ℕ)^4947*50000000000000^3923 ≤ 16619919534697^3923*5000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087578031 5000000000 16619919534697 50000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4528486451/10000000000 : ℝ)^4947 ≤ (36825471641747/100000000000000 : ℝ)^3923 := by
    have hnat : (4528486451 : ℕ)^4947*100000000000000^3923 ≤ 36825471641747^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4528486451 10000000000 36825471641747 100000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3842408281/10000000000 : ℝ)^4947 ≤ (7483672319497/25000000000000 : ℝ)^3923 := by
    have hnat : (3842408281 : ℕ)^4947*25000000000000^3923 ≤ 7483672319497^3923*10000000000^4947 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3842408281 10000000000 7483672319497 25000000000000 4947 3923 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4947/1024 : ℝ)) 4947 3923 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2087578031/5000000000 : ℝ), (4528486451/10000000000 : ℝ), (3842408281/10000000000 : ℝ)] ![(16619919534697/50000000000000 : ℝ), (36825471641747/100000000000000 : ℝ), (7483672319497/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2087578031/5000000000 : ℝ)|^4947 ≤ (16619919534697/50000000000000 : ℝ)^3923
        have hw : |(2087578031/5000000000 : ℝ)|=(2087578031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4528486451/10000000000 : ℝ)|^4947 ≤ (36825471641747/100000000000000 : ℝ)^3923
        have hw : |(4528486451/10000000000 : ℝ)|=(4528486451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3842408281/10000000000 : ℝ)|^4947 ≤ (7483672319497/25000000000000 : ℝ)^3923
        have hw : |(3842408281/10000000000 : ℝ)|=(3842408281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1657_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180504009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17211/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (197/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (2661/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16323/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17211/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (197/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17211/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (197/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17211/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (197/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17211/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (197/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17211/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (197/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17211/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (197/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (197/2000 : ℝ) ^ (4943/1024 : ℝ) ≤ (1384099375844391/100000000000000000000 : ℝ) := by
    have hpowers : (197/2000 : ℝ)^4943 ≤ (1384099375844391/100000000000000000000 : ℝ)^1024 := by
      have hnat : (197 : ℕ)^4943*100000000000000000000^1024 ≤ 1384099375844391^1024*2000^4943 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        197 2000 1384099375844391 100000000000000000000 4943 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (197/2000 : ℝ)) (X := (1384099375844391/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17211/100000 : ℝ) ^ (4943/1024 : ℝ) ≤ (10235112867982739/50000000000000000000 : ℝ) := by
    have hpowers : (17211/100000 : ℝ)^4943 ≤ (10235112867982739/50000000000000000000 : ℝ)^1024 := by
      have hnat : (17211 : ℕ)^4943*50000000000000000000^1024 ≤ 10235112867982739^1024*100000^4943 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17211 100000 10235112867982739 50000000000000000000 4943 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17211/100000 : ℝ)) (X := (10235112867982739/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001384099375844391/50000000000000000000 : ℝ) ≤ (10000057345830789/10000000000000000 : ℝ) ^ (4943/1024 : ℝ) := by
    have hpowers : (50001384099375844391/50000000000000000000 : ℝ)^1024 ≤ (10000057345830789/10000000000000000 : ℝ)^4943 := by
      have hnat : (50001384099375844391 : ℕ)^1024*10000000000000000^4943 ≤ 10000057345830789^4943*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001384099375844391 50000000000000000000 10000057345830789 10000000000000000 1024 4943 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000057345830789/10000000000000000 : ℝ)) (X := (50001384099375844391/50000000000000000000 : ℝ)) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100021854325111809869/100000000000000000000 : ℝ) ≤ (10000452698571389/10000000000000000 : ℝ) ^ (4943/1024 : ℝ) := by
    have hpowers : (100021854325111809869/100000000000000000000 : ℝ)^1024 ≤ (10000452698571389/10000000000000000 : ℝ)^4943 := by
      have hnat : (100021854325111809869 : ℕ)^1024*10000000000000000^4943 ≤ 10000452698571389^4943*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100021854325111809869 100000000000000000000 10000452698571389 10000000000000000 1024 4943 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000452698571389/10000000000000000 : ℝ)) (X := (100021854325111809869/100000000000000000000 : ℝ)) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010235112867982739/25000000000000000000 : ℝ) ≤ (10000848051311989/10000000000000000 : ℝ) ^ (4943/1024 : ℝ) := by
    have hpowers : (25010235112867982739/25000000000000000000 : ℝ)^1024 ≤ (10000848051311989/10000000000000000 : ℝ)^4943 := by
      have hnat : (25010235112867982739 : ℕ)^1024*10000000000000000^4943 ≤ 10000848051311989^4943*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010235112867982739 25000000000000000000 10000848051311989 10000000000000000 1024 4943 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000848051311989/10000000000000000 : ℝ)) (X := (25010235112867982739/25000000000000000000 : ℝ)) (by norm_num) 4943 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1384099375844391/100000000000000000000 : ℝ) ≤ ((73602633673670617829/73610000000000000000 : ℝ)+2*(1976763703/3680500000000 : ℝ)*(197/2000 : ℝ))^(4943/1024 : ℝ) := by
    rw [show (73602633673670617829/73610000000000000000 : ℝ)+2*(1976763703/3680500000000 : ℝ)*(197/2000 : ℝ)=(10000057345830789/10000000000000000 : ℝ) by norm_num, show 1+2*(1384099375844391/100000000000000000000 : ℝ)=(50001384099375844391/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10235112867982739/50000000000000000000 : ℝ)+(1384099375844391/100000000000000000000 : ℝ) ≤ ((73602633673670617829/73610000000000000000 : ℝ)+(1976763703/3680500000000 : ℝ)*((17211/100000 : ℝ)+(197/2000 : ℝ)))^(4943/1024 : ℝ) := by
    rw [show (73602633673670617829/73610000000000000000 : ℝ)+(1976763703/3680500000000 : ℝ)*((17211/100000 : ℝ)+(197/2000 : ℝ))=(10000452698571389/10000000000000000 : ℝ) by norm_num, show 1+(10235112867982739/50000000000000000000 : ℝ)+(1384099375844391/100000000000000000000 : ℝ)=(100021854325111809869/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10235112867982739/50000000000000000000 : ℝ) ≤ ((73602633673670617829/73610000000000000000 : ℝ)+2*(1976763703/3680500000000 : ℝ)*(17211/100000 : ℝ))^(4943/1024 : ℝ) := by
    rw [show (73602633673670617829/73610000000000000000 : ℝ)+2*(1976763703/3680500000000 : ℝ)*(17211/100000 : ℝ)=(10000848051311989/10000000000000000 : ℝ) by norm_num, show 1+2*(10235112867982739/50000000000000000000 : ℝ)=(25010235112867982739/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (73602633673670617829/73610000000000000000 : ℝ)*(X 1 0+X 2 0)+(1976763703/3680500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4943/1024 : ℝ)) (lo := (197/2000 : ℝ)) (hi := (17211/100000 : ℝ)) (c := (73602633673670617829/73610000000000000000 : ℝ)) (alpha := (1976763703/3680500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (73602633673670617829/73610000000000000000 : ℝ)*(X 0 1+X 2 1)+(1976763703/3680500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4943/1024 : ℝ)) (lo := (197/2000 : ℝ)) (hi := (17211/100000 : ℝ)) (c := (73602633673670617829/73610000000000000000 : ℝ)) (alpha := (1976763703/3680500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (73602633673670617829/73610000000000000000 : ℝ)*(X 0 2+X 1 2)+(1976763703/3680500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4943/1024 : ℝ)) (lo := (197/2000 : ℝ)) (hi := (17211/100000 : ℝ)) (c := (73602633673670617829/73610000000000000000 : ℝ)) (alpha := (1976763703/3680500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-497541/3125000 : ℝ)*X 0 0+(2724312527/5000000000 : ℝ)*X 0 1+(2590800417/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133688427/250000000 : ℝ)*X 1 0+(-1729642473/10000000000 : ℝ)*X 1 1+(5181601373/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069507443/2000000000 : ℝ)*X 2 0+(5181600979/10000000000 : ℝ)*X 2 1+(-27025669/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((83499577/200000000 : ℝ)*X 0 0+(1918471087/5000000000 : ℝ)*X 0 1+(906778957/2000000000 : ℝ)*X 0 2+(83499577/200000000 : ℝ)*X 1 0+(1918471087/5000000000 : ℝ)*X 1 1+(906778957/2000000000 : ℝ)*X 1 2+(83499577/200000000 : ℝ)*X 2 0+(1918471087/5000000000 : ℝ)*X 2 1+(906778957/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-796099397/5000000000 : ℝ)*X 0 0+(41469387/80000000 : ℝ)*X 0 1+(5446530279/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638070259/5000000000 : ℝ)*X 1 0+(-146471313/1000000000 : ℝ)*X 1 1+(5446530403/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((164879399/312500000 : ℝ)*X 2 0+(5446530037/10000000000 : ℝ)*X 2 1+(-1464713297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2087578031/5000000000 : ℝ)*X 0 0+(4528486451/10000000000 : ℝ)*X 0 1+(3842408281/10000000000 : ℝ)*X 0 2+(2087578031/5000000000 : ℝ)*X 1 0+(4528486451/10000000000 : ℝ)*X 1 1+(3842408281/10000000000 : ℝ)*X 1 2+(2087578031/5000000000 : ℝ)*X 2 0+(4528486451/10000000000 : ℝ)*X 2 1+(3842408281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1657_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23549216174272910717287800753/1840250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62728119/4000000000000 : ℝ)*(base19) + (161333363/10000000000000 : ℝ)*(base23) + (393918131/100000000000000 : ℝ)*(upper3) + (13212029/50000000000000 : ℝ)*(upper4) + (20343787/20000000000000 : ℝ)*(upper5) + (1294964967743519/50000000000000 : ℝ)*(major0) + (1294964967743519/50000000000000 : ℝ)*(major1) + (1294964967743519/50000000000000 : ℝ)*(major2) + (468125726309299/12500000000000 : ℝ)*(sp0) + (1872512757204011/50000000000000 : ℝ)*(sp1) + (3745025469277367/100000000000000 : ℝ)*(sp2) + (71741188728311/5000000000000 : ℝ)*(sp3) + (10636068303/50000000000000 : ℝ)*(sp4) + (4293619287/50000000000000 : ℝ)*(sp7) + (717416180902397/50000000000000 : ℝ)*(f.failure) + (3745027082610997/100000000000000 : ℝ)*(f.sum) + (41424934283/14376953125000000000000000 : ℝ)*base65 + (31329001639865399749/3680500000000000000000000000000000 : ℝ)*base68 + (44557912682397399749/3680500000000000000000000000000000 : ℝ)*base70 + (12982993578066600251/3680500000000000000000000000000000 : ℝ)*base71 + (4476891470367/1840250000000000000000000000 : ℝ)*base74 + (40698092112219399749/3680500000000000000000000000000000 : ℝ)*base76 + (13867200344105899749/3680500000000000000000000000000000 : ℝ)*base78 + (14647583990197100251/3680500000000000000000000000000000 : ℝ)*base79 + (1512709150941/3680500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (3790427/5000000000000000000000 : ℝ)*base90 + (3790427/5000000000000000000000 : ℝ)*base92 + (3790427/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1869673365062442738623481759/230031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (306281387/25000000000000 : ℝ)*(base19) + (1531785619/100000000000000 : ℝ)*(base23) + (100017927/50000000000000 : ℝ)*(upper3) + (15474047/25000000000000 : ℝ)*(lower4) + (127696351/100000000000000 : ℝ)*(upper5) + (328869365328443/12500000000000 : ℝ)*(major0) + (328869365328443/12500000000000 : ℝ)*(major1) + (328869365328443/12500000000000 : ℝ)*(major2) + (15286934333/100000000000000 : ℝ)*(sp1) + (3191664087/20000000000000 : ℝ)*(sp2) + (951087298147411/25000000000000 : ℝ)*(sp4) + (1902166340264881/50000000000000 : ℝ)*(sp5) + (380433170248359/10000000000000 : ℝ)*(sp6) + (1457560381735091/100000000000000 : ℝ)*(sp7) + (1457560381735091/100000000000000 : ℝ)*(f.failure) + (951087298147411/25000000000000 : ℝ)*(f.sum) + (22070825281407/3680500000000000000000000000 : ℝ)*base65 + (1892954188108985247/920125000000000000000000000000000 : ℝ)*base67 + (6770041136250735247/920125000000000000000000000000000 : ℝ)*base69 + (4236001473236860247/920125000000000000000000000000000 : ℝ)*base71 + (2282334608243/460062500000000000000000000 : ℝ)*base73 + (1943835881443360247/920125000000000000000000000000000 : ℝ)*base75 + (5274066909695735247/920125000000000000000000000000000 : ℝ)*base77 + (2452584737565389753/920125000000000000000000000000000 : ℝ)*base80 + (26235539045739/7361000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (98520181/10000000000000000000000 : ℝ)*base90 + (98520181/10000000000000000000000 : ℝ)*base92 + (98520181/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1657_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180504009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17211/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (197/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2661/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16323/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1657_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1657_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180504009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2661/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16323/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1657_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1657_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1657_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4943/1024 : ℝ) ≤ p) (hpb : p ≤ (4947/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180504009/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2661/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16323/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1657_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
