-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1573_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:28:28.506298+00:00
-- url     : https://prove2.me/submissions/04442d32-9af1-458e-866e-1e703d2347c8

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
theorem support_rectangle_w1573_s0_0 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-405750991/2500000000 : ℝ)*x 0 + (2933690519/5000000000 : ℝ)*x 1 + (2440276583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (405750991/2500000000 : ℝ)^4643 ≤ (4851194064889/50000000000000 : ℝ)^3619 := by
    have hnat : (405750991 : ℕ)^4643*50000000000000^3619 ≤ 4851194064889^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405750991 2500000000 4851194064889 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2933690519/5000000000 : ℝ)^4643 ≤ (12614364080609/25000000000000 : ℝ)^3619 := by
    have hnat : (2933690519 : ℕ)^4643*25000000000000^3619 ≤ 12614364080609^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2933690519 5000000000 12614364080609 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2440276583/5000000000 : ℝ)^4643 ≤ (19920077767421/50000000000000 : ℝ)^3619 := by
    have hnat : (2440276583 : ℕ)^4643*50000000000000^3619 ≤ 19920077767421^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2440276583 5000000000 19920077767421 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-405750991/2500000000 : ℝ), (2933690519/5000000000 : ℝ), (2440276583/5000000000 : ℝ)] ![(4851194064889/50000000000000 : ℝ), (12614364080609/25000000000000 : ℝ), (19920077767421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-405750991/2500000000 : ℝ)|^4643 ≤ (4851194064889/50000000000000 : ℝ)^3619
        have hw : |(-405750991/2500000000 : ℝ)|=(405750991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2933690519/5000000000 : ℝ)|^4643 ≤ (12614364080609/25000000000000 : ℝ)^3619
        have hw : |(2933690519/5000000000 : ℝ)|=(2933690519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2440276583/5000000000 : ℝ)|^4643 ≤ (19920077767421/50000000000000 : ℝ)^3619
        have hw : |(2440276583/5000000000 : ℝ)|=(2440276583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s0_1 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1092967767/2000000000 : ℝ)*x 0 + (-1085977797/5000000000 : ℝ)*x 1 + (1220138291/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092967767/2000000000 : ℝ)^4643 ≤ (23030034582053/50000000000000 : ℝ)^3619 := by
    have hnat : (1092967767 : ℕ)^4643*50000000000000^3619 ≤ 23030034582053^3619*2000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092967767 2000000000 23030034582053 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085977797/5000000000 : ℝ)^4643 ≤ (14099775311353/100000000000000 : ℝ)^3619 := by
    have hnat : (1085977797 : ℕ)^4643*100000000000000^3619 ≤ 14099775311353^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085977797 5000000000 14099775311353 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1220138291/2500000000 : ℝ)^4643 ≤ (39840155513897/100000000000000 : ℝ)^3619 := by
    have hnat : (1220138291 : ℕ)^4643*100000000000000^3619 ≤ 39840155513897^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1220138291 2500000000 39840155513897 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092967767/2000000000 : ℝ), (-1085977797/5000000000 : ℝ), (1220138291/2500000000 : ℝ)] ![(23030034582053/50000000000000 : ℝ), (14099775311353/100000000000000 : ℝ), (39840155513897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092967767/2000000000 : ℝ)|^4643 ≤ (23030034582053/50000000000000 : ℝ)^3619
        have hw : |(1092967767/2000000000 : ℝ)|=(1092967767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1085977797/5000000000 : ℝ)|^4643 ≤ (14099775311353/100000000000000 : ℝ)^3619
        have hw : |(-1085977797/5000000000 : ℝ)|=(1085977797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1220138291/2500000000 : ℝ)|^4643 ≤ (39840155513897/100000000000000 : ℝ)^3619
        have hw : |(1220138291/2500000000 : ℝ)|=(1220138291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s0_2 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2732419447/5000000000 : ℝ)*x 0 + (4880553091/10000000000 : ℝ)*x 1 + (-271494451/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2732419447/5000000000 : ℝ)^4643 ≤ (46060069802089/100000000000000 : ℝ)^3619 := by
    have hnat : (2732419447 : ℕ)^4643*100000000000000^3619 ≤ 46060069802089^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732419447 5000000000 46060069802089 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4880553091/10000000000 : ℝ)^4643 ≤ (4980019343673/12500000000000 : ℝ)^3619 := by
    have hnat : (4880553091 : ℕ)^4643*12500000000000^3619 ≤ 4980019343673^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4880553091 10000000000 4980019343673 12500000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271494451/1250000000 : ℝ)^4643 ≤ (14099775427953/100000000000000 : ℝ)^3619 := by
    have hnat : (271494451 : ℕ)^4643*100000000000000^3619 ≤ 14099775427953^3619*1250000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271494451 1250000000 14099775427953 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2732419447/5000000000 : ℝ), (4880553091/10000000000 : ℝ), (-271494451/1250000000 : ℝ)] ![(46060069802089/100000000000000 : ℝ), (4980019343673/12500000000000 : ℝ), (14099775427953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2732419447/5000000000 : ℝ)|^4643 ≤ (46060069802089/100000000000000 : ℝ)^3619
        have hw : |(2732419447/5000000000 : ℝ)|=(2732419447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4880553091/10000000000 : ℝ)|^4643 ≤ (4980019343673/12500000000000 : ℝ)^3619
        have hw : |(4880553091/10000000000 : ℝ)|=(4880553091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-271494451/1250000000 : ℝ)|^4643 ≤ (14099775427953/100000000000000 : ℝ)^3619
        have hw : |(-271494451/1250000000 : ℝ)|=(271494451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s0_3 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4129077481/10000000000 : ℝ)*x 0 + (193333171/625000000 : ℝ)*x 1 + (2713780309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4129077481/10000000000 : ℝ)^4643 ≤ (16074158001659/50000000000000 : ℝ)^3619 := by
    have hnat : (4129077481 : ℕ)^4643*50000000000000^3619 ≤ 16074158001659^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129077481 10000000000 16074158001659 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (193333171/625000000 : ℝ)^4643 ≤ (4438864969783/20000000000000 : ℝ)^3619 := by
    have hnat : (193333171 : ℕ)^4643*20000000000000^3619 ≤ 4438864969783^3619*625000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193333171 625000000 4438864969783 20000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713780309/5000000000 : ℝ)^4643 ≤ (5707169891749/12500000000000 : ℝ)^3619 := by
    have hnat : (2713780309 : ℕ)^4643*12500000000000^3619 ≤ 5707169891749^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713780309 5000000000 5707169891749 12500000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4129077481/10000000000 : ℝ), (193333171/625000000 : ℝ), (2713780309/5000000000 : ℝ)] ![(16074158001659/50000000000000 : ℝ), (4438864969783/20000000000000 : ℝ), (5707169891749/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4129077481/10000000000 : ℝ)|^4643 ≤ (16074158001659/50000000000000 : ℝ)^3619
        have hw : |(4129077481/10000000000 : ℝ)|=(4129077481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(193333171/625000000 : ℝ)|^4643 ≤ (4438864969783/20000000000000 : ℝ)^3619
        have hw : |(193333171/625000000 : ℝ)|=(193333171/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713780309/5000000000 : ℝ)|^4643 ≤ (5707169891749/12500000000000 : ℝ)^3619
        have hw : |(2713780309/5000000000 : ℝ)|=(2713780309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s0_4 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-813018029/5000000000 : ℝ)*x 0 + (2452702893/5000000000 : ℝ)*x 1 + (5841648943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (813018029/5000000000 : ℝ)^4643 ≤ (2431412257851/25000000000000 : ℝ)^3619 := by
    have hnat : (813018029 : ℕ)^4643*25000000000000^3619 ≤ 2431412257851^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      813018029 5000000000 2431412257851 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2452702893/5000000000 : ℝ)^4643 ≤ (40100618894621/100000000000000 : ℝ)^3619 := by
    have hnat : (2452702893 : ℕ)^4643*100000000000000^3619 ≤ 40100618894621^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2452702893 5000000000 40100618894621 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5841648943/10000000000 : ℝ)^4643 ≤ (10034746411643/20000000000000 : ℝ)^3619 := by
    have hnat : (5841648943 : ℕ)^4643*20000000000000^3619 ≤ 10034746411643^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5841648943 10000000000 10034746411643 20000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-813018029/5000000000 : ℝ), (2452702893/5000000000 : ℝ), (5841648943/10000000000 : ℝ)] ![(2431412257851/25000000000000 : ℝ), (40100618894621/100000000000000 : ℝ), (10034746411643/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-813018029/5000000000 : ℝ)|^4643 ≤ (2431412257851/25000000000000 : ℝ)^3619
        have hw : |(-813018029/5000000000 : ℝ)|=(813018029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2452702893/5000000000 : ℝ)|^4643 ≤ (40100618894621/100000000000000 : ℝ)^3619
        have hw : |(2452702893/5000000000 : ℝ)|=(2452702893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5841648943/10000000000 : ℝ)|^4643 ≤ (10034746411643/20000000000000 : ℝ)^3619
        have hw : |(5841648943/10000000000 : ℝ)|=(5841648943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s0_5 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1298765261/2500000000 : ℝ)*x 0 + (-605430109/5000000000 : ℝ)*x 1 + (116832973/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1298765261/2500000000 : ℝ)^4643 ≤ (43163506697781/100000000000000 : ℝ)^3619 := by
    have hnat : (1298765261 : ℕ)^4643*100000000000000^3619 ≤ 43163506697781^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298765261 2500000000 43163506697781 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (605430109/5000000000 : ℝ)^4643 ≤ (6662764461817/100000000000000 : ℝ)^3619 := by
    have hnat : (605430109 : ℕ)^4643*100000000000000^3619 ≤ 6662764461817^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605430109 5000000000 6662764461817 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (116832973/200000000 : ℝ)^4643 ≤ (25086864414791/50000000000000 : ℝ)^3619 := by
    have hnat : (116832973 : ℕ)^4643*50000000000000^3619 ≤ 25086864414791^3619*200000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116832973 200000000 25086864414791 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1298765261/2500000000 : ℝ), (-605430109/5000000000 : ℝ), (116832973/200000000 : ℝ)] ![(43163506697781/100000000000000 : ℝ), (6662764461817/100000000000000 : ℝ), (25086864414791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1298765261/2500000000 : ℝ)|^4643 ≤ (43163506697781/100000000000000 : ℝ)^3619
        have hw : |(1298765261/2500000000 : ℝ)|=(1298765261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-605430109/5000000000 : ℝ)|^4643 ≤ (6662764461817/100000000000000 : ℝ)^3619
        have hw : |(-605430109/5000000000 : ℝ)|=(605430109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(116832973/200000000 : ℝ)|^4643 ≤ (25086864414791/50000000000000 : ℝ)^3619
        have hw : |(116832973/200000000 : ℝ)|=(116832973/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s0_6 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5195060649/10000000000 : ℝ)*x 0 + (584164927/1000000000 : ℝ)*x 1 + (-605429923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195060649/10000000000 : ℝ)^4643 ≤ (8632700497457/20000000000000 : ℝ)^3619 := by
    have hnat : (5195060649 : ℕ)^4643*20000000000000^3619 ≤ 8632700497457^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195060649 10000000000 8632700497457 20000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (584164927/1000000000 : ℝ)^4643 ≤ (50173735661501/100000000000000 : ℝ)^3619 := by
    have hnat : (584164927 : ℕ)^4643*100000000000000^3619 ≤ 50173735661501^3619*1000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      584164927 1000000000 50173735661501 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (605429923/5000000000 : ℝ)^4643 ≤ (832845229463/12500000000000 : ℝ)^3619 := by
    have hnat : (605429923 : ℕ)^4643*12500000000000^3619 ≤ 832845229463^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605429923 5000000000 832845229463 12500000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195060649/10000000000 : ℝ), (584164927/1000000000 : ℝ), (-605429923/5000000000 : ℝ)] ![(8632700497457/20000000000000 : ℝ), (50173735661501/100000000000000 : ℝ), (832845229463/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195060649/10000000000 : ℝ)|^4643 ≤ (8632700497457/20000000000000 : ℝ)^3619
        have hw : |(5195060649/10000000000 : ℝ)|=(5195060649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(584164927/1000000000 : ℝ)|^4643 ≤ (50173735661501/100000000000000 : ℝ)^3619
        have hw : |(584164927/1000000000 : ℝ)|=(584164927/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-605429923/5000000000 : ℝ)|^4643 ≤ (832845229463/12500000000000 : ℝ)^3619
        have hw : |(-605429923/5000000000 : ℝ)|=(605429923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s0_7 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (827249653/2000000000 : ℝ)*x 0 + (5368773427/10000000000 : ℝ)*x 1 + (3154197349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (827249653/2000000000 : ℝ)^4643 ≤ (4027495181027/12500000000000 : ℝ)^3619 := by
    have hnat : (827249653 : ℕ)^4643*12500000000000^3619 ≤ 4027495181027^3619*2000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827249653 2000000000 4027495181027 12500000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5368773427/10000000000 : ℝ)^4643 ≤ (4502388165823/10000000000000 : ℝ)^3619 := by
    have hnat : (5368773427 : ℕ)^4643*10000000000000^3619 ≤ 4502388165823^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368773427 10000000000 4502388165823 10000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154197349/10000000000 : ℝ)^4643 ≤ (5689039219317/25000000000000 : ℝ)^3619 := by
    have hnat : (3154197349 : ℕ)^4643*25000000000000^3619 ≤ 5689039219317^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154197349 10000000000 5689039219317 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(827249653/2000000000 : ℝ), (5368773427/10000000000 : ℝ), (3154197349/10000000000 : ℝ)] ![(4027495181027/12500000000000 : ℝ), (4502388165823/10000000000000 : ℝ), (5689039219317/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(827249653/2000000000 : ℝ)|^4643 ≤ (4027495181027/12500000000000 : ℝ)^3619
        have hw : |(827249653/2000000000 : ℝ)|=(827249653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5368773427/10000000000 : ℝ)|^4643 ≤ (4502388165823/10000000000000 : ℝ)^3619
        have hw : |(5368773427/10000000000 : ℝ)|=(5368773427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154197349/10000000000 : ℝ)|^4643 ≤ (5689039219317/25000000000000 : ℝ)^3619
        have hw : |(3154197349/10000000000 : ℝ)|=(3154197349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1573_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21033669/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (179/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (12359/50000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4641/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4641 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4641*1^1024 ≤ 0^1024*1^4641 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4641 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4641/1024 : ℝ) ≤ (39299382916577429/2500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4641 ≤ (39299382916577429/2500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4641*2500000000000000000^1024 ≤ 39299382916577429^1024*5^4641 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 39299382916577429 2500000000000000000 4641 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (39299382916577429/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4641/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4641 := by
      have hnat : (1 : ℕ)^1024*1^4641 ≤ 1^4641*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4641 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2539299382916577429/2500000000000000000 : ℝ) ≤ (10034473888847043/10000000000000000 : ℝ) ^ (4641/1024 : ℝ) := by
    have hpowers : (2539299382916577429/2500000000000000000 : ℝ)^1024 ≤ (10034473888847043/10000000000000000 : ℝ)^4641 := by
      have hnat : (2539299382916577429 : ℕ)^1024*10000000000000000^4641 ≤ 10034473888847043^4641*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2539299382916577429 2500000000000000000 10034473888847043 10000000000000000 1024 4641 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10034473888847043/10000000000000000 : ℝ)) (X := (2539299382916577429/2500000000000000000 : ℝ)) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1289299382916577429/1250000000000000000 : ℝ) ≤ (5034473888847043/5000000000000000 : ℝ) ^ (4641/1024 : ℝ) := by
    have hpowers : (1289299382916577429/1250000000000000000 : ℝ)^1024 ≤ (5034473888847043/5000000000000000 : ℝ)^4641 := by
      have hnat : (1289299382916577429 : ℕ)^1024*5000000000000000^4641 ≤ 5034473888847043^4641*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1289299382916577429 1250000000000000000 5034473888847043 5000000000000000 1024 4641 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5034473888847043/5000000000000000 : ℝ)) (X := (1289299382916577429/1250000000000000000 : ℝ)) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(34473888847043/4000000000000000 : ℝ)*(0 : ℝ))^(4641/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(34473888847043/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39299382916577429/2500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(34473888847043/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4641/1024 : ℝ) := by
    rw [show (1 : ℝ)+(34473888847043/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10034473888847043/10000000000000000 : ℝ) by norm_num, show 1+(39299382916577429/2500000000000000000 : ℝ)+(0 : ℝ)=(2539299382916577429/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39299382916577429/2500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(34473888847043/4000000000000000 : ℝ)*(2/5 : ℝ))^(4641/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(34473888847043/4000000000000000 : ℝ)*(2/5 : ℝ)=(5034473888847043/5000000000000000 : ℝ) by norm_num, show 1+2*(39299382916577429/2500000000000000000 : ℝ)=(1289299382916577429/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(34473888847043/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4641/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (34473888847043/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(34473888847043/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4641/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (34473888847043/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(34473888847043/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4641/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (34473888847043/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-405750991/2500000000 : ℝ)*X 0 0+(2933690519/5000000000 : ℝ)*X 0 1+(2440276583/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1092967767/2000000000 : ℝ)*X 1 0+(-1085977797/5000000000 : ℝ)*X 1 1+(1220138291/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2732419447/5000000000 : ℝ)*X 2 0+(4880553091/10000000000 : ℝ)*X 2 1+(-271494451/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4129077481/10000000000 : ℝ)*X 0 0+(193333171/625000000 : ℝ)*X 0 1+(2713780309/5000000000 : ℝ)*X 0 2+(4129077481/10000000000 : ℝ)*X 1 0+(193333171/625000000 : ℝ)*X 1 1+(2713780309/5000000000 : ℝ)*X 1 2+(4129077481/10000000000 : ℝ)*X 2 0+(193333171/625000000 : ℝ)*X 2 1+(2713780309/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-813018029/5000000000 : ℝ)*X 0 0+(2452702893/5000000000 : ℝ)*X 0 1+(5841648943/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1298765261/2500000000 : ℝ)*X 1 0+(-605430109/5000000000 : ℝ)*X 1 1+(116832973/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5195060649/10000000000 : ℝ)*X 2 0+(584164927/1000000000 : ℝ)*X 2 1+(-605429923/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((827249653/2000000000 : ℝ)*X 0 0+(5368773427/10000000000 : ℝ)*X 0 1+(3154197349/10000000000 : ℝ)*X 0 2+(827249653/2000000000 : ℝ)*X 1 0+(5368773427/10000000000 : ℝ)*X 1 1+(3154197349/10000000000 : ℝ)*X 1 2+(827249653/2000000000 : ℝ)*X 2 0+(5368773427/10000000000 : ℝ)*X 2 1+(3154197349/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (903722619039893690496621/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41900449/100000000000000 : ℝ)*(base1) + (908455313/100000000000000 : ℝ)*(base19) + (14365559/1562500000000 : ℝ)*(base23) + (117828393/100000000000000 : ℝ)*(upper3) + (23285997/20000000000000 : ℝ)*(upper5) + (720882171720251/100000000000000 : ℝ)*(major0) + (720882171720251/100000000000000 : ℝ)*(major1) + (720882171720251/100000000000000 : ℝ)*(major2) + (506675584425157/50000000000000 : ℝ)*(sp0) + (506676808339473/50000000000000 : ℝ)*(sp1) + (253338401434621/25000000000000 : ℝ)*(sp2) + (428408180614027/100000000000000 : ℝ)*(sp3) + (679636879/20000000000000 : ℝ)*(sp4) + (57806853/4000000000000 : ℝ)*(sp7) + (428409667685801/100000000000000 : ℝ)*(f.failure) + (50667726256713/5000000000000 : ℝ)*(f.sum) + (27712823367793/200000000000000000000000000000 : ℝ)*base65 + (519258304967793/400000000000000000000000000000 : ℝ)*base67 + (532468436567793/400000000000000000000000000000 : ℝ)*base69 + (1647648315767793/400000000000000000000000000000 : ℝ)*base71 + (647811820032207/200000000000000000000000000000 : ℝ)*base74 + (3200929822567793/400000000000000000000000000000 : ℝ)*base75 + (1196396801367793/400000000000000000000000000000 : ℝ)*base77 + (149541151832207/400000000000000000000000000000 : ℝ)*base80 + (75151243232207/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3266131/1250000000000000000000 : ℝ)*base90 + (3266131/1250000000000000000000 : ℝ)*base92 + (3266131/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (743105048557265384892267/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1617736521/100000000000000 : ℝ)*(base19) + (1643251111/100000000000000 : ℝ)*(base23) + (53807161/50000000000000 : ℝ)*(base39) + (25274537/12500000000000 : ℝ)*(upper3) + (298242131/100000000000000 : ℝ)*(upper5) + (189956486292971/25000000000000 : ℝ)*(major0) + (189956486292971/25000000000000 : ℝ)*(major1) + (379912918778781/50000000000000 : ℝ)*(major2) + (228499727/5000000000000 : ℝ)*(sp1) + (4587259397/100000000000000 : ℝ)*(sp2) + (534049077896663/50000000000000 : ℝ)*(sp4) + (213618393612453/20000000000000 : ℝ)*(sp5) + (53404601644857/5000000000000 : ℝ)*(sp6) + (225776689617217/50000000000000 : ℝ)*(sp7) + (225776689617217/50000000000000 : ℝ)*(f.failure) + (33378070731489/3125000000000 : ℝ)*(f.sum) + (167449347335911/200000000000000000000000000000 : ℝ)*base66 + (557202247805417/200000000000000000000000000000 : ℝ)*base68 + (423206683365247/100000000000000000000000000000 : ℝ)*base70 + (160292851005417/200000000000000000000000000000 : ℝ)*base72 + (45421315464089/200000000000000000000000000000 : ℝ)*base73 + (719062922565247/100000000000000000000000000000 : ℝ)*base76 + (243738473765247/100000000000000000000000000000 : ℝ)*base78 + (468121619465247/100000000000000000000000000000 : ℝ)*base80 + (87798972534753/50000000000000000000000000000 : ℝ)*base81 + (4079173/625000000000000000000 : ℝ)*base89 + (4079173/625000000000000000000 : ℝ)*base91 + (4079173/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1573_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21033669/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (179/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (12359/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1573_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1573_s1_0 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1760851939/10000000000 : ℝ)*x 0 + (172910599/312500000 : ℝ)*x 1 + (1025186151/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1760851939/10000000000 : ℝ)^4643 ≤ (10772073156951/100000000000000 : ℝ)^3619 := by
    have hnat : (1760851939 : ℕ)^4643*100000000000000^3619 ≤ 10772073156951^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1760851939 10000000000 10772073156951 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (172910599/312500000 : ℝ)^4643 ≤ (23399960797003/50000000000000 : ℝ)^3619 := by
    have hnat : (172910599 : ℕ)^4643*50000000000000^3619 ≤ 23399960797003^3619*312500000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172910599 312500000 23399960797003 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025186151/2000000000 : ℝ)^4643 ≤ (42428005231683/100000000000000 : ℝ)^3619 := by
    have hnat : (1025186151 : ℕ)^4643*100000000000000^3619 ≤ 42428005231683^3619*2000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025186151 2000000000 42428005231683 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1760851939/10000000000 : ℝ), (172910599/312500000 : ℝ), (1025186151/2000000000 : ℝ)] ![(10772073156951/100000000000000 : ℝ), (23399960797003/50000000000000 : ℝ), (42428005231683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1760851939/10000000000 : ℝ)|^4643 ≤ (10772073156951/100000000000000 : ℝ)^3619
        have hw : |(-1760851939/10000000000 : ℝ)|=(1760851939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(172910599/312500000 : ℝ)|^4643 ≤ (23399960797003/50000000000000 : ℝ)^3619
        have hw : |(172910599/312500000 : ℝ)|=(172910599/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1025186151/2000000000 : ℝ)|^4643 ≤ (42428005231683/100000000000000 : ℝ)^3619
        have hw : |(1025186151/2000000000 : ℝ)|=(1025186151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s1_1 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5375933191/10000000000 : ℝ)*x 0 + (-986891629/5000000000 : ℝ)*x 1 + (1025186091/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375933191/10000000000 : ℝ)^4643 ≤ (9020185832331/20000000000000 : ℝ)^3619 := by
    have hnat : (5375933191 : ℕ)^4643*20000000000000^3619 ≤ 9020185832331^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375933191 10000000000 9020185832331 20000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (986891629/5000000000 : ℝ)^4643 ≤ (12471068772857/100000000000000 : ℝ)^3619 := by
    have hnat : (986891629 : ℕ)^4643*100000000000000^3619 ≤ 12471068772857^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986891629 5000000000 12471068772857 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025186091/2000000000 : ℝ)^4643 ≤ (42428002045937/100000000000000 : ℝ)^3619 := by
    have hnat : (1025186091 : ℕ)^4643*100000000000000^3619 ≤ 42428002045937^3619*2000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025186091 2000000000 42428002045937 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375933191/10000000000 : ℝ), (-986891629/5000000000 : ℝ), (1025186091/2000000000 : ℝ)] ![(9020185832331/20000000000000 : ℝ), (12471068772857/100000000000000 : ℝ), (42428002045937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375933191/10000000000 : ℝ)|^4643 ≤ (9020185832331/20000000000000 : ℝ)^3619
        have hw : |(5375933191/10000000000 : ℝ)|=(5375933191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-986891629/5000000000 : ℝ)|^4643 ≤ (12471068772857/100000000000000 : ℝ)^3619
        have hw : |(-986891629/5000000000 : ℝ)|=(986891629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1025186091/2000000000 : ℝ)|^4643 ≤ (42428002045937/100000000000000 : ℝ)^3619
        have hw : |(1025186091/2000000000 : ℝ)|=(1025186091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s1_2 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134398327/250000000 : ℝ)*x 0 + (2562965343/5000000000 : ℝ)*x 1 + (-986891551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134398327/250000000 : ℝ)^4643 ≤ (45100927966939/100000000000000 : ℝ)^3619 := by
    have hnat : (134398327 : ℕ)^4643*100000000000000^3619 ≤ 45100927966939^3619*250000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134398327 250000000 45100927966939 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2562965343/5000000000 : ℝ)^4643 ≤ (21214002249481/50000000000000 : ℝ)^3619 := by
    have hnat : (2562965343 : ℕ)^4643*50000000000000^3619 ≤ 21214002249481^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2562965343 5000000000 21214002249481 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (986891551/5000000000 : ℝ)^4643 ≤ (6235533754149/50000000000000 : ℝ)^3619 := by
    have hnat : (986891551 : ℕ)^4643*50000000000000^3619 ≤ 6235533754149^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986891551 5000000000 6235533754149 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134398327/250000000 : ℝ), (2562965343/5000000000 : ℝ), (-986891551/5000000000 : ℝ)] ![(45100927966939/100000000000000 : ℝ), (21214002249481/50000000000000 : ℝ), (6235533754149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134398327/250000000 : ℝ)|^4643 ≤ (45100927966939/100000000000000 : ℝ)^3619
        have hw : |(134398327/250000000 : ℝ)|=(134398327/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2562965343/5000000000 : ℝ)|^4643 ≤ (21214002249481/50000000000000 : ℝ)^3619
        have hw : |(2562965343/5000000000 : ℝ)|=(2562965343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-986891551/5000000000 : ℝ)|^4643 ≤ (6235533754149/50000000000000 : ℝ)^3619
        have hw : |(-986891551/5000000000 : ℝ)|=(986891551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s1_3 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528420967/1250000000 : ℝ)*x 0 + (3767827227/10000000000 : ℝ)*x 1 + (2365517039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528420967/1250000000 : ℝ)^4643 ≤ (16566705011901/50000000000000 : ℝ)^3619 := by
    have hnat : (528420967 : ℕ)^4643*50000000000000^3619 ≤ 16566705011901^3619*1250000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528420967 1250000000 16566705011901 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3767827227/10000000000 : ℝ)^4643 ≤ (5717095618891/20000000000000 : ℝ)^3619 := by
    have hnat : (3767827227 : ℕ)^4643*20000000000000^3619 ≤ 5717095618891^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3767827227 10000000000 5717095618891 20000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2365517039/5000000000 : ℝ)^4643 ≤ (38281111871863/100000000000000 : ℝ)^3619 := by
    have hnat : (2365517039 : ℕ)^4643*100000000000000^3619 ≤ 38281111871863^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2365517039 5000000000 38281111871863 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528420967/1250000000 : ℝ), (3767827227/10000000000 : ℝ), (2365517039/5000000000 : ℝ)] ![(16566705011901/50000000000000 : ℝ), (5717095618891/20000000000000 : ℝ), (38281111871863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528420967/1250000000 : ℝ)|^4643 ≤ (16566705011901/50000000000000 : ℝ)^3619
        have hw : |(528420967/1250000000 : ℝ)|=(528420967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3767827227/10000000000 : ℝ)|^4643 ≤ (5717095618891/20000000000000 : ℝ)^3619
        have hw : |(3767827227/10000000000 : ℝ)|=(3767827227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2365517039/5000000000 : ℝ)|^4643 ≤ (38281111871863/100000000000000 : ℝ)^3619
        have hw : |(2365517039/5000000000 : ℝ)|=(2365517039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s1_4 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-880529697/5000000000 : ℝ)*x 0 + (2565057313/5000000000 : ℝ)*x 1 + (5528893839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (880529697/5000000000 : ℝ)^4643 ≤ (10773701394253/100000000000000 : ℝ)^3619 := by
    have hnat : (880529697 : ℕ)^4643*100000000000000^3619 ≤ 10773701394253^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880529697 5000000000 10773701394253 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2565057313/5000000000 : ℝ)^4643 ≤ (42472439537749/100000000000000 : ℝ)^3619 := by
    have hnat : (2565057313 : ℕ)^4643*100000000000000^3619 ≤ 42472439537749^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2565057313 5000000000 42472439537749 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5528893839/10000000000 : ℝ)^4643 ≤ (23376929529679/50000000000000 : ℝ)^3619 := by
    have hnat : (5528893839 : ℕ)^4643*50000000000000^3619 ≤ 23376929529679^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5528893839 10000000000 23376929529679 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-880529697/5000000000 : ℝ), (2565057313/5000000000 : ℝ), (5528893839/10000000000 : ℝ)] ![(10773701394253/100000000000000 : ℝ), (42472439537749/100000000000000 : ℝ), (23376929529679/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-880529697/5000000000 : ℝ)|^4643 ≤ (10773701394253/100000000000000 : ℝ)^3619
        have hw : |(-880529697/5000000000 : ℝ)|=(880529697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2565057313/5000000000 : ℝ)|^4643 ≤ (42472439537749/100000000000000 : ℝ)^3619
        have hw : |(2565057313/5000000000 : ℝ)|=(2565057313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5528893839/10000000000 : ℝ)|^4643 ≤ (23376929529679/50000000000000 : ℝ)^3619
        have hw : |(5528893839/10000000000 : ℝ)|=(5528893839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s1_5 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5267962897/10000000000 : ℝ)*x 0 + (-1570819861/10000000000 : ℝ)*x 1 + (1382223587/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5267962897/10000000000 : ℝ)^4643 ≤ (21971070220523/50000000000000 : ℝ)^3619 := by
    have hnat : (5267962897 : ℕ)^4643*50000000000000^3619 ≤ 21971070220523^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267962897 10000000000 21971070220523 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1570819861/10000000000 : ℝ)^4643 ≤ (930399496313/10000000000000 : ℝ)^3619 := by
    have hnat : (1570819861 : ℕ)^4643*10000000000000^3619 ≤ 930399496313^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1570819861 10000000000 930399496313 10000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1382223587/2500000000 : ℝ)^4643 ≤ (23376932290747/50000000000000 : ℝ)^3619 := by
    have hnat : (1382223587 : ℕ)^4643*50000000000000^3619 ≤ 23376932290747^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1382223587 2500000000 23376932290747 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5267962897/10000000000 : ℝ), (-1570819861/10000000000 : ℝ), (1382223587/2500000000 : ℝ)] ![(21971070220523/50000000000000 : ℝ), (930399496313/10000000000000 : ℝ), (23376932290747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5267962897/10000000000 : ℝ)|^4643 ≤ (21971070220523/50000000000000 : ℝ)^3619
        have hw : |(5267962897/10000000000 : ℝ)|=(5267962897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1570819861/10000000000 : ℝ)|^4643 ≤ (930399496313/10000000000000 : ℝ)^3619
        have hw : |(-1570819861/10000000000 : ℝ)|=(1570819861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1382223587/2500000000 : ℝ)|^4643 ≤ (23376932290747/50000000000000 : ℝ)^3619
        have hw : |(1382223587/2500000000 : ℝ)|=(1382223587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s1_6 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5267962309/10000000000 : ℝ)*x 0 + (691111821/1250000000 : ℝ)*x 1 + (-12566563/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5267962309/10000000000 : ℝ)^4643 ≤ (43942134148507/100000000000000 : ℝ)^3619 := by
    have hnat : (5267962309 : ℕ)^4643*100000000000000^3619 ≤ 43942134148507^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267962309 10000000000 43942134148507 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (691111821/1250000000 : ℝ)^4643 ≤ (2922116685517/6250000000000 : ℝ)^3619 := by
    have hnat : (691111821 : ℕ)^4643*6250000000000^3619 ≤ 2922116685517^3619*1250000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691111821 1250000000 2922116685517 6250000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12566563/80000000 : ℝ)^4643 ≤ (9303998868987/100000000000000 : ℝ)^3619 := by
    have hnat : (12566563 : ℕ)^4643*100000000000000^3619 ≤ 9303998868987^3619*80000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12566563 80000000 9303998868987 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5267962309/10000000000 : ℝ), (691111821/1250000000 : ℝ), (-12566563/80000000 : ℝ)] ![(43942134148507/100000000000000 : ℝ), (2922116685517/6250000000000 : ℝ), (9303998868987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5267962309/10000000000 : ℝ)|^4643 ≤ (43942134148507/100000000000000 : ℝ)^3619
        have hw : |(5267962309/10000000000 : ℝ)|=(5267962309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(691111821/1250000000 : ℝ)|^4643 ≤ (2922116685517/6250000000000 : ℝ)^3619
        have hw : |(691111821/1250000000 : ℝ)|=(691111821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12566563/80000000 : ℝ)|^4643 ≤ (9303998868987/100000000000000 : ℝ)^3619
        have hw : |(-12566563/80000000 : ℝ)|=(12566563/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s1_7 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2113928719/5000000000 : ℝ)*x 0 + (4721137949/10000000000 : ℝ)*x 1 + (188893447/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2113928719/5000000000 : ℝ)^4643 ≤ (8284583582931/25000000000000 : ℝ)^3619 := by
    have hnat : (2113928719 : ℕ)^4643*25000000000000^3619 ≤ 8284583582931^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113928719 5000000000 8284583582931 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4721137949/10000000000 : ℝ)^4643 ≤ (9544602680219/25000000000000 : ℝ)^3619 := by
    have hnat : (4721137949 : ℕ)^4643*25000000000000^3619 ≤ 9544602680219^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4721137949 10000000000 9544602680219 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188893447/500000000 : ℝ)^4643 ≤ (14341627467617/50000000000000 : ℝ)^3619 := by
    have hnat : (188893447 : ℕ)^4643*50000000000000^3619 ≤ 14341627467617^3619*500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188893447 500000000 14341627467617 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2113928719/5000000000 : ℝ), (4721137949/10000000000 : ℝ), (188893447/500000000 : ℝ)] ![(8284583582931/25000000000000 : ℝ), (9544602680219/25000000000000 : ℝ), (14341627467617/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2113928719/5000000000 : ℝ)|^4643 ≤ (8284583582931/25000000000000 : ℝ)^3619
        have hw : |(2113928719/5000000000 : ℝ)|=(2113928719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4721137949/10000000000 : ℝ)|^4643 ≤ (9544602680219/25000000000000 : ℝ)^3619
        have hw : |(4721137949/10000000000 : ℝ)|=(4721137949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(188893447/500000000 : ℝ)|^4643 ≤ (14341627467617/50000000000000 : ℝ)^3619
        have hw : |(188893447/500000000 : ℝ)|=(188893447/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1573_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21033669/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12359/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (179/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (9103/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (554/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (12359/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (179/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (12359/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (179/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (12359/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (179/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (12359/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (179/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (12359/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (179/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (12359/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (179/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (179/5000 : ℝ) ^ (4641/1024 : ℝ) ≤ (27917096056259/100000000000000000000 : ℝ) := by
    have hpowers : (179/5000 : ℝ)^4641 ≤ (27917096056259/100000000000000000000 : ℝ)^1024 := by
      have hnat : (179 : ℕ)^4641*100000000000000000000^1024 ≤ 27917096056259^1024*5000^4641 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        179 5000 27917096056259 100000000000000000000 4641 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (179/5000 : ℝ)) (X := (27917096056259/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (12359/50000 : ℝ) ^ (4641/1024 : ℝ) ≤ (177418491210915399/100000000000000000000 : ℝ) := by
    have hpowers : (12359/50000 : ℝ)^4641 ≤ (177418491210915399/100000000000000000000 : ℝ)^1024 := by
      have hnat : (12359 : ℕ)^4641*100000000000000000000^1024 ≤ 177418491210915399^1024*50000^4641 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12359 50000 177418491210915399 100000000000000000000 4641 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12359/50000 : ℝ)) (X := (177418491210915399/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000027917096056259/50000000000000000000 : ℝ) ≤ (10000001231937089/10000000000000000 : ℝ) ^ (4641/1024 : ℝ) := by
    have hpowers : (50000027917096056259/50000000000000000000 : ℝ)^1024 ≤ (10000001231937089/10000000000000000 : ℝ)^4641 := by
      have hnat : (50000027917096056259 : ℕ)^1024*10000000000000000^4641 ≤ 10000001231937089^4641*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000027917096056259 50000000000000000000 10000001231937089 10000000000000000 1024 4641 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001231937089/10000000000000000 : ℝ)) (X := (50000027917096056259/50000000000000000000 : ℝ)) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50088723204153485829/50000000000000000000 : ℝ) ≤ (5001956255228433/5000000000000000 : ℝ) ^ (4641/1024 : ℝ) := by
    have hpowers : (50088723204153485829/50000000000000000000 : ℝ)^1024 ≤ (5001956255228433/5000000000000000 : ℝ)^4641 := by
      have hnat : (50088723204153485829 : ℕ)^1024*5000000000000000^4641 ≤ 5001956255228433^4641*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50088723204153485829 50000000000000000000 5001956255228433 5000000000000000 1024 4641 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001956255228433/5000000000000000 : ℝ)) (X := (50088723204153485829/50000000000000000000 : ℝ)) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50177418491210915399/50000000000000000000 : ℝ) ≤ (10007823788976643/10000000000000000 : ℝ) ^ (4641/1024 : ℝ) := by
    have hpowers : (50177418491210915399/50000000000000000000 : ℝ)^1024 ≤ (10007823788976643/10000000000000000 : ℝ)^4641 := by
      have hnat : (50177418491210915399 : ℕ)^1024*10000000000000000^4641 ≤ 10007823788976643^4641*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50177418491210915399 50000000000000000000 10007823788976643 10000000000000000 1024 4641 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007823788976643/10000000000000000 : ℝ)) (X := (50177418491210915399/50000000000000000000 : ℝ)) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(27917096056259/100000000000000000000 : ℝ) ≤ ((105676010643242291981/105690000000000000000 : ℝ)+2*(3911278519777/2113800000000000 : ℝ)*(179/5000 : ℝ))^(4641/1024 : ℝ) := by
    rw [show (105676010643242291981/105690000000000000000 : ℝ)+2*(3911278519777/2113800000000000 : ℝ)*(179/5000 : ℝ)=(10000001231937089/10000000000000000 : ℝ) by norm_num, show 1+2*(27917096056259/100000000000000000000 : ℝ)=(50000027917096056259/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(177418491210915399/100000000000000000000 : ℝ)+(27917096056259/100000000000000000000 : ℝ) ≤ ((105676010643242291981/105690000000000000000 : ℝ)+(3911278519777/2113800000000000 : ℝ)*((12359/50000 : ℝ)+(179/5000 : ℝ)))^(4641/1024 : ℝ) := by
    rw [show (105676010643242291981/105690000000000000000 : ℝ)+(3911278519777/2113800000000000 : ℝ)*((12359/50000 : ℝ)+(179/5000 : ℝ))=(5001956255228433/5000000000000000 : ℝ) by norm_num, show 1+(177418491210915399/100000000000000000000 : ℝ)+(27917096056259/100000000000000000000 : ℝ)=(50088723204153485829/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(177418491210915399/100000000000000000000 : ℝ) ≤ ((105676010643242291981/105690000000000000000 : ℝ)+2*(3911278519777/2113800000000000 : ℝ)*(12359/50000 : ℝ))^(4641/1024 : ℝ) := by
    rw [show (105676010643242291981/105690000000000000000 : ℝ)+2*(3911278519777/2113800000000000 : ℝ)*(12359/50000 : ℝ)=(10007823788976643/10000000000000000 : ℝ) by norm_num, show 1+2*(177418491210915399/100000000000000000000 : ℝ)=(50177418491210915399/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (105676010643242291981/105690000000000000000 : ℝ)*(X 1 0+X 2 0)+(3911278519777/2113800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4641/1024 : ℝ)) (lo := (179/5000 : ℝ)) (hi := (12359/50000 : ℝ)) (c := (105676010643242291981/105690000000000000000 : ℝ)) (alpha := (3911278519777/2113800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (105676010643242291981/105690000000000000000 : ℝ)*(X 0 1+X 2 1)+(3911278519777/2113800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4641/1024 : ℝ)) (lo := (179/5000 : ℝ)) (hi := (12359/50000 : ℝ)) (c := (105676010643242291981/105690000000000000000 : ℝ)) (alpha := (3911278519777/2113800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (105676010643242291981/105690000000000000000 : ℝ)*(X 0 2+X 1 2)+(3911278519777/2113800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4641/1024 : ℝ)) (lo := (179/5000 : ℝ)) (hi := (12359/50000 : ℝ)) (c := (105676010643242291981/105690000000000000000 : ℝ)) (alpha := (3911278519777/2113800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1760851939/10000000000 : ℝ)*X 0 0+(172910599/312500000 : ℝ)*X 0 1+(1025186151/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5375933191/10000000000 : ℝ)*X 1 0+(-986891629/5000000000 : ℝ)*X 1 1+(1025186091/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((134398327/250000000 : ℝ)*X 2 0+(2562965343/5000000000 : ℝ)*X 2 1+(-986891551/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((528420967/1250000000 : ℝ)*X 0 0+(3767827227/10000000000 : ℝ)*X 0 1+(2365517039/5000000000 : ℝ)*X 0 2+(528420967/1250000000 : ℝ)*X 1 0+(3767827227/10000000000 : ℝ)*X 1 1+(2365517039/5000000000 : ℝ)*X 1 2+(528420967/1250000000 : ℝ)*X 2 0+(3767827227/10000000000 : ℝ)*X 2 1+(2365517039/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-880529697/5000000000 : ℝ)*X 0 0+(2565057313/5000000000 : ℝ)*X 0 1+(5528893839/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5267962897/10000000000 : ℝ)*X 1 0+(-1570819861/10000000000 : ℝ)*X 1 1+(1382223587/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5267962309/10000000000 : ℝ)*X 2 0+(691111821/1250000000 : ℝ)*X 2 1+(-12566563/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2113928719/5000000000 : ℝ)*X 0 0+(4721137949/10000000000 : ℝ)*X 0 1+(188893447/500000000 : ℝ)*X 0 2+(2113928719/5000000000 : ℝ)*X 1 0+(4721137949/10000000000 : ℝ)*X 1 1+(188893447/500000000 : ℝ)*X 1 2+(2113928719/5000000000 : ℝ)*X 2 0+(4721137949/10000000000 : ℝ)*X 2 1+(188893447/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1525238376835228115764501401/440375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (302119341/25000000000000 : ℝ)*(base19) + (1157501593/100000000000000 : ℝ)*(base23) + (1993687/3125000000000 : ℝ)*(upper3) + (36311/25000000000000 : ℝ)*(upper4) + (71859767/50000000000000 : ℝ)*(upper5) + (436746878935821/25000000000000 : ℝ)*(major0) + (436746878935821/25000000000000 : ℝ)*(major1) + (436746878935821/25000000000000 : ℝ)*(major2) + (122787736732799/5000000000000 : ℝ)*(sp0) + (2455764731902583/100000000000000 : ℝ)*(sp1) + (1227882391439177/50000000000000 : ℝ)*(sp2) + (519102001200757/50000000000000 : ℝ)*(sp3) + (11205723967/100000000000000 : ℝ)*(sp4) + (4973255137/100000000000000 : ℝ)*(sp7) + (1038208975656651/100000000000000 : ℝ)*(f.failure) + (2455765940379947/100000000000000 : ℝ)*(f.sum) + (18898112575349/8807500000000000000000000000 : ℝ)*base65 + (274331977882149533/880750000000000000000000000000000 : ℝ)*base68 + (3138258498850467/880750000000000000000000000000000 : ℝ)*base69 + (4073171574425350467/880750000000000000000000000000000 : ℝ)*base71 + (18918402541923/17615000000000000000000000000 : ℝ)*base73 + (4739930413050149533/880750000000000000000000000000000 : ℝ)*base76 + (3286567400009899533/880750000000000000000000000000000 : ℝ)*base78 + (3977801935088649533/880750000000000000000000000000000 : ℝ)*base80 + (36577454251709/8807500000000000000000000000 : ℝ)*base81 + (4782519/1250000000000000000000 : ℝ)*base89 + (4782519/1250000000000000000000 : ℝ)*base91 + (4782519/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2286328123314476134203423/271000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1490289473/100000000000000 : ℝ)*(base19) + (670545273/50000000000000 : ℝ)*(base23) + (9800117/12500000000000 : ℝ)*(upper2) + (29386483/10000000000000 : ℝ)*(upper3) + (18141473/12500000000000 : ℝ)*(upper5) + (7135585047921/400000000000 : ℝ)*(major0) + (7135585047921/400000000000 : ℝ)*(major1) + (7135585047921/400000000000 : ℝ)*(major2) + (3102627049/25000000000000 : ℝ)*(sp1) + (11526075221/100000000000000 : ℝ)*(sp2) + (1253824471132293/50000000000000 : ℝ)*(sp4) + (2507635041466917/100000000000000 : ℝ)*(sp5) + (125381803754941/5000000000000 : ℝ)*(sp6) + (212028660094947/20000000000000 : ℝ)*(sp7) + (212028660094947/20000000000000 : ℝ)*(f.failure) + (1253824471132293/50000000000000 : ℝ)*(f.sum) + (15268749267417/3523000000000000000000000000 : ℝ)*base65 + (63937081057665167/14092000000000000000000000000000 : ℝ)*base67 + (88774749600989167/14092000000000000000000000000000 : ℝ)*base69 + (97223969505777167/14092000000000000000000000000000 : ℝ)*base71 + (25668387609/704600000000000000000000000 : ℝ)*base73 + (79044101817925167/14092000000000000000000000000000 : ℝ)*base75 + (138236282440877167/14092000000000000000000000000000 : ℝ)*base77 + (52024669763094833/14092000000000000000000000000000 : ℝ)*base80 + (1409091779741/3523000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1229457/250000000000000000000 : ℝ)*base90 + (1229457/250000000000000000000 : ℝ)*base92 + (1229457/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1573_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21033669/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12359/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (179/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9103/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (554/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1573_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1573_s2_0 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-889590623/5000000000 : ℝ)*x 0 + (170021837/312500000 : ℝ)*x 1 + (5206423171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (889590623/5000000000 : ℝ)^4643 ≤ (1364517752093/12500000000000 : ℝ)^3619 := by
    have hnat : (889590623 : ℕ)^4643*12500000000000^3619 ≤ 1364517752093^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889590623 5000000000 1364517752093 12500000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170021837/312500000 : ℝ)^4643 ≤ (22899599705103/50000000000000 : ℝ)^3619 := by
    have hnat : (170021837 : ℕ)^4643*50000000000000^3619 ≤ 22899599705103^3619*312500000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170021837 312500000 22899599705103 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5206423171/10000000000 : ℝ)^4643 ≤ (21642329280041/50000000000000 : ℝ)^3619 := by
    have hnat : (5206423171 : ℕ)^4643*50000000000000^3619 ≤ 21642329280041^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206423171 10000000000 21642329280041 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-889590623/5000000000 : ℝ), (170021837/312500000 : ℝ), (5206423171/10000000000 : ℝ)] ![(1364517752093/12500000000000 : ℝ), (22899599705103/50000000000000 : ℝ), (21642329280041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-889590623/5000000000 : ℝ)|^4643 ≤ (1364517752093/12500000000000 : ℝ)^3619
        have hw : |(-889590623/5000000000 : ℝ)|=(889590623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(170021837/312500000 : ℝ)|^4643 ≤ (22899599705103/50000000000000 : ℝ)^3619
        have hw : |(170021837/312500000 : ℝ)|=(170021837/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5206423171/10000000000 : ℝ)|^4643 ≤ (21642329280041/50000000000000 : ℝ)^3619
        have hw : |(5206423171/10000000000 : ℝ)|=(5206423171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s2_1 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352039463/10000000000 : ℝ)*x 0 + (-949704781/5000000000 : ℝ)*x 1 + (1301605683/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352039463/10000000000 : ℝ)^4643 ≤ (44843917883197/100000000000000 : ℝ)^3619 := by
    have hnat : (5352039463 : ℕ)^4643*100000000000000^3619 ≤ 44843917883197^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352039463 10000000000 44843917883197 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (949704781/5000000000 : ℝ)^4643 ≤ (11871428226871/100000000000000 : ℝ)^3619 := by
    have hnat : (949704781 : ℕ)^4643*100000000000000^3619 ≤ 11871428226871^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949704781 5000000000 11871428226871 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1301605683/2500000000 : ℝ)^4643 ≤ (1731386155107/4000000000000 : ℝ)^3619 := by
    have hnat : (1301605683 : ℕ)^4643*4000000000000^3619 ≤ 1731386155107^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301605683 2500000000 1731386155107 4000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352039463/10000000000 : ℝ), (-949704781/5000000000 : ℝ), (1301605683/2500000000 : ℝ)] ![(44843917883197/100000000000000 : ℝ), (11871428226871/100000000000000 : ℝ), (1731386155107/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352039463/10000000000 : ℝ)|^4643 ≤ (44843917883197/100000000000000 : ℝ)^3619
        have hw : |(5352039463/10000000000 : ℝ)|=(5352039463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-949704781/5000000000 : ℝ)|^4643 ≤ (11871428226871/100000000000000 : ℝ)^3619
        have hw : |(-949704781/5000000000 : ℝ)|=(949704781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1301605683/2500000000 : ℝ)|^4643 ≤ (1731386155107/4000000000000 : ℝ)^3619
        have hw : |(1301605683/2500000000 : ℝ)|=(1301605683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s2_2 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352039923/10000000000 : ℝ)*x 0 + (5206422439/10000000000 : ℝ)*x 1 + (-949704667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352039923/10000000000 : ℝ)^4643 ≤ (11210980707009/25000000000000 : ℝ)^3619 := by
    have hnat : (5352039923 : ℕ)^4643*25000000000000^3619 ≤ 11210980707009^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352039923 10000000000 11210980707009 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5206422439/10000000000 : ℝ)^4643 ≤ (8656930150503/20000000000000 : ℝ)^3619 := by
    have hnat : (5206422439 : ℕ)^4643*20000000000000^3619 ≤ 8656930150503^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206422439 10000000000 8656930150503 20000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (949704667/5000000000 : ℝ)^4643 ≤ (11871426398647/100000000000000 : ℝ)^3619 := by
    have hnat : (949704667 : ℕ)^4643*100000000000000^3619 ≤ 11871426398647^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949704667 5000000000 11871426398647 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352039923/10000000000 : ℝ), (5206422439/10000000000 : ℝ), (-949704667/5000000000 : ℝ)] ![(11210980707009/25000000000000 : ℝ), (8656930150503/20000000000000 : ℝ), (11871426398647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352039923/10000000000 : ℝ)|^4643 ≤ (11210980707009/25000000000000 : ℝ)^3619
        have hw : |(5352039923/10000000000 : ℝ)|=(5352039923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5206422439/10000000000 : ℝ)|^4643 ≤ (8656930150503/20000000000000 : ℝ)^3619
        have hw : |(5206422439/10000000000 : ℝ)|=(5206422439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-949704667/5000000000 : ℝ)|^4643 ≤ (11871426398647/100000000000000 : ℝ)^3619
        have hw : |(-949704667/5000000000 : ℝ)|=(949704667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s2_3 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530082277/1250000000 : ℝ)*x 0 + (198544499/500000000 : ℝ)*x 1 + (2262521713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530082277/1250000000 : ℝ)^4643 ≤ (33267112624169/100000000000000 : ℝ)^3619 := by
    have hnat : (530082277 : ℕ)^4643*100000000000000^3619 ≤ 33267112624169^3619*1250000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530082277 1250000000 33267112624169 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (198544499/500000000 : ℝ)^4643 ≤ (15288424727019/50000000000000 : ℝ)^3619 := by
    have hnat : (198544499 : ℕ)^4643*50000000000000^3619 ≤ 15288424727019^3619*500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198544499 500000000 15288424727019 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2262521713/5000000000 : ℝ)^4643 ≤ (36156037906353/100000000000000 : ℝ)^3619 := by
    have hnat : (2262521713 : ℕ)^4643*100000000000000^3619 ≤ 36156037906353^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262521713 5000000000 36156037906353 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530082277/1250000000 : ℝ), (198544499/500000000 : ℝ), (2262521713/5000000000 : ℝ)] ![(33267112624169/100000000000000 : ℝ), (15288424727019/50000000000000 : ℝ), (36156037906353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530082277/1250000000 : ℝ)|^4643 ≤ (33267112624169/100000000000000 : ℝ)^3619
        have hw : |(530082277/1250000000 : ℝ)|=(530082277/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(198544499/500000000 : ℝ)|^4643 ≤ (15288424727019/50000000000000 : ℝ)^3619
        have hw : |(198544499/500000000 : ℝ)|=(198544499/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2262521713/5000000000 : ℝ)|^4643 ≤ (36156037906353/100000000000000 : ℝ)^3619
        have hw : |(2262521713/5000000000 : ℝ)|=(2262521713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s2_4 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-889610137/5000000000 : ℝ)*x 0 + (2603907927/5000000000 : ℝ)*x 1 + (1359823697/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (889610137/5000000000 : ℝ)^4643 ≤ (10916449227721/100000000000000 : ℝ)^3619 := by
    have hnat : (889610137 : ℕ)^4643*100000000000000^3619 ≤ 10916449227721^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889610137 5000000000 10916449227721 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2603907927/5000000000 : ℝ)^4643 ≤ (21649756791751/50000000000000 : ℝ)^3619 := by
    have hnat : (2603907927 : ℕ)^4643*50000000000000^3619 ≤ 21649756791751^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603907927 5000000000 21649756791751 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359823697/2500000000 : ℝ)^4643 ≤ (45784037171897/100000000000000 : ℝ)^3619 := by
    have hnat : (1359823697 : ℕ)^4643*100000000000000^3619 ≤ 45784037171897^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359823697 2500000000 45784037171897 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-889610137/5000000000 : ℝ), (2603907927/5000000000 : ℝ), (1359823697/2500000000 : ℝ)] ![(10916449227721/100000000000000 : ℝ), (21649756791751/50000000000000 : ℝ), (45784037171897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-889610137/5000000000 : ℝ)|^4643 ≤ (10916449227721/100000000000000 : ℝ)^3619
        have hw : |(-889610137/5000000000 : ℝ)|=(889610137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2603907927/5000000000 : ℝ)|^4643 ≤ (21649756791751/50000000000000 : ℝ)^3619
        have hw : |(2603907927/5000000000 : ℝ)|=(2603907927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359823697/2500000000 : ℝ)|^4643 ≤ (45784037171897/100000000000000 : ℝ)^3619
        have hw : |(1359823697/2500000000 : ℝ)|=(1359823697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s2_5 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290028907/10000000000 : ℝ)*x 0 + (-208317213/1250000000 : ℝ)*x 1 + (2719647869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290028907/10000000000 : ℝ)^4643 ≤ (11044605447499/25000000000000 : ℝ)^3619 := by
    have hnat : (5290028907 : ℕ)^4643*25000000000000^3619 ≤ 11044605447499^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290028907 10000000000 11044605447499 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208317213/1250000000 : ℝ)^4643 ≤ (2509382690029/25000000000000 : ℝ)^3619 := by
    have hnat : (208317213 : ℕ)^4643*25000000000000^3619 ≤ 2509382690029^3619*1250000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208317213 1250000000 2509382690029 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719647869/5000000000 : ℝ)^4643 ≤ (45784047430901/100000000000000 : ℝ)^3619 := by
    have hnat : (2719647869 : ℕ)^4643*100000000000000^3619 ≤ 45784047430901^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719647869 5000000000 45784047430901 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290028907/10000000000 : ℝ), (-208317213/1250000000 : ℝ), (2719647869/5000000000 : ℝ)] ![(11044605447499/25000000000000 : ℝ), (2509382690029/25000000000000 : ℝ), (45784047430901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290028907/10000000000 : ℝ)|^4643 ≤ (11044605447499/25000000000000 : ℝ)^3619
        have hw : |(5290028907/10000000000 : ℝ)|=(5290028907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-208317213/1250000000 : ℝ)|^4643 ≤ (2509382690029/25000000000000 : ℝ)^3619
        have hw : |(-208317213/1250000000 : ℝ)|=(208317213/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719647869/5000000000 : ℝ)|^4643 ≤ (45784047430901/100000000000000 : ℝ)^3619
        have hw : |(2719647869/5000000000 : ℝ)|=(2719647869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s2_6 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322507323/2500000000 : ℝ)*x 0 + (5439296839/10000000000 : ℝ)*x 1 + (-1666535633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322507323/2500000000 : ℝ)^4643 ≤ (44178425914987/100000000000000 : ℝ)^3619 := by
    have hnat : (1322507323 : ℕ)^4643*100000000000000^3619 ≤ 44178425914987^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322507323 2500000000 44178425914987 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439296839/10000000000 : ℝ)^4643 ≤ (11446014830137/25000000000000 : ℝ)^3619 := by
    have hnat : (5439296839 : ℕ)^4643*25000000000000^3619 ≤ 11446014830137^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439296839 10000000000 11446014830137 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1666535633/10000000000 : ℝ)^4643 ≤ (10037514757099/100000000000000 : ℝ)^3619 := by
    have hnat : (1666535633 : ℕ)^4643*100000000000000^3619 ≤ 10037514757099^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1666535633 10000000000 10037514757099 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322507323/2500000000 : ℝ), (5439296839/10000000000 : ℝ), (-1666535633/10000000000 : ℝ)] ![(44178425914987/100000000000000 : ℝ), (11446014830137/25000000000000 : ℝ), (10037514757099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322507323/2500000000 : ℝ)|^4643 ≤ (44178425914987/100000000000000 : ℝ)^3619
        have hw : |(1322507323/2500000000 : ℝ)|=(1322507323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439296839/10000000000 : ℝ)|^4643 ≤ (11446014830137/25000000000000 : ℝ)^3619
        have hw : |(5439296839/10000000000 : ℝ)|=(5439296839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1666535633/10000000000 : ℝ)|^4643 ≤ (10037514757099/100000000000000 : ℝ)^3619
        have hw : |(-1666535633/10000000000 : ℝ)|=(1666535633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s2_7 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2120375743/5000000000 : ℝ)*x 0 + (4521749961/10000000000 : ℝ)*x 1 + (248388231/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120375743/5000000000 : ℝ)^4643 ≤ (33268051342429/100000000000000 : ℝ)^3619 := by
    have hnat : (2120375743 : ℕ)^4643*100000000000000^3619 ≤ 33268051342429^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120375743 5000000000 33268051342429 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4521749961/10000000000 : ℝ)^4643 ≤ (18061139961091/50000000000000 : ℝ)^3619 := by
    have hnat : (4521749961 : ℕ)^4643*50000000000000^3619 ≤ 18061139961091^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521749961 10000000000 18061139961091 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (248388231/625000000 : ℝ)^4643 ≤ (6121933744003/20000000000000 : ℝ)^3619 := by
    have hnat : (248388231 : ℕ)^4643*20000000000000^3619 ≤ 6121933744003^3619*625000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248388231 625000000 6121933744003 20000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2120375743/5000000000 : ℝ), (4521749961/10000000000 : ℝ), (248388231/625000000 : ℝ)] ![(33268051342429/100000000000000 : ℝ), (18061139961091/50000000000000 : ℝ), (6121933744003/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2120375743/5000000000 : ℝ)|^4643 ≤ (33268051342429/100000000000000 : ℝ)^3619
        have hw : |(2120375743/5000000000 : ℝ)|=(2120375743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4521749961/10000000000 : ℝ)|^4643 ≤ (18061139961091/50000000000000 : ℝ)^3619
        have hw : |(4521749961/10000000000 : ℝ)|=(4521749961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(248388231/625000000 : ℝ)|^4643 ≤ (6121933744003/20000000000000 : ℝ)^3619
        have hw : |(248388231/625000000 : ℝ)|=(248388231/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1573_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21033669/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (554/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9103/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2709/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3951/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (554/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9103/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (554/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9103/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (554/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9103/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (554/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9103/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (554/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9103/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (554/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9103/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9103/100000 : ℝ) ^ (4641/1024 : ℝ) ≤ (29964605470331/1562500000000000000 : ℝ) := by
    have hpowers : (9103/100000 : ℝ)^4641 ≤ (29964605470331/1562500000000000000 : ℝ)^1024 := by
      have hnat : (9103 : ℕ)^4641*1562500000000000000^1024 ≤ 29964605470331^1024*100000^4641 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9103 100000 29964605470331 1562500000000000000 4641 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9103/100000 : ℝ)) (X := (29964605470331/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (554/3125 : ℝ) ^ (4641/1024 : ℝ) ≤ (19666439222860147/50000000000000000000 : ℝ) := by
    have hpowers : (554/3125 : ℝ)^4641 ≤ (19666439222860147/50000000000000000000 : ℝ)^1024 := by
      have hnat : (554 : ℕ)^4641*50000000000000000000^1024 ≤ 19666439222860147^1024*3125^4641 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        554 3125 19666439222860147 50000000000000000000 4641 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (554/3125 : ℝ)) (X := (19666439222860147/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (781279964605470331/781250000000000000 : ℝ) ≤ (625005289083803/625000000000000 : ℝ) ^ (4641/1024 : ℝ) := by
    have hpowers : (781279964605470331/781250000000000000 : ℝ)^1024 ≤ (625005289083803/625000000000000 : ℝ)^4641 := by
      have hnat : (781279964605470331 : ℕ)^1024*625000000000000^4641 ≤ 625005289083803^4641*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781279964605470331 781250000000000000 625005289083803 625000000000000 1024 4641 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625005289083803/625000000000000 : ℝ)) (X := (781279964605470331/781250000000000000 : ℝ)) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020625306597910739/50000000000000000000 : ℝ) ≤ (10000910015936339/10000000000000000 : ℝ) ^ (4641/1024 : ℝ) := by
    have hpowers : (50020625306597910739/50000000000000000000 : ℝ)^1024 ≤ (10000910015936339/10000000000000000 : ℝ)^4641 := by
      have hnat : (50020625306597910739 : ℕ)^1024*10000000000000000^4641 ≤ 10000910015936339^4641*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020625306597910739 50000000000000000000 10000910015936339 10000000000000000 1024 4641 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000910015936339/10000000000000000 : ℝ)) (X := (50020625306597910739/50000000000000000000 : ℝ)) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25019666439222860147/25000000000000000000 : ℝ) ≤ (1000173540653183/1000000000000000 : ℝ) ^ (4641/1024 : ℝ) := by
    have hpowers : (25019666439222860147/25000000000000000000 : ℝ)^1024 ≤ (1000173540653183/1000000000000000 : ℝ)^4641 := by
      have hnat : (25019666439222860147 : ℕ)^1024*1000000000000000^4641 ≤ 1000173540653183^4641*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019666439222860147 25000000000000000000 1000173540653183 1000000000000000 1024 4641 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000173540653183/1000000000000000 : ℝ)) (X := (25019666439222860147/25000000000000000000 : ℝ)) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(29964605470331/1562500000000000000 : ℝ) ≤ ((14372617138730550809/14375000000000000000 : ℝ)+2*(275130198497/287500000000000 : ℝ)*(9103/100000 : ℝ))^(4641/1024 : ℝ) := by
    rw [show (14372617138730550809/14375000000000000000 : ℝ)+2*(275130198497/287500000000000 : ℝ)*(9103/100000 : ℝ)=(625005289083803/625000000000000 : ℝ) by norm_num, show 1+2*(29964605470331/1562500000000000000 : ℝ)=(781279964605470331/781250000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19666439222860147/50000000000000000000 : ℝ)+(29964605470331/1562500000000000000 : ℝ) ≤ ((14372617138730550809/14375000000000000000 : ℝ)+(275130198497/287500000000000 : ℝ)*((554/3125 : ℝ)+(9103/100000 : ℝ)))^(4641/1024 : ℝ) := by
    rw [show (14372617138730550809/14375000000000000000 : ℝ)+(275130198497/287500000000000 : ℝ)*((554/3125 : ℝ)+(9103/100000 : ℝ))=(10000910015936339/10000000000000000 : ℝ) by norm_num, show 1+(19666439222860147/50000000000000000000 : ℝ)+(29964605470331/1562500000000000000 : ℝ)=(50020625306597910739/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19666439222860147/50000000000000000000 : ℝ) ≤ ((14372617138730550809/14375000000000000000 : ℝ)+2*(275130198497/287500000000000 : ℝ)*(554/3125 : ℝ))^(4641/1024 : ℝ) := by
    rw [show (14372617138730550809/14375000000000000000 : ℝ)+2*(275130198497/287500000000000 : ℝ)*(554/3125 : ℝ)=(1000173540653183/1000000000000000 : ℝ) by norm_num, show 1+2*(19666439222860147/50000000000000000000 : ℝ)=(25019666439222860147/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14372617138730550809/14375000000000000000 : ℝ)*(X 1 0+X 2 0)+(275130198497/287500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4641/1024 : ℝ)) (lo := (9103/100000 : ℝ)) (hi := (554/3125 : ℝ)) (c := (14372617138730550809/14375000000000000000 : ℝ)) (alpha := (275130198497/287500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14372617138730550809/14375000000000000000 : ℝ)*(X 0 1+X 2 1)+(275130198497/287500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4641/1024 : ℝ)) (lo := (9103/100000 : ℝ)) (hi := (554/3125 : ℝ)) (c := (14372617138730550809/14375000000000000000 : ℝ)) (alpha := (275130198497/287500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14372617138730550809/14375000000000000000 : ℝ)*(X 0 2+X 1 2)+(275130198497/287500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4641/1024 : ℝ)) (lo := (9103/100000 : ℝ)) (hi := (554/3125 : ℝ)) (c := (14372617138730550809/14375000000000000000 : ℝ)) (alpha := (275130198497/287500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-889590623/5000000000 : ℝ)*X 0 0+(170021837/312500000 : ℝ)*X 0 1+(5206423171/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352039463/10000000000 : ℝ)*X 1 0+(-949704781/5000000000 : ℝ)*X 1 1+(1301605683/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352039923/10000000000 : ℝ)*X 2 0+(5206422439/10000000000 : ℝ)*X 2 1+(-949704667/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((530082277/1250000000 : ℝ)*X 0 0+(198544499/500000000 : ℝ)*X 0 1+(2262521713/5000000000 : ℝ)*X 0 2+(530082277/1250000000 : ℝ)*X 1 0+(198544499/500000000 : ℝ)*X 1 1+(2262521713/5000000000 : ℝ)*X 1 2+(530082277/1250000000 : ℝ)*X 2 0+(198544499/500000000 : ℝ)*X 2 1+(2262521713/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-889610137/5000000000 : ℝ)*X 0 0+(2603907927/5000000000 : ℝ)*X 0 1+(1359823697/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5290028907/10000000000 : ℝ)*X 1 0+(-208317213/1250000000 : ℝ)*X 1 1+(2719647869/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1322507323/2500000000 : ℝ)*X 2 0+(5439296839/10000000000 : ℝ)*X 2 1+(-1666535633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2120375743/5000000000 : ℝ)*X 0 0+(4521749961/10000000000 : ℝ)*X 0 1+(248388231/625000000 : ℝ)*X 0 2+(2120375743/5000000000 : ℝ)*X 1 0+(4521749961/10000000000 : ℝ)*X 1 1+(248388231/625000000 : ℝ)*X 1 2+(2120375743/5000000000 : ℝ)*X 2 0+(4521749961/10000000000 : ℝ)*X 2 1+(248388231/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (93983467783141018031561109/7812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1866828509/100000000000000 : ℝ)*(base19) + (1040821503/50000000000000 : ℝ)*(base23) + (81382001/100000000000000 : ℝ)*(lower2) + (179800071/100000000000000 : ℝ)*(upper3) + (329836457/100000000000000 : ℝ)*(upper5) + (1518272086315541/50000000000000 : ℝ)*(major0) + (1518272086315541/50000000000000 : ℝ)*(major1) + (1518272086315541/50000000000000 : ℝ)*(major2) + (106712294040787/2500000000000 : ℝ)*(sp0) + (266782034685201/6250000000000 : ℝ)*(sp1) + (2134256170074359/50000000000000 : ℝ)*(sp2) + (180456397632173/10000000000000 : ℝ)*(sp3) + (5665040061/25000000000000 : ℝ)*(sp4) + (9546152573/100000000000000 : ℝ)*(sp7) + (902286761237151/50000000000000 : ℝ)*(f.failure) + (1067128605447931/25000000000000 : ℝ)*(f.sum) + (303105788437/1796875000000000000000000000 : ℝ)*base66 + (3836334865693077331/718750000000000000000000000000000 : ℝ)*base68 + (6654250584224327331/718750000000000000000000000000000 : ℝ)*base70 + (10066680102911827331/718750000000000000000000000000000 : ℝ)*base72 + (45893371993121/14375000000000000000000000000 : ℝ)*base74 + (14227859317974327331/718750000000000000000000000000000 : ℝ)*base76 + (7154215766599327331/718750000000000000000000000000000 : ℝ)*base78 + (1901838458119422669/718750000000000000000000000000000 : ℝ)*base79 + (1023469198123/7187500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2137019/625000000000000000000 : ℝ)*base89 + (2137019/625000000000000000000 : ℝ)*base91 + (2137019/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5001962539756844559270937569/359375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8566659/2500000000000 : ℝ)*(base23) + (242590919/100000000000000 : ℝ)*(lower2) + (52473613/25000000000000 : ℝ)*(upper3) + (24289551/100000000000000 : ℝ)*(lower4) + (29614473/100000000000000 : ℝ)*(upper5) + (1536602952973151/50000000000000 : ℝ)*(major0) + (1536602952973151/50000000000000 : ℝ)*(major1) + (1536602952973151/50000000000000 : ℝ)*(major2) + (344411453/4000000000000 : ℝ)*(sp1) + (9244989107/20000000000000 : ℝ)*(sp2) + (4320050296794941/100000000000000 : ℝ)*(sp4) + (540005210813577/12500000000000 : ℝ)*(sp5) + (2160001864591523/50000000000000 : ℝ)*(sp6) + (1826361051147509/100000000000000 : ℝ)*(sp7) + (1826361051147509/100000000000000 : ℝ)*(f.failure) + (4320050296794941/100000000000000 : ℝ)*(f.sum) + (102944180797797/7187500000000000000000000000 : ℝ)*base65 + (1169649285464429159/718750000000000000000000000000000 : ℝ)*base67 + (4976766685245679159/718750000000000000000000000000000 : ℝ)*base69 + (5153060399401929159/718750000000000000000000000000000 : ℝ)*base71 + (71968677020031/14375000000000000000000000000 : ℝ)*base74 + (2869570653995679159/718750000000000000000000000000000 : ℝ)*base75 + (4638024957214429159/718750000000000000000000000000000 : ℝ)*base77 + (1162277178120679159/718750000000000000000000000000000 : ℝ)*base79 + (33480670785953/7187500000000000000000000000 : ℝ)*base82 + (519479/1250000000000000000000 : ℝ)*base90 + (519479/1250000000000000000000 : ℝ)*base92 + (519479/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1573_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21033669/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (554/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9103/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2709/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3951/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1573_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1573_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21033669/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2709/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3951/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1573_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1573_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1573_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21033669/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2709/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3951/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1573_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
