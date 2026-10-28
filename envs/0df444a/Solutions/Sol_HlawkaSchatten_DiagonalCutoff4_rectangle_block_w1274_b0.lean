-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1274_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:30.88852+00:00
-- url     : https://prove2.me/submissions/bc803c22-1dd1-40bb-a710-9f40627c5427

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
theorem support_rectangle_w1274_s0_0 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-18504201/100000000 : ℝ)*x 0 + (6024098673/10000000000 : ℝ)*x 1 + (959411853/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18504201/100000000 : ℝ)^2117 ≤ (5401287524881/50000000000000 : ℝ)^1605 := by
    have hnat : (18504201 : ℕ)^2117*50000000000000^1605 ≤ 5401287524881^1605*100000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18504201 100000000 5401287524881 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6024098673/10000000000 : ℝ)^2117 ≤ (10249601000109/20000000000000 : ℝ)^1605 := by
    have hnat : (6024098673 : ℕ)^2117*20000000000000^1605 ≤ 10249601000109^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6024098673 10000000000 10249601000109 20000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (959411853/2000000000 : ℝ)^2117 ≤ (37949419926763/100000000000000 : ℝ)^1605 := by
    have hnat : (959411853 : ℕ)^2117*100000000000000^1605 ≤ 37949419926763^1605*2000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959411853 2000000000 37949419926763 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-18504201/100000000 : ℝ), (6024098673/10000000000 : ℝ), (959411853/2000000000 : ℝ)] ![(5401287524881/50000000000000 : ℝ), (10249601000109/20000000000000 : ℝ), (37949419926763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-18504201/100000000 : ℝ)|^2117 ≤ (5401287524881/50000000000000 : ℝ)^1605
        have hw : |(-18504201/100000000 : ℝ)|=(18504201/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6024098673/10000000000 : ℝ)|^2117 ≤ (10249601000109/20000000000000 : ℝ)^1605
        have hw : |(6024098673/10000000000 : ℝ)|=(6024098673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(959411853/2000000000 : ℝ)|^2117 ≤ (37949419926763/100000000000000 : ℝ)^1605
        have hw : |(959411853/2000000000 : ℝ)|=(959411853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s0_1 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (688662563/1250000000 : ℝ)*x 0 + (-2551012991/10000000000 : ℝ)*x 1 + (2398529617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (688662563/1250000000 : ℝ)^2117 ≤ (45551787753313/100000000000000 : ℝ)^1605 := by
    have hnat : (688662563 : ℕ)^2117*100000000000000^1605 ≤ 45551787753313^1605*1250000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688662563 1250000000 45551787753313 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2551012991/10000000000 : ℝ)^2117 ≤ (16498792622603/100000000000000 : ℝ)^1605 := by
    have hnat : (2551012991 : ℕ)^2117*100000000000000^1605 ≤ 16498792622603^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2551012991 10000000000 16498792622603 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2398529617/5000000000 : ℝ)^2117 ≤ (3794941960329/10000000000000 : ℝ)^1605 := by
    have hnat : (2398529617 : ℕ)^2117*10000000000000^1605 ≤ 3794941960329^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2398529617 5000000000 3794941960329 10000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(688662563/1250000000 : ℝ), (-2551012991/10000000000 : ℝ), (2398529617/5000000000 : ℝ)] ![(45551787753313/100000000000000 : ℝ), (16498792622603/100000000000000 : ℝ), (3794941960329/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(688662563/1250000000 : ℝ)|^2117 ≤ (45551787753313/100000000000000 : ℝ)^1605
        have hw : |(688662563/1250000000 : ℝ)|=(688662563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2551012991/10000000000 : ℝ)|^2117 ≤ (16498792622603/100000000000000 : ℝ)^1605
        have hw : |(-2551012991/10000000000 : ℝ)|=(2551012991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2398529617/5000000000 : ℝ)|^2117 ≤ (3794941960329/10000000000000 : ℝ)^1605
        have hw : |(2398529617/5000000000 : ℝ)|=(2398529617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s0_2 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2754650261/5000000000 : ℝ)*x 0 + (4797059239/10000000000 : ℝ)*x 1 + (-2551012963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2754650261/5000000000 : ℝ)^2117 ≤ (2846986746851/6250000000000 : ℝ)^1605 := by
    have hnat : (2754650261 : ℕ)^2117*6250000000000^1605 ≤ 2846986746851^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754650261 5000000000 2846986746851 6250000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4797059239/10000000000 : ℝ)^2117 ≤ (37949419655463/100000000000000 : ℝ)^1605 := by
    have hnat : (4797059239 : ℕ)^2117*100000000000000^1605 ≤ 37949419655463^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4797059239 10000000000 37949419655463 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2551012963/10000000000 : ℝ)^2117 ≤ (64448407749/390625000000 : ℝ)^1605 := by
    have hnat : (2551012963 : ℕ)^2117*390625000000^1605 ≤ 64448407749^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2551012963 10000000000 64448407749 390625000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2754650261/5000000000 : ℝ), (4797059239/10000000000 : ℝ), (-2551012963/10000000000 : ℝ)] ![(2846986746851/6250000000000 : ℝ), (37949419655463/100000000000000 : ℝ), (64448407749/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2754650261/5000000000 : ℝ)|^2117 ≤ (2846986746851/6250000000000 : ℝ)^1605
        have hw : |(2754650261/5000000000 : ℝ)|=(2754650261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4797059239/10000000000 : ℝ)|^2117 ≤ (37949419655463/100000000000000 : ℝ)^1605
        have hw : |(4797059239/10000000000 : ℝ)|=(4797059239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2551012963/10000000000 : ℝ)|^2117 ≤ (64448407749/390625000000 : ℝ)^1605
        have hw : |(-2551012963/10000000000 : ℝ)|=(2551012963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s0_3 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4190441809/10000000000 : ℝ)*x 0 + (3115698907/10000000000 : ℝ)*x 1 + (1405176223/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4190441809/10000000000 : ℝ)^2117 ≤ (7937788567767/25000000000000 : ℝ)^1605 := by
    have hnat : (4190441809 : ℕ)^2117*25000000000000^1605 ≤ 7937788567767^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4190441809 10000000000 7937788567767 25000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3115698907/10000000000 : ℝ)^2117 ≤ (10739105461503/50000000000000 : ℝ)^1605 := by
    have hnat : (3115698907 : ℕ)^2117*50000000000000^1605 ≤ 10739105461503^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3115698907 10000000000 10739105461503 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1405176223/2500000000 : ℝ)^2117 ≤ (11692658697693/25000000000000 : ℝ)^1605 := by
    have hnat : (1405176223 : ℕ)^2117*25000000000000^1605 ≤ 11692658697693^1605*2500000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1405176223 2500000000 11692658697693 25000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4190441809/10000000000 : ℝ), (3115698907/10000000000 : ℝ), (1405176223/2500000000 : ℝ)] ![(7937788567767/25000000000000 : ℝ), (10739105461503/50000000000000 : ℝ), (11692658697693/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4190441809/10000000000 : ℝ)|^2117 ≤ (7937788567767/25000000000000 : ℝ)^1605
        have hw : |(4190441809/10000000000 : ℝ)|=(4190441809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3115698907/10000000000 : ℝ)|^2117 ≤ (10739105461503/50000000000000 : ℝ)^1605
        have hw : |(3115698907/10000000000 : ℝ)|=(3115698907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1405176223/2500000000 : ℝ)|^2117 ≤ (11692658697693/25000000000000 : ℝ)^1605
        have hw : |(1405176223/2500000000 : ℝ)|=(1405176223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s0_4 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-231898061/1250000000 : ℝ)*x 0 + (4828635851/10000000000 : ℝ)*x 1 + (5991405059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (231898061/1250000000 : ℝ)^2117 ≤ (10839276913031/100000000000000 : ℝ)^1605 := by
    have hnat : (231898061 : ℕ)^2117*100000000000000^1605 ≤ 10839276913031^1605*1250000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231898061 1250000000 10839276913031 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4828635851/10000000000 : ℝ)^2117 ≤ (38279254447753/100000000000000 : ℝ)^1605 := by
    have hnat : (4828635851 : ℕ)^2117*100000000000000^1605 ≤ 38279254447753^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4828635851 10000000000 38279254447753 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5991405059/10000000000 : ℝ)^2117 ≤ (50881468634229/100000000000000 : ℝ)^1605 := by
    have hnat : (5991405059 : ℕ)^2117*100000000000000^1605 ≤ 50881468634229^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5991405059 10000000000 50881468634229 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-231898061/1250000000 : ℝ), (4828635851/10000000000 : ℝ), (5991405059/10000000000 : ℝ)] ![(10839276913031/100000000000000 : ℝ), (38279254447753/100000000000000 : ℝ), (50881468634229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-231898061/1250000000 : ℝ)|^2117 ≤ (10839276913031/100000000000000 : ℝ)^1605
        have hw : |(-231898061/1250000000 : ℝ)|=(231898061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4828635851/10000000000 : ℝ)|^2117 ≤ (38279254447753/100000000000000 : ℝ)^1605
        have hw : |(4828635851/10000000000 : ℝ)|=(4828635851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5991405059/10000000000 : ℝ)|^2117 ≤ (50881468634229/100000000000000 : ℝ)^1605
        have hw : |(5991405059/10000000000 : ℝ)|=(5991405059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s0_5 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5175305389/10000000000 : ℝ)*x 0 + (-1356664679/10000000000 : ℝ)*x 1 + (5991407567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5175305389/10000000000 : ℝ)^2117 ≤ (5243130680423/12500000000000 : ℝ)^1605 := by
    have hnat : (5175305389 : ℕ)^2117*12500000000000^1605 ≤ 5243130680423^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175305389 10000000000 5243130680423 12500000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356664679/10000000000 : ℝ)^2117 ≤ (7173457819243/100000000000000 : ℝ)^1605 := by
    have hnat : (1356664679 : ℕ)^2117*100000000000000^1605 ≤ 7173457819243^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356664679 10000000000 7173457819243 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5991407567/10000000000 : ℝ)^2117 ≤ (3180093545477/6250000000000 : ℝ)^1605 := by
    have hnat : (5991407567 : ℕ)^2117*6250000000000^1605 ≤ 3180093545477^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5991407567 10000000000 3180093545477 6250000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5175305389/10000000000 : ℝ), (-1356664679/10000000000 : ℝ), (5991407567/10000000000 : ℝ)] ![(5243130680423/12500000000000 : ℝ), (7173457819243/100000000000000 : ℝ), (3180093545477/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5175305389/10000000000 : ℝ)|^2117 ≤ (5243130680423/12500000000000 : ℝ)^1605
        have hw : |(5175305389/10000000000 : ℝ)|=(5175305389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1356664679/10000000000 : ℝ)|^2117 ≤ (7173457819243/100000000000000 : ℝ)^1605
        have hw : |(-1356664679/10000000000 : ℝ)|=(1356664679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5991407567/10000000000 : ℝ)|^2117 ≤ (3180093545477/6250000000000 : ℝ)^1605
        have hw : |(5991407567/10000000000 : ℝ)|=(5991407567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s0_6 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (646913317/1250000000 : ℝ)*x 0 + (599140547/1000000000 : ℝ)*x 1 + (-1356666289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646913317/1250000000 : ℝ)^2117 ≤ (5243132213147/12500000000000 : ℝ)^1605 := by
    have hnat : (646913317 : ℕ)^2117*12500000000000^1605 ≤ 5243132213147^1605*1250000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646913317 1250000000 5243132213147 12500000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (599140547/1000000000 : ℝ)^2117 ≤ (12720368309513/25000000000000 : ℝ)^1605 := by
    have hnat : (599140547 : ℕ)^2117*25000000000000^1605 ≤ 12720368309513^1605*1000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599140547 1000000000 12720368309513 25000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356666289/10000000000 : ℝ)^2117 ≤ (71734690479/1000000000000 : ℝ)^1605 := by
    have hnat : (1356666289 : ℕ)^2117*1000000000000^1605 ≤ 71734690479^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356666289 10000000000 71734690479 1000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646913317/1250000000 : ℝ), (599140547/1000000000 : ℝ), (-1356666289/10000000000 : ℝ)] ![(5243132213147/12500000000000 : ℝ), (12720368309513/25000000000000 : ℝ), (71734690479/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646913317/1250000000 : ℝ)|^2117 ≤ (5243132213147/12500000000000 : ℝ)^1605
        have hw : |(646913317/1250000000 : ℝ)|=(646913317/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(599140547/1000000000 : ℝ)|^2117 ≤ (12720368309513/25000000000000 : ℝ)^1605
        have hw : |(599140547/1000000000 : ℝ)|=(599140547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1356666289/10000000000 : ℝ)|^2117 ≤ (71734690479/1000000000000 : ℝ)^1605
        have hw : |(-1356666289/10000000000 : ℝ)|=(1356666289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s0_7 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2100085837/5000000000 : ℝ)*x 0 + (5556247503/10000000000 : ℝ)*x 1 + (318243667/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100085837/5000000000 : ℝ)^2117 ≤ (7962107980023/25000000000000 : ℝ)^1605 := by
    have hnat : (2100085837 : ℕ)^2117*25000000000000^1605 ≤ 7962107980023^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100085837 5000000000 7962107980023 25000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5556247503/10000000000 : ℝ)^2117 ≤ (460644736473/1000000000000 : ℝ)^1605 := by
    have hnat : (5556247503 : ℕ)^2117*1000000000000^1605 ≤ 460644736473^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5556247503 10000000000 460644736473 1000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (318243667/1000000000 : ℝ)^2117 ≤ (4417418882741/20000000000000 : ℝ)^1605 := by
    have hnat : (318243667 : ℕ)^2117*20000000000000^1605 ≤ 4417418882741^1605*1000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318243667 1000000000 4417418882741 20000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2100085837/5000000000 : ℝ), (5556247503/10000000000 : ℝ), (318243667/1000000000 : ℝ)] ![(7962107980023/25000000000000 : ℝ), (460644736473/1000000000000 : ℝ), (4417418882741/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2100085837/5000000000 : ℝ)|^2117 ≤ (7962107980023/25000000000000 : ℝ)^1605
        have hw : |(2100085837/5000000000 : ℝ)|=(2100085837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5556247503/10000000000 : ℝ)|^2117 ≤ (460644736473/1000000000000 : ℝ)^1605
        have hw : |(5556247503/10000000000 : ℝ)|=(5556247503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(318243667/1000000000 : ℝ)|^2117 ≤ (4417418882741/20000000000000 : ℝ)^1605
        have hw : |(318243667/1000000000 : ℝ)|=(318243667/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1274_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152075211/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (949/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27313/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8467/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8467 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8467*1^2048 ≤ 0^2048*1^8467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8467 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8467/2048 : ℝ) ≤ (70738469579132217/3125000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8467 ≤ (70738469579132217/3125000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8467*3125000000000000000^2048 ≤ 70738469579132217^2048*5^8467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 70738469579132217 3125000000000000000 8467 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (70738469579132217/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8467/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8467 := by
      have hnat : (1 : ℕ)^2048*1^8467 ≤ 1^8467*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (3195738469579132217/3125000000000000000 : ℝ) ≤ (50271445457543/50000000000000 : ℝ) ^ (8467/2048 : ℝ) := by
    have hpowers : (3195738469579132217/3125000000000000000 : ℝ)^2048 ≤ (50271445457543/50000000000000 : ℝ)^8467 := by
      have hnat : (3195738469579132217 : ℕ)^2048*50000000000000^8467 ≤ 50271445457543^8467*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3195738469579132217 3125000000000000000 50271445457543 50000000000000 2048 8467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50271445457543/50000000000000 : ℝ)) (X := (3195738469579132217/3125000000000000000 : ℝ)) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1633238469579132217/1562500000000000000 : ℝ) ≤ (25271445457543/25000000000000 : ℝ) ^ (8467/2048 : ℝ) := by
    have hpowers : (1633238469579132217/1562500000000000000 : ℝ)^2048 ≤ (25271445457543/25000000000000 : ℝ)^8467 := by
      have hnat : (1633238469579132217 : ℕ)^2048*25000000000000^8467 ≤ 25271445457543^8467*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1633238469579132217 1562500000000000000 25271445457543 25000000000000 2048 8467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (25271445457543/25000000000000 : ℝ)) (X := (1633238469579132217/1562500000000000000 : ℝ)) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(271445457543/20000000000000 : ℝ)*(0 : ℝ))^(8467/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(271445457543/20000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(70738469579132217/3125000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(271445457543/20000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8467/2048 : ℝ) := by
    rw [show (1 : ℝ)+(271445457543/20000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(50271445457543/50000000000000 : ℝ) by norm_num, show 1+(70738469579132217/3125000000000000000 : ℝ)+(0 : ℝ)=(3195738469579132217/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(70738469579132217/3125000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(271445457543/20000000000000 : ℝ)*(2/5 : ℝ))^(8467/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(271445457543/20000000000000 : ℝ)*(2/5 : ℝ)=(25271445457543/25000000000000 : ℝ) by norm_num, show 1+2*(70738469579132217/3125000000000000000 : ℝ)=(1633238469579132217/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(271445457543/20000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8467/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (271445457543/20000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(271445457543/20000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8467/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (271445457543/20000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(271445457543/20000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8467/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (271445457543/20000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-18504201/100000000 : ℝ)*X 0 0+(6024098673/10000000000 : ℝ)*X 0 1+(959411853/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((688662563/1250000000 : ℝ)*X 1 0+(-2551012991/10000000000 : ℝ)*X 1 1+(2398529617/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2754650261/5000000000 : ℝ)*X 2 0+(4797059239/10000000000 : ℝ)*X 2 1+(-2551012963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4190441809/10000000000 : ℝ)*X 0 0+(3115698907/10000000000 : ℝ)*X 0 1+(1405176223/2500000000 : ℝ)*X 0 2+(4190441809/10000000000 : ℝ)*X 1 0+(3115698907/10000000000 : ℝ)*X 1 1+(1405176223/2500000000 : ℝ)*X 1 2+(4190441809/10000000000 : ℝ)*X 2 0+(3115698907/10000000000 : ℝ)*X 2 1+(1405176223/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-231898061/1250000000 : ℝ)*X 0 0+(4828635851/10000000000 : ℝ)*X 0 1+(5991405059/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5175305389/10000000000 : ℝ)*X 1 0+(-1356664679/10000000000 : ℝ)*X 1 1+(5991407567/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((646913317/1250000000 : ℝ)*X 2 0+(599140547/1000000000 : ℝ)*X 2 1+(-1356666289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2100085837/5000000000 : ℝ)*X 0 0+(5556247503/10000000000 : ℝ)*X 0 1+(318243667/1000000000 : ℝ)*X 0 2+(2100085837/5000000000 : ℝ)*X 1 0+(5556247503/10000000000 : ℝ)*X 1 1+(318243667/1000000000 : ℝ)*X 1 2+(2100085837/5000000000 : ℝ)*X 2 0+(5556247503/10000000000 : ℝ)*X 2 1+(318243667/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (197730915880193981733/100000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27645101/100000000000000 : ℝ)*(base1) + (243027903/50000000000000 : ℝ)*(base19) + (244359243/50000000000000 : ℝ)*(base23) + (10518893/20000000000000 : ℝ)*(upper3) + (3025893/5000000000000 : ℝ)*(upper5) + (60708741776377/10000000000000 : ℝ)*(major0) + (60708741776377/10000000000000 : ℝ)*(major1) + (60708741776377/10000000000000 : ℝ)*(major2) + (814971164323747/100000000000000 : ℝ)*(sp0) + (814972195481617/100000000000000 : ℝ)*(sp1) + (407486096409469/50000000000000 : ℝ)*(sp2) + (9980033571113/2500000000000 : ℝ)*(sp3) + (1544858777/100000000000000 : ℝ)*(sp4) + (143518037/20000000000000 : ℝ)*(sp7) + (199601044039903/50000000000000 : ℝ)*(f.failure) + (814972681537423/100000000000000 : ℝ)*(f.sum) + (35874812311/100000000000000000000000000 : ℝ)*base65 + (209793931111/200000000000000000000000000 : ℝ)*base67 + (1806585055889/200000000000000000000000000 : ℝ)*base70 + (953204405889/200000000000000000000000000 : ℝ)*base72 + (458372736911/100000000000000000000000000 : ℝ)*base73 + (595161571889/200000000000000000000000000 : ℝ)*base76 + (1096014539489/200000000000000000000000000 : ℝ)*base78 + (2067759313689/200000000000000000000000000 : ℝ)*base80 + (25204387889/100000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (41144533/5000000000000000000000 : ℝ)*base89 + (41144533/5000000000000000000000 : ℝ)*base91 + (41144533/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4521843579637033149/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (143142283/50000000000000 : ℝ)*(base1) + (222231607/25000000000000 : ℝ)*(base19) + (522592633/50000000000000 : ℝ)*(base23) + (179745117/100000000000000 : ℝ)*(upper3) + (40039996117777/6250000000000 : ℝ)*(major0) + (40039996117777/6250000000000 : ℝ)*(major1) + (40039996117777/6250000000000 : ℝ)*(major2) + (1848340357/100000000000000 : ℝ)*(sp1) + (1316156617/100000000000000 : ℝ)*(sp2) + (399531459/100000000000000 : ℝ)*(sp3) + (107501851735007/12500000000000 : ℝ)*(sp4) + (172002358065741/20000000000000 : ℝ)*(sp5) + (860012166253607/100000000000000 : ℝ)*(sp6) + (210632255814613/50000000000000 : ℝ)*(sp7) + (421265197445251/100000000000000 : ℝ)*(f.failure) + (86001452759549/10000000000000 : ℝ)*(f.sum) + (339080707053/125000000000000000000000000 : ℝ)*base66 + (156675709009/31250000000000000000000000 : ℝ)*base67 + (257366272911/125000000000000000000000000 : ℝ)*base69 + (685025438411/125000000000000000000000000 : ℝ)*base71 + (303644104803/125000000000000000000000000 : ℝ)*base74 + (332532263393/62500000000000000000000000 : ℝ)*base75 + (182450328393/62500000000000000000000000 : ℝ)*base77 + (736405698911/125000000000000000000000000 : ℝ)*base79 + (66950587241/15625000000000000000000000 : ℝ)*base82 + (6772961/10000000000000000000000 : ℝ)*base89 + (6772961/10000000000000000000000 : ℝ)*base91 + (6772961/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1274_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152075211/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (949/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27313/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1274_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1274_s1_0 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-409085831/2000000000 : ℝ)*x 0 + (1133481419/2000000000 : ℝ)*x 1 + (5028920747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (409085831/2000000000 : ℝ)^2117 ≤ (12328848953659/100000000000000 : ℝ)^1605 := by
    have hnat : (409085831 : ℕ)^2117*100000000000000^1605 ≤ 12328848953659^1605*2000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409085831 2000000000 12328848953659 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133481419/2000000000 : ℝ)^2117 ≤ (23641948786959/50000000000000 : ℝ)^1605 := by
    have hnat : (1133481419 : ℕ)^2117*50000000000000^1605 ≤ 23641948786959^1605*2000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133481419 2000000000 23641948786959 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5028920747/10000000000 : ℝ)^2117 ≤ (5048406682401/12500000000000 : ℝ)^1605 := by
    have hnat : (5028920747 : ℕ)^2117*12500000000000^1605 ≤ 5048406682401^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5028920747 10000000000 5048406682401 12500000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-409085831/2000000000 : ℝ), (1133481419/2000000000 : ℝ), (5028920747/10000000000 : ℝ)] ![(12328848953659/100000000000000 : ℝ), (23641948786959/50000000000000 : ℝ), (5048406682401/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-409085831/2000000000 : ℝ)|^2117 ≤ (12328848953659/100000000000000 : ℝ)^1605
        have hw : |(-409085831/2000000000 : ℝ)|=(409085831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1133481419/2000000000 : ℝ)|^2117 ≤ (23641948786959/50000000000000 : ℝ)^1605
        have hw : |(1133481419/2000000000 : ℝ)|=(1133481419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5028920747/10000000000 : ℝ)|^2117 ≤ (5048406682401/12500000000000 : ℝ)^1605
        have hw : |(5028920747/10000000000 : ℝ)|=(5028920747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s1_1 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5411870187/10000000000 : ℝ)*x 0 + (-1193876679/5000000000 : ℝ)*x 1 + (157153767/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5411870187/10000000000 : ℝ)^2117 ≤ (44492248206119/100000000000000 : ℝ)^1605 := by
    have hnat : (5411870187 : ℕ)^2117*100000000000000^1605 ≤ 44492248206119^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411870187 10000000000 44492248206119 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1193876679/5000000000 : ℝ)^2117 ≤ (945031279237/6250000000000 : ℝ)^1605 := by
    have hnat : (1193876679 : ℕ)^2117*6250000000000^1605 ≤ 945031279237^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193876679 5000000000 945031279237 6250000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157153767/312500000 : ℝ)^2117 ≤ (40387251308847/100000000000000 : ℝ)^1605 := by
    have hnat : (157153767 : ℕ)^2117*100000000000000^1605 ≤ 40387251308847^1605*312500000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157153767 312500000 40387251308847 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5411870187/10000000000 : ℝ), (-1193876679/5000000000 : ℝ), (157153767/312500000 : ℝ)] ![(44492248206119/100000000000000 : ℝ), (945031279237/6250000000000 : ℝ), (40387251308847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5411870187/10000000000 : ℝ)|^2117 ≤ (44492248206119/100000000000000 : ℝ)^1605
        have hw : |(5411870187/10000000000 : ℝ)|=(5411870187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1193876679/5000000000 : ℝ)|^2117 ≤ (945031279237/6250000000000 : ℝ)^1605
        have hw : |(-1193876679/5000000000 : ℝ)|=(1193876679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(157153767/312500000 : ℝ)|^2117 ≤ (40387251308847/100000000000000 : ℝ)^1605
        have hw : |(157153767/312500000 : ℝ)|=(157153767/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s1_2 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2705934977/5000000000 : ℝ)*x 0 + (1005784149/2000000000 : ℝ)*x 1 + (-1193876703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2705934977/5000000000 : ℝ)^2117 ≤ (22246122839753/50000000000000 : ℝ)^1605 := by
    have hnat : (2705934977 : ℕ)^2117*50000000000000^1605 ≤ 22246122839753^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705934977 5000000000 22246122839753 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005784149/2000000000 : ℝ)^2117 ≤ (20193626719011/50000000000000 : ℝ)^1605 := by
    have hnat : (1005784149 : ℕ)^2117*50000000000000^1605 ≤ 20193626719011^1605*2000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005784149 2000000000 20193626719011 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1193876703/5000000000 : ℝ)^2117 ≤ (7560250434359/50000000000000 : ℝ)^1605 := by
    have hnat : (1193876703 : ℕ)^2117*50000000000000^1605 ≤ 7560250434359^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193876703 5000000000 7560250434359 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2705934977/5000000000 : ℝ), (1005784149/2000000000 : ℝ), (-1193876703/5000000000 : ℝ)] ![(22246122839753/50000000000000 : ℝ), (20193626719011/50000000000000 : ℝ), (7560250434359/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2705934977/5000000000 : ℝ)|^2117 ≤ (22246122839753/50000000000000 : ℝ)^1605
        have hw : |(2705934977/5000000000 : ℝ)|=(2705934977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1005784149/2000000000 : ℝ)|^2117 ≤ (20193626719011/50000000000000 : ℝ)^1605
        have hw : |(1005784149/2000000000 : ℝ)|=(1005784149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1193876703/5000000000 : ℝ)|^2117 ≤ (7560250434359/50000000000000 : ℝ)^1605
        have hw : |(-1193876703/5000000000 : ℝ)|=(1193876703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s1_3 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (53824751/125000000 : ℝ)*x 0 + (1850681891/5000000000 : ℝ)*x 1 + (500483633/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53824751/125000000 : ℝ)^2117 ≤ (8227726719073/25000000000000 : ℝ)^1605 := by
    have hnat : (53824751 : ℕ)^2117*25000000000000^1605 ≤ 8227726719073^1605*125000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53824751 125000000 8227726719073 25000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1850681891/5000000000 : ℝ)^2117 ≤ (13478384322959/50000000000000 : ℝ)^1605 := by
    have hnat : (1850681891 : ℕ)^2117*50000000000000^1605 ≤ 13478384322959^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1850681891 5000000000 13478384322959 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (500483633/1000000000 : ℝ)^2117 ≤ (4013232445497/10000000000000 : ℝ)^1605 := by
    have hnat : (500483633 : ℕ)^2117*10000000000000^1605 ≤ 4013232445497^1605*1000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500483633 1000000000 4013232445497 10000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53824751/125000000 : ℝ), (1850681891/5000000000 : ℝ), (500483633/1000000000 : ℝ)] ![(8227726719073/25000000000000 : ℝ), (13478384322959/50000000000000 : ℝ), (4013232445497/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53824751/125000000 : ℝ)|^2117 ≤ (8227726719073/25000000000000 : ℝ)^1605
        have hw : |(53824751/125000000 : ℝ)|=(53824751/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1850681891/5000000000 : ℝ)|^2117 ≤ (13478384322959/50000000000000 : ℝ)^1605
        have hw : |(1850681891/5000000000 : ℝ)|=(1850681891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(500483633/1000000000 : ℝ)|^2117 ≤ (4013232445497/10000000000000 : ℝ)^1605
        have hw : |(500483633/1000000000 : ℝ)|=(500483633/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s1_4 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2046067617/10000000000 : ℝ)*x 0 + (1259299919/2500000000 : ℝ)*x 1 + (5658972517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2046067617/10000000000 : ℝ)^2117 ≤ (6166962587703/50000000000000 : ℝ)^1605 := by
    have hnat : (2046067617 : ℕ)^2117*50000000000000^1605 ≤ 6166962587703^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046067617 10000000000 6166962587703 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1259299919/2500000000 : ℝ)^2117 ≤ (40474974441871/100000000000000 : ℝ)^1605 := by
    have hnat : (1259299919 : ℕ)^2117*100000000000000^1605 ≤ 40474974441871^1605*2500000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1259299919 2500000000 40474974441871 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5658972517/10000000000 : ℝ)^2117 ≤ (47191100368307/100000000000000 : ℝ)^1605 := by
    have hnat : (5658972517 : ℕ)^2117*100000000000000^1605 ≤ 47191100368307^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5658972517 10000000000 47191100368307 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2046067617/10000000000 : ℝ), (1259299919/2500000000 : ℝ), (5658972517/10000000000 : ℝ)] ![(6166962587703/50000000000000 : ℝ), (40474974441871/100000000000000 : ℝ), (47191100368307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2046067617/10000000000 : ℝ)|^2117 ≤ (6166962587703/50000000000000 : ℝ)^1605
        have hw : |(-2046067617/10000000000 : ℝ)|=(2046067617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1259299919/2500000000 : ℝ)|^2117 ≤ (40474974441871/100000000000000 : ℝ)^1605
        have hw : |(1259299919/2500000000 : ℝ)|=(1259299919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5658972517/10000000000 : ℝ)|^2117 ≤ (47191100368307/100000000000000 : ℝ)^1605
        have hw : |(5658972517/10000000000 : ℝ)|=(5658972517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s1_5 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2623561897/5000000000 : ℝ)*x 0 + (-219712649/1250000000 : ℝ)*x 1 + (565897313/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2623561897/5000000000 : ℝ)^2117 ≤ (42714500886047/100000000000000 : ℝ)^1605 := by
    have hnat : (2623561897 : ℕ)^2117*100000000000000^1605 ≤ 42714500886047^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623561897 5000000000 42714500886047 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219712649/1250000000 : ℝ)^2117 ≤ (10094391982531/100000000000000 : ℝ)^1605 := by
    have hnat : (219712649 : ℕ)^2117*100000000000000^1605 ≤ 10094391982531^1605*1250000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219712649 1250000000 10094391982531 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565897313/1000000000 : ℝ)^2117 ≤ (47191107110929/100000000000000 : ℝ)^1605 := by
    have hnat : (565897313 : ℕ)^2117*100000000000000^1605 ≤ 47191107110929^1605*1000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565897313 1000000000 47191107110929 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2623561897/5000000000 : ℝ), (-219712649/1250000000 : ℝ), (565897313/1000000000 : ℝ)] ![(42714500886047/100000000000000 : ℝ), (10094391982531/100000000000000 : ℝ), (47191107110929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2623561897/5000000000 : ℝ)|^2117 ≤ (42714500886047/100000000000000 : ℝ)^1605
        have hw : |(2623561897/5000000000 : ℝ)|=(2623561897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-219712649/1250000000 : ℝ)|^2117 ≤ (10094391982531/100000000000000 : ℝ)^1605
        have hw : |(-219712649/1250000000 : ℝ)|=(219712649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(565897313/1000000000 : ℝ)|^2117 ≤ (47191107110929/100000000000000 : ℝ)^1605
        have hw : |(565897313/1000000000 : ℝ)|=(565897313/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s1_6 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (524712371/1000000000 : ℝ)*x 0 + (226358911/400000000 : ℝ)*x 1 + (-439425457/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524712371/1000000000 : ℝ)^2117 ≤ (5339312498013/12500000000000 : ℝ)^1605 := by
    have hnat : (524712371 : ℕ)^2117*12500000000000^1605 ≤ 5339312498013^1605*1000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524712371 1000000000 5339312498013 12500000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226358911/400000000 : ℝ)^2117 ≤ (11797775801537/25000000000000 : ℝ)^1605 := by
    have hnat : (226358911 : ℕ)^2117*25000000000000^1605 ≤ 11797775801537^1605*400000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226358911 400000000 11797775801537 25000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (439425457/2500000000 : ℝ)^2117 ≤ (2523599200053/25000000000000 : ℝ)^1605 := by
    have hnat : (439425457 : ℕ)^2117*25000000000000^1605 ≤ 2523599200053^1605*2500000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439425457 2500000000 2523599200053 25000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524712371/1000000000 : ℝ), (226358911/400000000 : ℝ), (-439425457/2500000000 : ℝ)] ![(5339312498013/12500000000000 : ℝ), (11797775801537/25000000000000 : ℝ), (2523599200053/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524712371/1000000000 : ℝ)|^2117 ≤ (5339312498013/12500000000000 : ℝ)^1605
        have hw : |(524712371/1000000000 : ℝ)|=(524712371/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(226358911/400000000 : ℝ)|^2117 ≤ (11797775801537/25000000000000 : ℝ)^1605
        have hw : |(226358911/400000000 : ℝ)|=(226358911/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-439425457/2500000000 : ℝ)|^2117 ≤ (2523599200053/25000000000000 : ℝ)^1605
        have hw : |(-439425457/2500000000 : ℝ)|=(439425457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s1_7 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (430728281/1000000000 : ℝ)*x 0 + (2493967547/5000000000 : ℝ)*x 1 + (929645627/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430728281/1000000000 : ℝ)^2117 ≤ (16462020317363/50000000000000 : ℝ)^1605 := by
    have hnat : (430728281 : ℕ)^2117*50000000000000^1605 ≤ 16462020317363^1605*1000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430728281 1000000000 16462020317363 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2493967547/5000000000 : ℝ)^2117 ≤ (799073229659/2000000000000 : ℝ)^1605 := by
    have hnat : (2493967547 : ℕ)^2117*2000000000000^1605 ≤ 799073229659^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2493967547 5000000000 799073229659 2000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (929645627/2500000000 : ℝ)^2117 ≤ (3390287234003/12500000000000 : ℝ)^1605 := by
    have hnat : (929645627 : ℕ)^2117*12500000000000^1605 ≤ 3390287234003^1605*2500000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929645627 2500000000 3390287234003 12500000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(430728281/1000000000 : ℝ), (2493967547/5000000000 : ℝ), (929645627/2500000000 : ℝ)] ![(16462020317363/50000000000000 : ℝ), (799073229659/2000000000000 : ℝ), (3390287234003/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(430728281/1000000000 : ℝ)|^2117 ≤ (16462020317363/50000000000000 : ℝ)^1605
        have hw : |(430728281/1000000000 : ℝ)|=(430728281/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2493967547/5000000000 : ℝ)|^2117 ≤ (799073229659/2000000000000 : ℝ)^1605
        have hw : |(2493967547/5000000000 : ℝ)|=(2493967547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(929645627/2500000000 : ℝ)|^2117 ≤ (3390287234003/12500000000000 : ℝ)^1605
        have hw : |(929645627/2500000000 : ℝ)|=(929645627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1274_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152075211/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27313/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (949/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (3181/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (993/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27313/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (949/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27313/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (949/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27313/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (949/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27313/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (949/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27313/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (949/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27313/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (949/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (949/100000 : ℝ) ^ (8467/2048 : ℝ) ≤ (86793564623/20000000000000000000 : ℝ) := by
    have hpowers : (949/100000 : ℝ)^8467 ≤ (86793564623/20000000000000000000 : ℝ)^2048 := by
      have hnat : (949 : ℕ)^8467*20000000000000000000^2048 ≤ 86793564623^2048*100000^8467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        949 100000 86793564623 20000000000000000000 8467 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (949/100000 : ℝ)) (X := (86793564623/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27313/100000 : ℝ) ^ (8467/2048 : ℝ) ≤ (1870056770921711/400000000000000000 : ℝ) := by
    have hpowers : (27313/100000 : ℝ)^8467 ≤ (1870056770921711/400000000000000000 : ℝ)^2048 := by
      have hnat : (27313 : ℕ)^8467*400000000000000000^2048 ≤ 1870056770921711^2048*100000^8467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27313 100000 1870056770921711 400000000000000000 8467 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27313/100000 : ℝ)) (X := (1870056770921711/400000000000000000 : ℝ)) (by norm_num) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000086793564623/10000000000000000000 : ℝ) ≤ (10000000020993649/10000000000000000 : ℝ) ^ (8467/2048 : ℝ) := by
    have hpowers : (10000000086793564623/10000000000000000000 : ℝ)^2048 ≤ (10000000020993649/10000000000000000 : ℝ)^8467 := by
      have hnat : (10000000086793564623 : ℕ)^2048*10000000000000000^8467 ≤ 10000000020993649^8467*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000086793564623 10000000000000000000 10000000020993649 10000000000000000 2048 8467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000020993649/10000000000000000 : ℝ)) (X := (10000000086793564623/10000000000000000000 : ℝ)) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20093502925339650173/20000000000000000000 : ℝ) ≤ (2502822067435713/2500000000000000 : ℝ) ^ (8467/2048 : ℝ) := by
    have hpowers : (20093502925339650173/20000000000000000000 : ℝ)^2048 ≤ (2502822067435713/2500000000000000 : ℝ)^8467 := by
      have hnat : (20093502925339650173 : ℕ)^2048*2500000000000000^8467 ≤ 2502822067435713^8467*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20093502925339650173 20000000000000000000 2502822067435713 2500000000000000 2048 8467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502822067435713/2500000000000000 : ℝ)) (X := (20093502925339650173/20000000000000000000 : ℝ)) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (201870056770921711/200000000000000000 : ℝ) ≤ (2004515303698411/2000000000000000 : ℝ) ^ (8467/2048 : ℝ) := by
    have hpowers : (201870056770921711/200000000000000000 : ℝ)^2048 ≤ (2004515303698411/2000000000000000 : ℝ)^8467 := by
      have hnat : (201870056770921711 : ℕ)^2048*2000000000000000^8467 ≤ 2004515303698411^8467*200000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        201870056770921711 200000000000000000 2004515303698411 2000000000000000 2048 8467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2004515303698411/2000000000000000 : ℝ)) (X := (201870056770921711/200000000000000000 : ℝ)) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(86793564623/20000000000000000000 : ℝ) ≤ ((10139175979128868267/10140000000000000000 : ℝ)+2*(11288248749203/2636400000000000 : ℝ)*(949/100000 : ℝ))^(8467/2048 : ℝ) := by
    rw [show (10139175979128868267/10140000000000000000 : ℝ)+2*(11288248749203/2636400000000000 : ℝ)*(949/100000 : ℝ)=(10000000020993649/10000000000000000 : ℝ) by norm_num, show 1+2*(86793564623/20000000000000000000 : ℝ)=(10000000086793564623/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1870056770921711/400000000000000000 : ℝ)+(86793564623/20000000000000000000 : ℝ) ≤ ((10139175979128868267/10140000000000000000 : ℝ)+(11288248749203/2636400000000000 : ℝ)*((27313/100000 : ℝ)+(949/100000 : ℝ)))^(8467/2048 : ℝ) := by
    rw [show (10139175979128868267/10140000000000000000 : ℝ)+(11288248749203/2636400000000000 : ℝ)*((27313/100000 : ℝ)+(949/100000 : ℝ))=(2502822067435713/2500000000000000 : ℝ) by norm_num, show 1+(1870056770921711/400000000000000000 : ℝ)+(86793564623/20000000000000000000 : ℝ)=(20093502925339650173/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1870056770921711/400000000000000000 : ℝ) ≤ ((10139175979128868267/10140000000000000000 : ℝ)+2*(11288248749203/2636400000000000 : ℝ)*(27313/100000 : ℝ))^(8467/2048 : ℝ) := by
    rw [show (10139175979128868267/10140000000000000000 : ℝ)+2*(11288248749203/2636400000000000 : ℝ)*(27313/100000 : ℝ)=(2004515303698411/2000000000000000 : ℝ) by norm_num, show 1+2*(1870056770921711/400000000000000000 : ℝ)=(201870056770921711/200000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10139175979128868267/10140000000000000000 : ℝ)*(X 1 0+X 2 0)+(11288248749203/2636400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8467/2048 : ℝ)) (lo := (949/100000 : ℝ)) (hi := (27313/100000 : ℝ)) (c := (10139175979128868267/10140000000000000000 : ℝ)) (alpha := (11288248749203/2636400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10139175979128868267/10140000000000000000 : ℝ)*(X 0 1+X 2 1)+(11288248749203/2636400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8467/2048 : ℝ)) (lo := (949/100000 : ℝ)) (hi := (27313/100000 : ℝ)) (c := (10139175979128868267/10140000000000000000 : ℝ)) (alpha := (11288248749203/2636400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10139175979128868267/10140000000000000000 : ℝ)*(X 0 2+X 1 2)+(11288248749203/2636400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8467/2048 : ℝ)) (lo := (949/100000 : ℝ)) (hi := (27313/100000 : ℝ)) (c := (10139175979128868267/10140000000000000000 : ℝ)) (alpha := (11288248749203/2636400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-409085831/2000000000 : ℝ)*X 0 0+(1133481419/2000000000 : ℝ)*X 0 1+(5028920747/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5411870187/10000000000 : ℝ)*X 1 0+(-1193876679/5000000000 : ℝ)*X 1 1+(157153767/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2705934977/5000000000 : ℝ)*X 2 0+(1005784149/2000000000 : ℝ)*X 2 1+(-1193876703/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((53824751/125000000 : ℝ)*X 0 0+(1850681891/5000000000 : ℝ)*X 0 1+(500483633/1000000000 : ℝ)*X 0 2+(53824751/125000000 : ℝ)*X 1 0+(1850681891/5000000000 : ℝ)*X 1 1+(500483633/1000000000 : ℝ)*X 1 2+(53824751/125000000 : ℝ)*X 2 0+(1850681891/5000000000 : ℝ)*X 2 1+(500483633/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2046067617/10000000000 : ℝ)*X 0 0+(1259299919/2500000000 : ℝ)*X 0 1+(5658972517/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2623561897/5000000000 : ℝ)*X 1 0+(-219712649/1250000000 : ℝ)*X 1 1+(565897313/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((524712371/1000000000 : ℝ)*X 2 0+(226358911/400000000 : ℝ)*X 2 1+(-439425457/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((430728281/1000000000 : ℝ)*X 0 0+(2493967547/5000000000 : ℝ)*X 0 1+(929645627/2500000000 : ℝ)*X 0 2+(430728281/1000000000 : ℝ)*X 1 0+(2493967547/5000000000 : ℝ)*X 1 1+(929645627/2500000000 : ℝ)*X 1 2+(430728281/1000000000 : ℝ)*X 2 0+(2493967547/5000000000 : ℝ)*X 2 1+(929645627/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (503388814099793304616727961/84500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (106031/156250000000 : ℝ)*(base1) + (123959381/10000000000000 : ℝ)*(base19) + (1172162707/100000000000000 : ℝ)*(base23) + (35932523/25000000000000 : ℝ)*(upper3) + (27107591/25000000000000 : ℝ)*(upper5) + (583351403144839/50000000000000 : ℝ)*(major0) + (583351403144839/50000000000000 : ℝ)*(major1) + (583351403144839/50000000000000 : ℝ)*(major2) + (3915527512553/250000000000 : ℝ)*(sp0) + (313243230078733/20000000000000 : ℝ)*(sp1) + (3059016050439/195312500000 : ℝ)*(sp2) + (383592315156023/50000000000000 : ℝ)*(sp3) + (1290565223/20000000000000 : ℝ)*(sp4) + (3325844519/100000000000000 : ℝ)*(sp7) + (191797006004101/25000000000000 : ℝ)*(f.failure) + (62648695599499/4000000000000 : ℝ)*(f.sum) + (125865094546333/65910000000000000000000000000 : ℝ)*base66 + (7737120910122862169/6591000000000000000000000000000000 : ℝ)*base67 + (25885424982423862169/6591000000000000000000000000000000 : ℝ)*base69 + (16370626154265862169/6591000000000000000000000000000000 : ℝ)*base71 + (94869768432763/65910000000000000000000000000 : ℝ)*base74 + (25976144132568862169/6591000000000000000000000000000000 : ℝ)*base75 + (34502102559918862169/6591000000000000000000000000000000 : ℝ)*base77 + (12335929072902862169/6591000000000000000000000000000000 : ℝ)*base79 + (11207195718523/65910000000000000000000000000 : ℝ)*base82 + (23559689/2500000000000000000000 : ℝ)*base90 + (23559689/2500000000000000000000 : ℝ)*base92 + (23559689/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (429735902473677521499126537/169000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (358486641/100000000000000 : ℝ)*(base19) + (182581511/50000000000000 : ℝ)*(base23) + (17356749/50000000000000 : ℝ)*(upper2) + (92618887/100000000000000 : ℝ)*(upper3) + (10432903/20000000000000 : ℝ)*(upper5) + (1198053427971063/100000000000000 : ℝ)*(major0) + (1198053427971063/100000000000000 : ℝ)*(major1) + (1198053427971063/100000000000000 : ℝ)*(major2) + (160294293/6250000000000 : ℝ)*(sp1) + (298059349/20000000000000 : ℝ)*(sp2) + (160830353875927/10000000000000 : ℝ)*(sp4) + (1608300615563941/100000000000000 : ℝ)*(sp5) + (1608301683299503/100000000000000 : ℝ)*(sp6) + (9847540405279/1250000000000 : ℝ)*(sp7) + (9847540405279/1250000000000 : ℝ)*(f.failure) + (160830353875927/10000000000000 : ℝ)*(f.sum) + (183458701159137/43940000000000000000000000000 : ℝ)*base66 + (5193186040744633891/4394000000000000000000000000000000 : ℝ)*base67 + (16978480420044633891/4394000000000000000000000000000000 : ℝ)*base69 + (12309174965204633891/4394000000000000000000000000000000 : ℝ)*base71 + (40849080105497/43940000000000000000000000000 : ℝ)*base74 + (20645673221316633891/4394000000000000000000000000000000 : ℝ)*base75 + (5474663659504633891/4394000000000000000000000000000000 : ℝ)*base77 + (11790736044724633891/4394000000000000000000000000000000 : ℝ)*base79 + (113636459143377/43940000000000000000000000000 : ℝ)*base82 + (688869/125000000000000000000 : ℝ)*base89 + (688869/125000000000000000000 : ℝ)*base91 + (688869/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1274_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152075211/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27313/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (949/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3181/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (993/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1274_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1274_s2_0 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2091845829/10000000000 : ℝ)*x 0 + (685907811/1250000000 : ℝ)*x 1 + (2589717353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2091845829/10000000000 : ℝ)^2117 ≤ (12699204667079/100000000000000 : ℝ)^1605 := by
    have hnat : (2091845829 : ℕ)^2117*100000000000000^1605 ≤ 12699204667079^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091845829 10000000000 12699204667079 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (685907811/1250000000 : ℝ)^2117 ≤ (45311600560401/100000000000000 : ℝ)^1605 := by
    have hnat : (685907811 : ℕ)^2117*100000000000000^1605 ≤ 45311600560401^1605*1250000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685907811 1250000000 45311600560401 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2589717353/5000000000 : ℝ)^2117 ≤ (41989194760379/100000000000000 : ℝ)^1605 := by
    have hnat : (2589717353 : ℕ)^2117*100000000000000^1605 ≤ 41989194760379^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589717353 5000000000 41989194760379 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2091845829/10000000000 : ℝ), (685907811/1250000000 : ℝ), (2589717353/5000000000 : ℝ)] ![(12699204667079/100000000000000 : ℝ), (45311600560401/100000000000000 : ℝ), (41989194760379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2091845829/10000000000 : ℝ)|^2117 ≤ (12699204667079/100000000000000 : ℝ)^1605
        have hw : |(-2091845829/10000000000 : ℝ)|=(2091845829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(685907811/1250000000 : ℝ)|^2117 ≤ (45311600560401/100000000000000 : ℝ)^1605
        have hw : |(685907811/1250000000 : ℝ)|=(685907811/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2589717353/5000000000 : ℝ)|^2117 ≤ (41989194760379/100000000000000 : ℝ)^1605
        have hw : |(2589717353/5000000000 : ℝ)|=(2589717353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s2_1 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5368356961/10000000000 : ℝ)*x 0 + (-1125559279/5000000000 : ℝ)*x 1 + (258971751/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368356961/10000000000 : ℝ)^2117 ≤ (44021004300637/100000000000000 : ℝ)^1605 := by
    have hnat : (5368356961 : ℕ)^2117*100000000000000^1605 ≤ 44021004300637^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368356961 10000000000 44021004300637 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125559279/5000000000 : ℝ)^2117 ≤ (1398979756767/10000000000000 : ℝ)^1605 := by
    have hnat : (1125559279 : ℕ)^2117*10000000000000^1605 ≤ 1398979756767^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125559279 5000000000 1398979756767 10000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258971751/500000000 : ℝ)^2117 ≤ (5248649764749/12500000000000 : ℝ)^1605 := by
    have hnat : (258971751 : ℕ)^2117*12500000000000^1605 ≤ 5248649764749^1605*500000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258971751 500000000 5248649764749 12500000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368356961/10000000000 : ℝ), (-1125559279/5000000000 : ℝ), (258971751/500000000 : ℝ)] ![(44021004300637/100000000000000 : ℝ), (1398979756767/10000000000000 : ℝ), (5248649764749/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368356961/10000000000 : ℝ)|^2117 ≤ (44021004300637/100000000000000 : ℝ)^1605
        have hw : |(5368356961/10000000000 : ℝ)|=(5368356961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1125559279/5000000000 : ℝ)|^2117 ≤ (1398979756767/10000000000000 : ℝ)^1605
        have hw : |(-1125559279/5000000000 : ℝ)|=(1125559279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258971751/500000000 : ℝ)|^2117 ≤ (5248649764749/12500000000000 : ℝ)^1605
        have hw : |(258971751/500000000 : ℝ)|=(258971751/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s2_2 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5368356939/10000000000 : ℝ)*x 0 + (5179434979/10000000000 : ℝ)*x 1 + (-28138983/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368356939/10000000000 : ℝ)^2117 ≤ (22010502031343/50000000000000 : ℝ)^1605 := by
    have hnat : (5368356939 : ℕ)^2117*50000000000000^1605 ≤ 22010502031343^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368356939 10000000000 22010502031343 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179434979/10000000000 : ℝ)^2117 ≤ (20994598839789/50000000000000 : ℝ)^1605 := by
    have hnat : (5179434979 : ℕ)^2117*50000000000000^1605 ≤ 20994598839789^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179434979 10000000000 20994598839789 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28138983/125000000 : ℝ)^2117 ≤ (1398979823983/10000000000000 : ℝ)^1605 := by
    have hnat : (28138983 : ℕ)^2117*10000000000000^1605 ≤ 1398979823983^1605*125000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28138983 125000000 1398979823983 10000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368356939/10000000000 : ℝ), (5179434979/10000000000 : ℝ), (-28138983/125000000 : ℝ)] ![(22010502031343/50000000000000 : ℝ), (20994598839789/50000000000000 : ℝ), (1398979823983/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368356939/10000000000 : ℝ)|^2117 ≤ (22010502031343/50000000000000 : ℝ)^1605
        have hw : |(5368356939/10000000000 : ℝ)|=(5368356939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179434979/10000000000 : ℝ)|^2117 ≤ (20994598839789/50000000000000 : ℝ)^1605
        have hw : |(5179434979/10000000000 : ℝ)|=(5179434979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-28138983/125000000 : ℝ)|^2117 ≤ (1398979823983/10000000000000 : ℝ)^1605
        have hw : |(-28138983/125000000 : ℝ)|=(28138983/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s2_3 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4338107183/10000000000 : ℝ)*x 0 + (4034832557/10000000000 : ℝ)*x 1 + (1165815851/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4338107183/10000000000 : ℝ)^2117 ≤ (2077198279489/6250000000000 : ℝ)^1605 := by
    have hnat : (4338107183 : ℕ)^2117*6250000000000^1605 ≤ 2077198279489^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4338107183 10000000000 2077198279489 6250000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4034832557/10000000000 : ℝ)^2117 ≤ (1887828966897/6250000000000 : ℝ)^1605 := by
    have hnat : (4034832557 : ℕ)^2117*6250000000000^1605 ≤ 1887828966897^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4034832557 10000000000 1887828966897 6250000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1165815851/2500000000 : ℝ)^2117 ≤ (36559564039649/100000000000000 : ℝ)^1605 := by
    have hnat : (1165815851 : ℕ)^2117*100000000000000^1605 ≤ 36559564039649^1605*2500000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1165815851 2500000000 36559564039649 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4338107183/10000000000 : ℝ), (4034832557/10000000000 : ℝ), (1165815851/2500000000 : ℝ)] ![(2077198279489/6250000000000 : ℝ), (1887828966897/6250000000000 : ℝ), (36559564039649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4338107183/10000000000 : ℝ)|^2117 ≤ (2077198279489/6250000000000 : ℝ)^1605
        have hw : |(4338107183/10000000000 : ℝ)|=(4338107183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4034832557/10000000000 : ℝ)|^2117 ≤ (1887828966897/6250000000000 : ℝ)^1605
        have hw : |(4034832557/10000000000 : ℝ)|=(4034832557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1165815851/2500000000 : ℝ)|^2117 ≤ (36559564039649/100000000000000 : ℝ)^1605
        have hw : |(1165815851/2500000000 : ℝ)|=(1165815851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s2_4 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2091917633/10000000000 : ℝ)*x 0 + (5181369029/10000000000 : ℝ)*x 1 + (109706209/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2091917633/10000000000 : ℝ)^2117 ≤ (2539955927019/20000000000000 : ℝ)^1605 := by
    have hnat : (2091917633 : ℕ)^2117*20000000000000^1605 ≤ 2539955927019^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091917633 10000000000 2539955927019 20000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181369029/10000000000 : ℝ)^2117 ≤ (2625617486043/6250000000000 : ℝ)^1605 := by
    have hnat : (5181369029 : ℕ)^2117*6250000000000^1605 ≤ 2625617486043^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181369029 10000000000 2625617486043 6250000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109706209/200000000 : ℝ)^2117 ≤ (45290340567671/100000000000000 : ℝ)^1605 := by
    have hnat : (109706209 : ℕ)^2117*100000000000000^1605 ≤ 45290340567671^1605*200000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109706209 200000000 45290340567671 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2091917633/10000000000 : ℝ), (5181369029/10000000000 : ℝ), (109706209/200000000 : ℝ)] ![(2539955927019/20000000000000 : ℝ), (2625617486043/6250000000000 : ℝ), (45290340567671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2091917633/10000000000 : ℝ)|^2117 ≤ (2539955927019/20000000000000 : ℝ)^1605
        have hw : |(-2091917633/10000000000 : ℝ)|=(2091917633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181369029/10000000000 : ℝ)|^2117 ≤ (2625617486043/6250000000000 : ℝ)^1605
        have hw : |(5181369029/10000000000 : ℝ)|=(5181369029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(109706209/200000000 : ℝ)|^2117 ≤ (45290340567671/100000000000000 : ℝ)^1605
        have hw : |(109706209/200000000 : ℝ)|=(109706209/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s2_5 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2644793277/5000000000 : ℝ)*x 0 + (-1945242829/10000000000 : ℝ)*x 1 + (548531049/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644793277/5000000000 : ℝ)^2117 ≤ (43171028716289/100000000000000 : ℝ)^1605 := by
    have hnat : (2644793277 : ℕ)^2117*100000000000000^1605 ≤ 43171028716289^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644793277 5000000000 43171028716289 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1945242829/10000000000 : ℝ)^2117 ≤ (5769315134077/50000000000000 : ℝ)^1605 := by
    have hnat : (1945242829 : ℕ)^2117*50000000000000^1605 ≤ 5769315134077^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945242829 10000000000 5769315134077 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548531049/1000000000 : ℝ)^2117 ≤ (22645170501647/50000000000000 : ℝ)^1605 := by
    have hnat : (548531049 : ℕ)^2117*50000000000000^1605 ≤ 22645170501647^1605*1000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548531049 1000000000 22645170501647 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644793277/5000000000 : ℝ), (-1945242829/10000000000 : ℝ), (548531049/1000000000 : ℝ)] ![(43171028716289/100000000000000 : ℝ), (5769315134077/50000000000000 : ℝ), (22645170501647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644793277/5000000000 : ℝ)|^2117 ≤ (43171028716289/100000000000000 : ℝ)^1605
        have hw : |(2644793277/5000000000 : ℝ)|=(2644793277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1945242829/10000000000 : ℝ)|^2117 ≤ (5769315134077/50000000000000 : ℝ)^1605
        have hw : |(-1945242829/10000000000 : ℝ)|=(1945242829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(548531049/1000000000 : ℝ)|^2117 ≤ (22645170501647/50000000000000 : ℝ)^1605
        have hw : |(548531049/1000000000 : ℝ)|=(548531049/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s2_6 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1322396661/2500000000 : ℝ)*x 0 + (685663827/1250000000 : ℝ)*x 1 + (-1945242529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322396661/2500000000 : ℝ)^2117 ≤ (8634205937029/20000000000000 : ℝ)^1605 := by
    have hnat : (1322396661 : ℕ)^2117*20000000000000^1605 ≤ 8634205937029^1605*2500000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322396661 2500000000 8634205937029 20000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (685663827/1250000000 : ℝ)^2117 ≤ (2830646398469/6250000000000 : ℝ)^1605 := by
    have hnat : (685663827 : ℕ)^2117*6250000000000^1605 ≤ 2830646398469^1605*1250000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685663827 1250000000 2830646398469 6250000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1945242529/10000000000 : ℝ)^2117 ≤ (1442328490121/12500000000000 : ℝ)^1605 := by
    have hnat : (1945242529 : ℕ)^2117*12500000000000^1605 ≤ 1442328490121^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945242529 10000000000 1442328490121 12500000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322396661/2500000000 : ℝ), (685663827/1250000000 : ℝ), (-1945242529/10000000000 : ℝ)] ![(8634205937029/20000000000000 : ℝ), (2830646398469/6250000000000 : ℝ), (1442328490121/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322396661/2500000000 : ℝ)|^2117 ≤ (8634205937029/20000000000000 : ℝ)^1605
        have hw : |(1322396661/2500000000 : ℝ)|=(1322396661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(685663827/1250000000 : ℝ)|^2117 ≤ (2830646398469/6250000000000 : ℝ)^1605
        have hw : |(685663827/1250000000 : ℝ)|=(685663827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1945242529/10000000000 : ℝ)|^2117 ≤ (1442328490121/12500000000000 : ℝ)^1605
        have hw : |(-1945242529/10000000000 : ℝ)|=(1945242529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_s2_7 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2169126713/5000000000 : ℝ)*x 0 + (582414387/1250000000 : ℝ)*x 1 + (4038816607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169126713/5000000000 : ℝ)^2117 ≤ (33236650289657/100000000000000 : ℝ)^1605 := by
    have hnat : (2169126713 : ℕ)^2117*100000000000000^1605 ≤ 33236650289657^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169126713 5000000000 33236650289657 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (582414387/1250000000 : ℝ)^2117 ≤ (7303748126647/20000000000000 : ℝ)^1605 := by
    have hnat : (582414387 : ℕ)^2117*20000000000000^1605 ≤ 7303748126647^1605*1250000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      582414387 1250000000 7303748126647 20000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4038816607/10000000000 : ℝ)^2117 ≤ (15122304531503/50000000000000 : ℝ)^1605 := by
    have hnat : (4038816607 : ℕ)^2117*50000000000000^1605 ≤ 15122304531503^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4038816607 10000000000 15122304531503 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2169126713/5000000000 : ℝ), (582414387/1250000000 : ℝ), (4038816607/10000000000 : ℝ)] ![(33236650289657/100000000000000 : ℝ), (7303748126647/20000000000000 : ℝ), (15122304531503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2169126713/5000000000 : ℝ)|^2117 ≤ (33236650289657/100000000000000 : ℝ)^1605
        have hw : |(2169126713/5000000000 : ℝ)|=(2169126713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(582414387/1250000000 : ℝ)|^2117 ≤ (7303748126647/20000000000000 : ℝ)^1605
        have hw : |(582414387/1250000000 : ℝ)|=(582414387/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4038816607/10000000000 : ℝ)|^2117 ≤ (15122304531503/50000000000000 : ℝ)^1605
        have hw : |(4038816607/10000000000 : ℝ)|=(4038816607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1274_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152075211/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (993/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3181/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9631/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16139/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (993/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3181/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (993/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3181/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (993/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3181/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (993/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3181/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (993/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3181/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (993/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3181/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3181/50000 : ℝ) ^ (8467/2048 : ℝ) ≤ (1131681963742469/100000000000000000000 : ℝ) := by
    have hpowers : (3181/50000 : ℝ)^8467 ≤ (1131681963742469/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3181 : ℕ)^8467*100000000000000000000^2048 ≤ 1131681963742469^2048*50000^8467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3181 50000 1131681963742469 100000000000000000000 8467 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3181/50000 : ℝ)) (X := (1131681963742469/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (993/5000 : ℝ) ^ (8467/2048 : ℝ) ≤ (15284863007261/12207031250000000 : ℝ) := by
    have hpowers : (993/5000 : ℝ)^8467 ≤ (15284863007261/12207031250000000 : ℝ)^2048 := by
      have hnat : (993 : ℕ)^8467*12207031250000000^2048 ≤ 15284863007261^2048*5000^8467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        993 5000 15284863007261 12207031250000000 8467 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (993/5000 : ℝ)) (X := (15284863007261/12207031250000000 : ℝ)) (by norm_num) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001131681963742469/50000000000000000000 : ℝ) ≤ (10000054745831521/10000000000000000 : ℝ) ^ (8467/2048 : ℝ) := by
    have hpowers : (50001131681963742469/50000000000000000000 : ℝ)^2048 ≤ (10000054745831521/10000000000000000 : ℝ)^8467 := by
      have hnat : (50001131681963742469 : ℕ)^2048*10000000000000000^8467 ≤ 10000054745831521^8467*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001131681963742469 50000000000000000000 10000054745831521 10000000000000000 2048 8467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000054745831521/10000000000000000 : ℝ)) (X := (50001131681963742469/50000000000000000000 : ℝ)) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100126345279719224581/100000000000000000000 : ℝ) ≤ (1000305458013973/1000000000000000 : ℝ) ^ (8467/2048 : ℝ) := by
    have hpowers : (100126345279719224581/100000000000000000000 : ℝ)^2048 ≤ (1000305458013973/1000000000000000 : ℝ)^8467 := by
      have hnat : (100126345279719224581 : ℕ)^2048*1000000000000000^8467 ≤ 1000305458013973^8467*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100126345279719224581 100000000000000000000 1000305458013973 1000000000000000 2048 8467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000305458013973/1000000000000000 : ℝ)) (X := (100126345279719224581/100000000000000000000 : ℝ)) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6118800488007261/6103515625000000 : ℝ) ≤ (10006054414447939/10000000000000000 : ℝ) ^ (8467/2048 : ℝ) := by
    have hpowers : (6118800488007261/6103515625000000 : ℝ)^2048 ≤ (10006054414447939/10000000000000000 : ℝ)^8467 := by
      have hnat : (6118800488007261 : ℕ)^2048*10000000000000000^8467 ≤ 10006054414447939^8467*6103515625000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6118800488007261 6103515625000000 10006054414447939 10000000000000000 2048 8467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006054414447939/10000000000000000 : ℝ)) (X := (6118800488007261/6103515625000000 : ℝ)) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1131681963742469/100000000000000000000 : ℝ) ≤ ((67471284533748109571/67490000000000000000 : ℝ)+2*(2999834308209/1349800000000000 : ℝ)*(3181/50000 : ℝ))^(8467/2048 : ℝ) := by
    rw [show (67471284533748109571/67490000000000000000 : ℝ)+2*(2999834308209/1349800000000000 : ℝ)*(3181/50000 : ℝ)=(10000054745831521/10000000000000000 : ℝ) by norm_num, show 1+2*(1131681963742469/100000000000000000000 : ℝ)=(50001131681963742469/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15284863007261/12207031250000000 : ℝ)+(1131681963742469/100000000000000000000 : ℝ) ≤ ((67471284533748109571/67490000000000000000 : ℝ)+(2999834308209/1349800000000000 : ℝ)*((993/5000 : ℝ)+(3181/50000 : ℝ)))^(8467/2048 : ℝ) := by
    rw [show (67471284533748109571/67490000000000000000 : ℝ)+(2999834308209/1349800000000000 : ℝ)*((993/5000 : ℝ)+(3181/50000 : ℝ))=(1000305458013973/1000000000000000 : ℝ) by norm_num, show 1+(15284863007261/12207031250000000 : ℝ)+(1131681963742469/100000000000000000000 : ℝ)=(100126345279719224581/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15284863007261/12207031250000000 : ℝ) ≤ ((67471284533748109571/67490000000000000000 : ℝ)+2*(2999834308209/1349800000000000 : ℝ)*(993/5000 : ℝ))^(8467/2048 : ℝ) := by
    rw [show (67471284533748109571/67490000000000000000 : ℝ)+2*(2999834308209/1349800000000000 : ℝ)*(993/5000 : ℝ)=(10006054414447939/10000000000000000 : ℝ) by norm_num, show 1+2*(15284863007261/12207031250000000 : ℝ)=(6118800488007261/6103515625000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (67471284533748109571/67490000000000000000 : ℝ)*(X 1 0+X 2 0)+(2999834308209/1349800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8467/2048 : ℝ)) (lo := (3181/50000 : ℝ)) (hi := (993/5000 : ℝ)) (c := (67471284533748109571/67490000000000000000 : ℝ)) (alpha := (2999834308209/1349800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (67471284533748109571/67490000000000000000 : ℝ)*(X 0 1+X 2 1)+(2999834308209/1349800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8467/2048 : ℝ)) (lo := (3181/50000 : ℝ)) (hi := (993/5000 : ℝ)) (c := (67471284533748109571/67490000000000000000 : ℝ)) (alpha := (2999834308209/1349800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (67471284533748109571/67490000000000000000 : ℝ)*(X 0 2+X 1 2)+(2999834308209/1349800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8467/2048 : ℝ)) (lo := (3181/50000 : ℝ)) (hi := (993/5000 : ℝ)) (c := (67471284533748109571/67490000000000000000 : ℝ)) (alpha := (2999834308209/1349800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2091845829/10000000000 : ℝ)*X 0 0+(685907811/1250000000 : ℝ)*X 0 1+(2589717353/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5368356961/10000000000 : ℝ)*X 1 0+(-1125559279/5000000000 : ℝ)*X 1 1+(258971751/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5368356939/10000000000 : ℝ)*X 2 0+(5179434979/10000000000 : ℝ)*X 2 1+(-28138983/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4338107183/10000000000 : ℝ)*X 0 0+(4034832557/10000000000 : ℝ)*X 0 1+(1165815851/2500000000 : ℝ)*X 0 2+(4338107183/10000000000 : ℝ)*X 1 0+(4034832557/10000000000 : ℝ)*X 1 1+(1165815851/2500000000 : ℝ)*X 1 2+(4338107183/10000000000 : ℝ)*X 2 0+(4034832557/10000000000 : ℝ)*X 2 1+(1165815851/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2091917633/10000000000 : ℝ)*X 0 0+(5181369029/10000000000 : ℝ)*X 0 1+(109706209/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644793277/5000000000 : ℝ)*X 1 0+(-1945242829/10000000000 : ℝ)*X 1 1+(548531049/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1322396661/2500000000 : ℝ)*X 2 0+(685663827/1250000000 : ℝ)*X 2 1+(-1945242529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2169126713/5000000000 : ℝ)*X 0 0+(582414387/1250000000 : ℝ)*X 0 1+(4038816607/10000000000 : ℝ)*X 0 2+(2169126713/5000000000 : ℝ)*X 1 0+(582414387/1250000000 : ℝ)*X 1 1+(4038816607/10000000000 : ℝ)*X 1 2+(2169126713/5000000000 : ℝ)*X 2 0+(582414387/1250000000 : ℝ)*X 2 1+(4038816607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (259217693378324394126009/33745000000000000000000000000 : ℝ) := by norm_num
    linear_combination (679148499/50000000000000 : ℝ)*(base19) + (647548137/50000000000000 : ℝ)*(base23) + (26781471/100000000000000 : ℝ)*(lower2) + (103404079/50000000000000 : ℝ)*(upper3) + (103304827/100000000000000 : ℝ)*(upper5) + (604986121525603/25000000000000 : ℝ)*(major0) + (604986121525603/25000000000000 : ℝ)*(major1) + (604986121525603/25000000000000 : ℝ)*(major2) + (1624294687829077/50000000000000 : ℝ)*(sp0) + (1624302998834559/50000000000000 : ℝ)*(sp1) + (1624303030434921/50000000000000 : ℝ)*(sp2) + (318254523439637/20000000000000 : ℝ)*(sp3) + (17980307961/100000000000000 : ℝ)*(sp4) + (8742985107/100000000000000 : ℝ)*(sp7) + (1591281360183293/100000000000000 : ℝ)*(f.failure) + (812151838991529/25000000000000 : ℝ)*(f.sum) + (12302700827461/8436250000000000000000000000 : ℝ)*base65 + (8641989780436696313/1687250000000000000000000000000000 : ℝ)*base67 + (564908863880446313/1687250000000000000000000000000000 : ℝ)*base69 + (10002069566126553687/1687250000000000000000000000000000 : ℝ)*base72 + (177360173648669/33745000000000000000000000000 : ℝ)*base73 + (1174185580698053687/1687250000000000000000000000000000 : ℝ)*base76 + (15547222157816553687/1687250000000000000000000000000000 : ℝ)*base78 + (3482486763323446313/1687250000000000000000000000000000 : ℝ)*base79 + (33719643040349/33745000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (81649823/10000000000000000000000 : ℝ)*base89 + (81649823/10000000000000000000000 : ℝ)*base91 + (81649823/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (931928540907409201571236449/99250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2272980541/100000000000000 : ℝ)*(base19) + (2443581127/100000000000000 : ℝ)*(base23) + (17274971/100000000000000 : ℝ)*(upper2) + (294535263/100000000000000 : ℝ)*(upper3) + (182513801/100000000000000 : ℝ)*(upper5) + (1225428656135053/50000000000000 : ℝ)*(major0) + (1225428656135053/50000000000000 : ℝ)*(major1) + (1225428656135053/50000000000000 : ℝ)*(major2) + (24349951959/100000000000000 : ℝ)*(sp1) + (1194157367/4000000000000 : ℝ)*(sp2) + (411263202984857/12500000000000 : ℝ)*(sp4) + (822519750236589/25000000000000 : ℝ)*(sp5) + (1645036663181777/50000000000000 : ℝ)*(sp6) + (805804343835533/50000000000000 : ℝ)*(sp7) + (805804343835533/50000000000000 : ℝ)*(f.failure) + (411263202984857/12500000000000 : ℝ)*(f.sum) + (1592478026417/33745000000000000000000000000 : ℝ)*base65 + (49229362694101742263/3374500000000000000000000000000000 : ℝ)*base67 + (57394049462402742263/3374500000000000000000000000000000 : ℝ)*base69 + (37003067386366242263/3374500000000000000000000000000000 : ℝ)*base71 + (33734211606973/33745000000000000000000000000 : ℝ)*base74 + (57713164386612742263/3374500000000000000000000000000000 : ℝ)*base75 + (16583531637755242263/3374500000000000000000000000000000 : ℝ)*base77 + (66561315160109242263/3374500000000000000000000000000000 : ℝ)*base79 + (157866290850057/33745000000000000000000000000 : ℝ)*base81 + (69727537/5000000000000000000000 : ℝ)*base90 + (69727537/5000000000000000000000 : ℝ)*base92 + (69727537/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1274_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152075211/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (993/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3181/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9631/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16139/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1274_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1274_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152075211/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9631/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16139/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1274_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1274_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1274_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152075211/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9631/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16139/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1274_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
