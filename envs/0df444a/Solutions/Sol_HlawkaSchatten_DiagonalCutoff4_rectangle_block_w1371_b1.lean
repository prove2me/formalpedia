-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1371_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:20:39.321161+00:00
-- url     : https://prove2.me/submissions/bf238c46-15bf-49e5-a347-7be1bd0723bf

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
theorem support_rectangle_w1371_s3_0 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1008847243/5000000000 : ℝ)*x 0 + (2711805299/5000000000 : ℝ)*x 1 + (2617016603/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1008847243/5000000000 : ℝ)^4331 ≤ (96027705609/781250000000 : ℝ)^3307 := by
    have hnat : (1008847243 : ℕ)^4331*781250000000^3307 ≤ 96027705609^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008847243 5000000000 96027705609 781250000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711805299/5000000000 : ℝ)^4331 ≤ (11218943270363/25000000000000 : ℝ)^3307 := by
    have hnat : (2711805299 : ℕ)^4331*25000000000000^3307 ≤ 11218943270363^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711805299 5000000000 11218943270363 25000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2617016603/5000000000 : ℝ)^4331 ≤ (8566536118363/20000000000000 : ℝ)^3307 := by
    have hnat : (2617016603 : ℕ)^4331*20000000000000^3307 ≤ 8566536118363^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617016603 5000000000 8566536118363 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1008847243/5000000000 : ℝ), (2711805299/5000000000 : ℝ), (2617016603/5000000000 : ℝ)] ![(96027705609/781250000000 : ℝ), (11218943270363/25000000000000 : ℝ), (8566536118363/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1008847243/5000000000 : ℝ)|^4331 ≤ (96027705609/781250000000 : ℝ)^3307
        have hw : |(-1008847243/5000000000 : ℝ)|=(1008847243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711805299/5000000000 : ℝ)|^4331 ≤ (11218943270363/25000000000000 : ℝ)^3307
        have hw : |(2711805299/5000000000 : ℝ)|=(2711805299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2617016603/5000000000 : ℝ)|^4331 ≤ (8566536118363/20000000000000 : ℝ)^3307
        have hw : |(2617016603/5000000000 : ℝ)|=(2617016603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s3_1 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351653297/10000000000 : ℝ)*x 0 + (-2114515729/10000000000 : ℝ)*x 1 + (5234033349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351653297/10000000000 : ℝ)^4331 ≤ (8819527043233/20000000000000 : ℝ)^3307 := by
    have hnat : (5351653297 : ℕ)^4331*20000000000000^3307 ≤ 8819527043233^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351653297 10000000000 8819527043233 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114515729/10000000000 : ℝ)^4331 ≤ (408427582617/3125000000000 : ℝ)^3307 := by
    have hnat : (2114515729 : ℕ)^4331*3125000000000^3307 ≤ 408427582617^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114515729 10000000000 408427582617 3125000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5234033349/10000000000 : ℝ)^4331 ≤ (8566536424883/20000000000000 : ℝ)^3307 := by
    have hnat : (5234033349 : ℕ)^4331*20000000000000^3307 ≤ 8566536424883^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234033349 10000000000 8566536424883 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351653297/10000000000 : ℝ), (-2114515729/10000000000 : ℝ), (5234033349/10000000000 : ℝ)] ![(8819527043233/20000000000000 : ℝ), (408427582617/3125000000000 : ℝ), (8566536424883/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351653297/10000000000 : ℝ)|^4331 ≤ (8819527043233/20000000000000 : ℝ)^3307
        have hw : |(5351653297/10000000000 : ℝ)|=(5351653297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2114515729/10000000000 : ℝ)|^4331 ≤ (408427582617/3125000000000 : ℝ)^3307
        have hw : |(-2114515729/10000000000 : ℝ)|=(2114515729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5234033349/10000000000 : ℝ)|^4331 ≤ (8566536424883/20000000000000 : ℝ)^3307
        have hw : |(5234033349/10000000000 : ℝ)|=(5234033349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s3_2 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351653767/10000000000 : ℝ)*x 0 + (5234033387/10000000000 : ℝ)*x 1 + (-528628763/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351653767/10000000000 : ℝ)^4331 ≤ (11024410072041/25000000000000 : ℝ)^3307 := by
    have hnat : (5351653767 : ℕ)^4331*25000000000000^3307 ≤ 11024410072041^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351653767 10000000000 11024410072041 25000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5234033387/10000000000 : ℝ)^4331 ≤ (42832682531679/100000000000000 : ℝ)^3307 := by
    have hnat : (5234033387 : ℕ)^4331*100000000000000^3307 ≤ 42832682531679^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234033387 10000000000 42832682531679 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528628763/2500000000 : ℝ)^4331 ≤ (13069677163539/100000000000000 : ℝ)^3307 := by
    have hnat : (528628763 : ℕ)^4331*100000000000000^3307 ≤ 13069677163539^3307*2500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528628763 2500000000 13069677163539 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351653767/10000000000 : ℝ), (5234033387/10000000000 : ℝ), (-528628763/2500000000 : ℝ)] ![(11024410072041/25000000000000 : ℝ), (42832682531679/100000000000000 : ℝ), (13069677163539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351653767/10000000000 : ℝ)|^4331 ≤ (11024410072041/25000000000000 : ℝ)^3307
        have hw : |(5351653767/10000000000 : ℝ)|=(5351653767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5234033387/10000000000 : ℝ)|^4331 ≤ (42832682531679/100000000000000 : ℝ)^3307
        have hw : |(5234033387/10000000000 : ℝ)|=(5234033387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-528628763/2500000000 : ℝ)|^4331 ≤ (13069677163539/100000000000000 : ℝ)^3307
        have hw : |(-528628763/2500000000 : ℝ)|=(528628763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s3_3 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (67471737/156250000 : ℝ)*x 0 + (824356627/2000000000 : ℝ)*x 1 + (4523202771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67471737/156250000 : ℝ)^4331 ≤ (4161831416813/12500000000000 : ℝ)^3307 := by
    have hnat : (67471737 : ℕ)^4331*12500000000000^3307 ≤ 4161831416813^3307*156250000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67471737 156250000 4161831416813 12500000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (824356627/2000000000 : ℝ)^4331 ≤ (6265095671223/20000000000000 : ℝ)^3307 := by
    have hnat : (824356627 : ℕ)^4331*20000000000000^3307 ≤ 6265095671223^3307*2000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824356627 2000000000 6265095671223 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4523202771/10000000000 : ℝ)^4331 ≤ (1415194811693/4000000000000 : ℝ)^3307 := by
    have hnat : (4523202771 : ℕ)^4331*4000000000000^3307 ≤ 1415194811693^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523202771 10000000000 1415194811693 4000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67471737/156250000 : ℝ), (824356627/2000000000 : ℝ), (4523202771/10000000000 : ℝ)] ![(4161831416813/12500000000000 : ℝ), (6265095671223/20000000000000 : ℝ), (1415194811693/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67471737/156250000 : ℝ)|^4331 ≤ (4161831416813/12500000000000 : ℝ)^3307
        have hw : |(67471737/156250000 : ℝ)|=(67471737/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(824356627/2000000000 : ℝ)|^4331 ≤ (6265095671223/20000000000000 : ℝ)^3307
        have hw : |(824356627/2000000000 : ℝ)|=(824356627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4523202771/10000000000 : ℝ)|^4331 ≤ (1415194811693/4000000000000 : ℝ)^3307
        have hw : |(4523202771/10000000000 : ℝ)|=(4523202771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s3_4 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-6305353/31250000 : ℝ)*x 0 + (5234810561/10000000000 : ℝ)*x 1 + (5422828123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6305353/31250000 : ℝ)^4331 ≤ (1229169370749/10000000000000 : ℝ)^3307 := by
    have hnat : (6305353 : ℕ)^4331*10000000000000^3307 ≤ 1229169370749^3307*31250000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6305353 31250000 1229169370749 10000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5234810561/10000000000 : ℝ)^4331 ≤ (5355126508967/12500000000000 : ℝ)^3307 := by
    have hnat : (5234810561 : ℕ)^4331*12500000000000^3307 ≤ 5355126508967^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234810561 10000000000 5355126508967 12500000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422828123/10000000000 : ℝ)^4331 ≤ (44867294207069/100000000000000 : ℝ)^3307 := by
    have hnat : (5422828123 : ℕ)^4331*100000000000000^3307 ≤ 44867294207069^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422828123 10000000000 44867294207069 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6305353/31250000 : ℝ), (5234810561/10000000000 : ℝ), (5422828123/10000000000 : ℝ)] ![(1229169370749/10000000000000 : ℝ), (5355126508967/12500000000000 : ℝ), (44867294207069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6305353/31250000 : ℝ)|^4331 ≤ (1229169370749/10000000000000 : ℝ)^3307
        have hw : |(-6305353/31250000 : ℝ)|=(6305353/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5234810561/10000000000 : ℝ)|^4331 ≤ (5355126508967/12500000000000 : ℝ)^3307
        have hw : |(5234810561/10000000000 : ℝ)|=(5234810561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422828123/10000000000 : ℝ)|^4331 ≤ (44867294207069/100000000000000 : ℝ)^3307
        have hw : |(5422828123/10000000000 : ℝ)|=(5422828123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s3_5 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651331747/5000000000 : ℝ)*x 0 + (-385143949/2000000000 : ℝ)*x 1 + (5422828613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651331747/5000000000 : ℝ)^4331 ≤ (10892428304743/25000000000000 : ℝ)^3307 := by
    have hnat : (2651331747 : ℕ)^4331*25000000000000^3307 ≤ 10892428304743^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651331747 5000000000 10892428304743 25000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (385143949/2000000000 : ℝ)^4331 ≤ (11562987245773/100000000000000 : ℝ)^3307 := by
    have hnat : (385143949 : ℕ)^4331*100000000000000^3307 ≤ 11562987245773^3307*2000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385143949 2000000000 11562987245773 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422828613/10000000000 : ℝ)^4331 ≤ (1794691980663/4000000000000 : ℝ)^3307 := by
    have hnat : (5422828613 : ℕ)^4331*4000000000000^3307 ≤ 1794691980663^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422828613 10000000000 1794691980663 4000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651331747/5000000000 : ℝ), (-385143949/2000000000 : ℝ), (5422828613/10000000000 : ℝ)] ![(10892428304743/25000000000000 : ℝ), (11562987245773/100000000000000 : ℝ), (1794691980663/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651331747/5000000000 : ℝ)|^4331 ≤ (10892428304743/25000000000000 : ℝ)^3307
        have hw : |(2651331747/5000000000 : ℝ)|=(2651331747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-385143949/2000000000 : ℝ)|^4331 ≤ (11562987245773/100000000000000 : ℝ)^3307
        have hw : |(-385143949/2000000000 : ℝ)|=(385143949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422828613/10000000000 : ℝ)|^4331 ≤ (1794691980663/4000000000000 : ℝ)^3307
        have hw : |(5422828613/10000000000 : ℝ)|=(5422828613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s3_6 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302664417/10000000000 : ℝ)*x 0 + (338926747/625000000 : ℝ)*x 1 + (-1925719393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302664417/10000000000 : ℝ)^4331 ≤ (5446215393899/12500000000000 : ℝ)^3307 := by
    have hnat : (5302664417 : ℕ)^4331*12500000000000^3307 ≤ 5446215393899^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302664417 10000000000 5446215393899 12500000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338926747/625000000 : ℝ)^4331 ≤ (560841154427/1250000000000 : ℝ)^3307 := by
    have hnat : (338926747 : ℕ)^4331*1250000000000^3307 ≤ 560841154427^3307*625000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338926747 625000000 560841154427 1250000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1925719393/10000000000 : ℝ)^4331 ≤ (462519379109/4000000000000 : ℝ)^3307 := by
    have hnat : (1925719393 : ℕ)^4331*4000000000000^3307 ≤ 462519379109^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925719393 10000000000 462519379109 4000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302664417/10000000000 : ℝ), (338926747/625000000 : ℝ), (-1925719393/10000000000 : ℝ)] ![(5446215393899/12500000000000 : ℝ), (560841154427/1250000000000 : ℝ), (462519379109/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302664417/10000000000 : ℝ)|^4331 ≤ (5446215393899/12500000000000 : ℝ)^3307
        have hw : |(5302664417/10000000000 : ℝ)|=(5302664417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338926747/625000000 : ℝ)|^4331 ≤ (560841154427/1250000000000 : ℝ)^3307
        have hw : |(338926747/625000000 : ℝ)|=(338926747/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1925719393/10000000000 : ℝ)|^4331 ≤ (462519379109/4000000000000 : ℝ)^3307
        have hw : |(-1925719393/10000000000 : ℝ)|=(1925719393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s3_7 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4318230059/10000000000 : ℝ)*x 0 + (2260778111/5000000000 : ℝ)*x 1 + (2061719051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318230059/10000000000 : ℝ)^4331 ≤ (33295044048439/100000000000000 : ℝ)^3307 := by
    have hnat : (4318230059 : ℕ)^4331*100000000000000^3307 ≤ 33295044048439^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318230059 10000000000 33295044048439 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2260778111/5000000000 : ℝ)^4331 ≤ (7072600840971/20000000000000 : ℝ)^3307 := by
    have hnat : (2260778111 : ℕ)^4331*20000000000000^3307 ≤ 7072600840971^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260778111 5000000000 7072600840971 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2061719051/5000000000 : ℝ)^4331 ≤ (6268390348577/20000000000000 : ℝ)^3307 := by
    have hnat : (2061719051 : ℕ)^4331*20000000000000^3307 ≤ 6268390348577^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061719051 5000000000 6268390348577 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318230059/10000000000 : ℝ), (2260778111/5000000000 : ℝ), (2061719051/5000000000 : ℝ)] ![(33295044048439/100000000000000 : ℝ), (7072600840971/20000000000000 : ℝ), (6268390348577/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318230059/10000000000 : ℝ)|^4331 ≤ (33295044048439/100000000000000 : ℝ)^3307
        have hw : |(4318230059/10000000000 : ℝ)|=(4318230059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2260778111/5000000000 : ℝ)|^4331 ≤ (7072600840971/20000000000000 : ℝ)^3307
        have hw : |(2260778111/5000000000 : ℝ)|=(2260778111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2061719051/5000000000 : ℝ)|^4331 ≤ (6268390348577/20000000000000 : ℝ)^3307
        have hw : |(2061719051/5000000000 : ℝ)|=(2061719051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1371_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155872451/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7997/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2007/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2743/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1873/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7997/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2007/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7997/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2007/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7997/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2007/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7997/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2007/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7997/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2007/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7997/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2007/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (2007/20000 : ℝ) ^ (2165/512 : ℝ) ≤ (5996538503451209/100000000000000000000 : ℝ) := by
    have hpowers : (2007/20000 : ℝ)^2165 ≤ (5996538503451209/100000000000000000000 : ℝ)^512 := by
      have hnat : (2007 : ℕ)^2165*100000000000000000000^512 ≤ 5996538503451209^512*20000^2165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2007 20000 5996538503451209 100000000000000000000 2165 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2007/20000 : ℝ)) (X := (5996538503451209/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7997/50000 : ℝ) ^ (2165/512 : ℝ) ≤ (538059293460511/1250000000000000000 : ℝ) := by
    have hpowers : (7997/50000 : ℝ)^2165 ≤ (538059293460511/1250000000000000000 : ℝ)^512 := by
      have hnat : (7997 : ℕ)^2165*1250000000000000000^512 ≤ 538059293460511^512*50000^2165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7997 50000 538059293460511 1250000000000000000 2165 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7997/50000 : ℝ)) (X := (538059293460511/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005996538503451209/50000000000000000000 : ℝ) ≤ (2000056722164541/2000000000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (50005996538503451209/50000000000000000000 : ℝ)^512 ≤ (2000056722164541/2000000000000000 : ℝ)^2165 := by
      have hnat : (50005996538503451209 : ℕ)^512*2000000000000000^2165 ≤ 2000056722164541^2165*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005996538503451209 50000000000000000000 2000056722164541 2000000000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000056722164541/2000000000000000 : ℝ)) (X := (50005996538503451209/50000000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049041281980292089/100000000000000000000 : ℝ) ≤ (10001159558284311/10000000000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (100049041281980292089/100000000000000000000 : ℝ)^512 ≤ (10001159558284311/10000000000000000 : ℝ)^2165 := by
      have hnat : (100049041281980292089 : ℕ)^512*10000000000000000^2165 ≤ 10001159558284311^2165*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049041281980292089 100000000000000000000 10001159558284311 10000000000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001159558284311/10000000000000000 : ℝ)) (X := (100049041281980292089/100000000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (625538059293460511/625000000000000000 : ℝ) ≤ (10002035505745917/10000000000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (625538059293460511/625000000000000000 : ℝ)^512 ≤ (10002035505745917/10000000000000000 : ℝ)^2165 := by
      have hnat : (625538059293460511 : ℕ)^512*10000000000000000^2165 ≤ 10002035505745917^2165*625000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625538059293460511 625000000000000000 10002035505745917 10000000000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002035505745917/10000000000000000 : ℝ)) (X := (625538059293460511/625000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5996538503451209/100000000000000000000 : ℝ) ≤ ((2382964390853522667/2383600000000000000 : ℝ)+2*(437973730803/297950000000000 : ℝ)*(2007/20000 : ℝ))^(2165/512 : ℝ) := by
    rw [show (2382964390853522667/2383600000000000000 : ℝ)+2*(437973730803/297950000000000 : ℝ)*(2007/20000 : ℝ)=(2000056722164541/2000000000000000 : ℝ) by norm_num, show 1+2*(5996538503451209/100000000000000000000 : ℝ)=(50005996538503451209/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(538059293460511/1250000000000000000 : ℝ)+(5996538503451209/100000000000000000000 : ℝ) ≤ ((2382964390853522667/2383600000000000000 : ℝ)+(437973730803/297950000000000 : ℝ)*((7997/50000 : ℝ)+(2007/20000 : ℝ)))^(2165/512 : ℝ) := by
    rw [show (2382964390853522667/2383600000000000000 : ℝ)+(437973730803/297950000000000 : ℝ)*((7997/50000 : ℝ)+(2007/20000 : ℝ))=(10001159558284311/10000000000000000 : ℝ) by norm_num, show 1+(538059293460511/1250000000000000000 : ℝ)+(5996538503451209/100000000000000000000 : ℝ)=(100049041281980292089/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(538059293460511/1250000000000000000 : ℝ) ≤ ((2382964390853522667/2383600000000000000 : ℝ)+2*(437973730803/297950000000000 : ℝ)*(7997/50000 : ℝ))^(2165/512 : ℝ) := by
    rw [show (2382964390853522667/2383600000000000000 : ℝ)+2*(437973730803/297950000000000 : ℝ)*(7997/50000 : ℝ)=(10002035505745917/10000000000000000 : ℝ) by norm_num, show 1+2*(538059293460511/1250000000000000000 : ℝ)=(625538059293460511/625000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2382964390853522667/2383600000000000000 : ℝ)*(X 1 0+X 2 0)+(437973730803/297950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (2007/20000 : ℝ)) (hi := (7997/50000 : ℝ)) (c := (2382964390853522667/2383600000000000000 : ℝ)) (alpha := (437973730803/297950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2382964390853522667/2383600000000000000 : ℝ)*(X 0 1+X 2 1)+(437973730803/297950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (2007/20000 : ℝ)) (hi := (7997/50000 : ℝ)) (c := (2382964390853522667/2383600000000000000 : ℝ)) (alpha := (437973730803/297950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2382964390853522667/2383600000000000000 : ℝ)*(X 0 2+X 1 2)+(437973730803/297950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (2007/20000 : ℝ)) (hi := (7997/50000 : ℝ)) (c := (2382964390853522667/2383600000000000000 : ℝ)) (alpha := (437973730803/297950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1008847243/5000000000 : ℝ)*X 0 0+(2711805299/5000000000 : ℝ)*X 0 1+(2617016603/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351653297/10000000000 : ℝ)*X 1 0+(-2114515729/10000000000 : ℝ)*X 1 1+(5234033349/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351653767/10000000000 : ℝ)*X 2 0+(5234033387/10000000000 : ℝ)*X 2 1+(-528628763/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((67471737/156250000 : ℝ)*X 0 0+(824356627/2000000000 : ℝ)*X 0 1+(4523202771/10000000000 : ℝ)*X 0 2+(67471737/156250000 : ℝ)*X 1 0+(824356627/2000000000 : ℝ)*X 1 1+(4523202771/10000000000 : ℝ)*X 1 2+(67471737/156250000 : ℝ)*X 2 0+(824356627/2000000000 : ℝ)*X 2 1+(4523202771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-6305353/31250000 : ℝ)*X 0 0+(5234810561/10000000000 : ℝ)*X 0 1+(5422828123/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651331747/5000000000 : ℝ)*X 1 0+(-385143949/2000000000 : ℝ)*X 1 1+(5422828613/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302664417/10000000000 : ℝ)*X 2 0+(338926747/625000000 : ℝ)*X 2 1+(-1925719393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4318230059/10000000000 : ℝ)*X 0 0+(2260778111/5000000000 : ℝ)*X 0 1+(2061719051/5000000000 : ℝ)*X 0 2+(4318230059/10000000000 : ℝ)*X 1 0+(2260778111/5000000000 : ℝ)*X 1 1+(2061719051/5000000000 : ℝ)*X 1 2+(4318230059/10000000000 : ℝ)*X 2 0+(2260778111/5000000000 : ℝ)*X 2 1+(2061719051/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (245426280886312629465212757/119180000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (158551201/100000000000000 : ℝ)*(base8) + (503160399/100000000000000 : ℝ)*(base15) + (68799997/50000000000000 : ℝ)*(base29) + (21107813/25000000000000 : ℝ)*(lower2) + (3883030713348757/100000000000000 : ℝ)*(major0) + (242689428184297/6250000000000 : ℝ)*(major1) + (242689428184297/6250000000000 : ℝ)*(major2) + (1318724185638101/25000000000000 : ℝ)*(sp0) + (659360862251773/12500000000000 : ℝ)*(sp1) + (5274901770943777/100000000000000 : ℝ)*(sp2) + (622789791595173/25000000000000 : ℝ)*(sp3) + (1391442543/25000000000000 : ℝ)*(sp4) + (14928099201/100000000000000 : ℝ)*(sp5) + (279165003/50000000000000 : ℝ)*(sp6) + (622789791595173/25000000000000 : ℝ)*(f.failure) + (5274902466873777/100000000000000 : ℝ)*(f.sum) + (9166383988991/3724375000000000000000000000 : ℝ)*base66 + (86574547321048099/14897500000000000000000000000000 : ℝ)*base67 + (121491629487868099/14897500000000000000000000000000 : ℝ)*base69 + (1708097531116657081/238360000000000000000000000000000 : ℝ)*base72 + (1535616467611/14897500000000000000000000000 : ℝ)*base73 + (119318552250101901/14897500000000000000000000000000 : ℝ)*base76 + (2322404052385497081/238360000000000000000000000000000 : ℝ)*base78 + (15642110408426901/14897500000000000000000000000000 : ℝ)*base80 + (160126536377423/29795000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (40279023/2500000000000000000000 : ℝ)*base89 + (15279023/2500000000000000000000 : ℝ)*base91 + (15279023/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42686878990469318997/29500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1020318493/100000000000000 : ℝ)*(base19) + (152082177/6250000000000 : ℝ)*(base23) + (146743107/50000000000000 : ℝ)*(upper3) + (151562919/100000000000000 : ℝ)*(lower4) + (38746301/20000000000000 : ℝ)*(upper5) + (783047407877349/20000000000000 : ℝ)*(major0) + (783047407877349/20000000000000 : ℝ)*(major1) + (783047407877349/20000000000000 : ℝ)*(major2) + (1149777369/5000000000000 : ℝ)*(sp1) + (2239719241/5000000000000 : ℝ)*(sp2) + (1063730595592419/20000000000000 : ℝ)*(sp4) + (5318628962096223/100000000000000 : ℝ)*(sp5) + (5318605750262443/100000000000000 : ℝ)*(sp6) + (1255910526288813/50000000000000 : ℝ)*(sp7) + (1255910526288813/50000000000000 : ℝ)*(f.failure) + (1063730595592419/20000000000000 : ℝ)*(f.sum) + (37883634447/14750000000000000000000000 : ℝ)*base65 + (1889721563573483/472000000000000000000000000000 : ℝ)*base67 + (1888274651866517/472000000000000000000000000000 : ℝ)*base70 + (2579070921634517/472000000000000000000000000000 : ℝ)*base72 + (256040229891/59000000000000000000000000 : ℝ)*base73 + (934460183114517/472000000000000000000000000000 : ℝ)*base76 + (538907908037483/472000000000000000000000000000 : ℝ)*base77 + (1852666362941483/472000000000000000000000000000 : ℝ)*base79 + (180307104427/59000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (33809337/5000000000000000000000 : ℝ)*base90 + (33809337/5000000000000000000000 : ℝ)*base92 + (33809337/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1371_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155872451/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7997/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2007/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2743/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1873/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1371_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1371_s4_0 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1009469559/5000000000 : ℝ)*x 0 + (169165363/312500000 : ℝ)*x 1 + (655441769/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1009469559/5000000000 : ℝ)^4331 ≤ (12301477193407/100000000000000 : ℝ)^3307 := by
    have hnat : (1009469559 : ℕ)^4331*100000000000000^3307 ≤ 12301477193407^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009469559 5000000000 12301477193407 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169165363/312500000 : ℝ)^4331 ≤ (179055949493/400000000000 : ℝ)^3307 := by
    have hnat : (169165363 : ℕ)^4331*400000000000^3307 ≤ 179055949493^3307*312500000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169165363 312500000 179055949493 400000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655441769/1250000000 : ℝ)^4331 ≤ (42934535416379/100000000000000 : ℝ)^3307 := by
    have hnat : (655441769 : ℕ)^4331*100000000000000^3307 ≤ 42934535416379^3307*1250000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655441769 1250000000 42934535416379 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1009469559/5000000000 : ℝ), (169165363/312500000 : ℝ), (655441769/1250000000 : ℝ)] ![(12301477193407/100000000000000 : ℝ), (179055949493/400000000000 : ℝ), (42934535416379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1009469559/5000000000 : ℝ)|^4331 ≤ (12301477193407/100000000000000 : ℝ)^3307
        have hw : |(-1009469559/5000000000 : ℝ)|=(1009469559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169165363/312500000 : ℝ)|^4331 ≤ (179055949493/400000000000 : ℝ)^3307
        have hw : |(169165363/312500000 : ℝ)|=(169165363/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655441769/1250000000 : ℝ)|^4331 ≤ (42934535416379/100000000000000 : ℝ)^3307
        have hw : |(655441769/1250000000 : ℝ)|=(655441769/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s4_1 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674506419/5000000000 : ℝ)*x 0 + (-263180893/1250000000 : ℝ)*x 1 + (5243534053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674506419/5000000000 : ℝ)^4331 ≤ (5508642864037/12500000000000 : ℝ)^3307 := by
    have hnat : (2674506419 : ℕ)^4331*12500000000000^3307 ≤ 5508642864037^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674506419 5000000000 5508642864037 12500000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263180893/1250000000 : ℝ)^4331 ≤ (649816135851/5000000000000 : ℝ)^3307 := by
    have hnat : (263180893 : ℕ)^4331*5000000000000^3307 ≤ 649816135851^3307*1250000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263180893 1250000000 649816135851 5000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243534053/10000000000 : ℝ)^4331 ≤ (670852099293/1562500000000 : ℝ)^3307 := by
    have hnat : (5243534053 : ℕ)^4331*1562500000000^3307 ≤ 670852099293^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243534053 10000000000 670852099293 1562500000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674506419/5000000000 : ℝ), (-263180893/1250000000 : ℝ), (5243534053/10000000000 : ℝ)] ![(5508642864037/12500000000000 : ℝ), (649816135851/5000000000000 : ℝ), (670852099293/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674506419/5000000000 : ℝ)|^4331 ≤ (5508642864037/12500000000000 : ℝ)^3307
        have hw : |(2674506419/5000000000 : ℝ)|=(2674506419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-263180893/1250000000 : ℝ)|^4331 ≤ (649816135851/5000000000000 : ℝ)^3307
        have hw : |(-263180893/1250000000 : ℝ)|=(263180893/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243534053/10000000000 : ℝ)|^4331 ≤ (670852099293/1562500000000 : ℝ)^3307
        have hw : |(5243534053/10000000000 : ℝ)|=(5243534053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s4_2 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337253201/2500000000 : ℝ)*x 0 + (5243534241/10000000000 : ℝ)*x 1 + (-105272347/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337253201/2500000000 : ℝ)^4331 ≤ (22034571272721/50000000000000 : ℝ)^3307 := by
    have hnat : (1337253201 : ℕ)^4331*50000000000000^3307 ≤ 22034571272721^3307*2500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337253201 2500000000 22034571272721 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243534241/10000000000 : ℝ)^4331 ≤ (42934536370771/100000000000000 : ℝ)^3307 := by
    have hnat : (5243534241 : ℕ)^4331*100000000000000^3307 ≤ 42934536370771^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243534241 10000000000 42934536370771 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105272347/500000000 : ℝ)^4331 ≤ (1299632106787/10000000000000 : ℝ)^3307 := by
    have hnat : (105272347 : ℕ)^4331*10000000000000^3307 ≤ 1299632106787^3307*500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105272347 500000000 1299632106787 10000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337253201/2500000000 : ℝ), (5243534241/10000000000 : ℝ), (-105272347/500000000 : ℝ)] ![(22034571272721/50000000000000 : ℝ), (42934536370771/100000000000000 : ℝ), (1299632106787/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337253201/2500000000 : ℝ)|^4331 ≤ (22034571272721/50000000000000 : ℝ)^3307
        have hw : |(1337253201/2500000000 : ℝ)|=(1337253201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243534241/10000000000 : ℝ)|^4331 ≤ (42934536370771/100000000000000 : ℝ)^3307
        have hw : |(5243534241/10000000000 : ℝ)|=(5243534241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-105272347/500000000 : ℝ)|^4331 ≤ (1299632106787/10000000000000 : ℝ)^3307
        have hw : |(-105272347/500000000 : ℝ)|=(105272347/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s4_3 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079737443/2500000000 : ℝ)*x 0 + (1035668389/2500000000 : ℝ)*x 1 + (2251063003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079737443/2500000000 : ℝ)^4331 ≤ (520348621427/1562500000000 : ℝ)^3307 := by
    have hnat : (1079737443 : ℕ)^4331*1562500000000^3307 ≤ 520348621427^3307*2500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079737443 2500000000 520348621427 1562500000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035668389/2500000000 : ℝ)^4331 ≤ (157667848491/500000000000 : ℝ)^3307 := by
    have hnat : (1035668389 : ℕ)^4331*500000000000^3307 ≤ 157667848491^3307*2500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035668389 2500000000 157667848491 500000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251063003/5000000000 : ℝ)^4331 ≤ (17582059263303/50000000000000 : ℝ)^3307 := by
    have hnat : (2251063003 : ℕ)^4331*50000000000000^3307 ≤ 17582059263303^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251063003 5000000000 17582059263303 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079737443/2500000000 : ℝ), (1035668389/2500000000 : ℝ), (2251063003/5000000000 : ℝ)] ![(520348621427/1562500000000 : ℝ), (157667848491/500000000000 : ℝ), (17582059263303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079737443/2500000000 : ℝ)|^4331 ≤ (520348621427/1562500000000 : ℝ)^3307
        have hw : |(1079737443/2500000000 : ℝ)|=(1079737443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035668389/2500000000 : ℝ)|^4331 ≤ (157667848491/500000000000 : ℝ)^3307
        have hw : |(1035668389/2500000000 : ℝ)|=(1035668389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2251063003/5000000000 : ℝ)|^4331 ≤ (17582059263303/50000000000000 : ℝ)^3307
        have hw : |(2251063003/5000000000 : ℝ)|=(2251063003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s4_4 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-403790381/2000000000 : ℝ)*x 0 + (5244157913/10000000000 : ℝ)*x 1 + (2706332267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (403790381/2000000000 : ℝ)^4331 ≤ (3075394807569/25000000000000 : ℝ)^3307 := by
    have hnat : (403790381 : ℕ)^4331*25000000000000^3307 ≤ 3075394807569^3307*2000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403790381 2000000000 3075394807569 25000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244157913/10000000000 : ℝ)^4331 ≤ (21470612221093/50000000000000 : ℝ)^3307 := by
    have hnat : (5244157913 : ℕ)^4331*50000000000000^3307 ≤ 21470612221093^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244157913 10000000000 21470612221093 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706332267/5000000000 : ℝ)^4331 ≤ (22378598154217/50000000000000 : ℝ)^3307 := by
    have hnat : (2706332267 : ℕ)^4331*50000000000000^3307 ≤ 22378598154217^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706332267 5000000000 22378598154217 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-403790381/2000000000 : ℝ), (5244157913/10000000000 : ℝ), (2706332267/5000000000 : ℝ)] ![(3075394807569/25000000000000 : ℝ), (21470612221093/50000000000000 : ℝ), (22378598154217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-403790381/2000000000 : ℝ)|^4331 ≤ (3075394807569/25000000000000 : ℝ)^3307
        have hw : |(-403790381/2000000000 : ℝ)|=(403790381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244157913/10000000000 : ℝ)|^4331 ≤ (21470612221093/50000000000000 : ℝ)^3307
        have hw : |(5244157913/10000000000 : ℝ)|=(5244157913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706332267/5000000000 : ℝ)|^4331 ≤ (22378598154217/50000000000000 : ℝ)^3307
        have hw : |(2706332267/5000000000 : ℝ)|=(2706332267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s4_5 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652572299/5000000000 : ℝ)*x 0 + (-1936316873/10000000000 : ℝ)*x 1 + (5412664377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652572299/5000000000 : ℝ)^4331 ≤ (43596413820633/100000000000000 : ℝ)^3307 := by
    have hnat : (2652572299 : ℕ)^4331*100000000000000^3307 ≤ 43596413820633^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652572299 5000000000 43596413820633 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1936316873/10000000000 : ℝ)^4331 ≤ (11646391560609/100000000000000 : ℝ)^3307 := by
    have hnat : (1936316873 : ℕ)^4331*100000000000000^3307 ≤ 11646391560609^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936316873 10000000000 11646391560609 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412664377/10000000000 : ℝ)^4331 ≤ (44757194608213/100000000000000 : ℝ)^3307 := by
    have hnat : (5412664377 : ℕ)^4331*100000000000000^3307 ≤ 44757194608213^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412664377 10000000000 44757194608213 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652572299/5000000000 : ℝ), (-1936316873/10000000000 : ℝ), (5412664377/10000000000 : ℝ)] ![(43596413820633/100000000000000 : ℝ), (11646391560609/100000000000000 : ℝ), (44757194608213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652572299/5000000000 : ℝ)|^4331 ≤ (43596413820633/100000000000000 : ℝ)^3307
        have hw : |(2652572299/5000000000 : ℝ)|=(2652572299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1936316873/10000000000 : ℝ)|^4331 ≤ (11646391560609/100000000000000 : ℝ)^3307
        have hw : |(-1936316873/10000000000 : ℝ)|=(1936316873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412664377/10000000000 : ℝ)|^4331 ≤ (44757194608213/100000000000000 : ℝ)^3307
        have hw : |(5412664377/10000000000 : ℝ)|=(5412664377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s4_6 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326286171/2500000000 : ℝ)*x 0 + (2706332139/5000000000 : ℝ)*x 1 + (-1936316891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326286171/2500000000 : ℝ)^4331 ≤ (10899103686549/25000000000000 : ℝ)^3307 := by
    have hnat : (1326286171 : ℕ)^4331*25000000000000^3307 ≤ 10899103686549^3307*2500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326286171 2500000000 10899103686549 25000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706332139/5000000000 : ℝ)^4331 ≤ (44757193536099/100000000000000 : ℝ)^3307 := by
    have hnat : (2706332139 : ℕ)^4331*100000000000000^3307 ≤ 44757193536099^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706332139 5000000000 44757193536099 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1936316891/10000000000 : ℝ)^4331 ≤ (5823195851199/50000000000000 : ℝ)^3307 := by
    have hnat : (1936316891 : ℕ)^4331*50000000000000^3307 ≤ 5823195851199^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936316891 10000000000 5823195851199 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326286171/2500000000 : ℝ), (2706332139/5000000000 : ℝ), (-1936316891/10000000000 : ℝ)] ![(10899103686549/25000000000000 : ℝ), (44757193536099/100000000000000 : ℝ), (5823195851199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326286171/2500000000 : ℝ)|^4331 ≤ (10899103686549/25000000000000 : ℝ)^3307
        have hw : |(1326286171/2500000000 : ℝ)|=(1326286171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706332139/5000000000 : ℝ)|^4331 ≤ (44757193536099/100000000000000 : ℝ)^3307
        have hw : |(2706332139/5000000000 : ℝ)|=(2706332139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1936316891/10000000000 : ℝ)|^4331 ≤ (5823195851199/50000000000000 : ℝ)^3307
        have hw : |(-1936316891/10000000000 : ℝ)|=(1936316891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s4_7 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2159488269/5000000000 : ℝ)*x 0 + (2250402689/5000000000 : ℝ)*x 1 + (414400141/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159488269/5000000000 : ℝ)^4331 ≤ (16651291031949/50000000000000 : ℝ)^3307 := by
    have hnat : (2159488269 : ℕ)^4331*50000000000000^3307 ≤ 16651291031949^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159488269 5000000000 16651291031949 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250402689/5000000000 : ℝ)^4331 ≤ (35150610346147/100000000000000 : ℝ)^3307 := by
    have hnat : (2250402689 : ℕ)^4331*100000000000000^3307 ≤ 35150610346147^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250402689 5000000000 35150610346147 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (414400141/1000000000 : ℝ)^4331 ≤ (15773403786813/50000000000000 : ℝ)^3307 := by
    have hnat : (414400141 : ℕ)^4331*50000000000000^3307 ≤ 15773403786813^3307*1000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414400141 1000000000 15773403786813 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2159488269/5000000000 : ℝ), (2250402689/5000000000 : ℝ), (414400141/1000000000 : ℝ)] ![(16651291031949/50000000000000 : ℝ), (35150610346147/100000000000000 : ℝ), (15773403786813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2159488269/5000000000 : ℝ)|^4331 ≤ (16651291031949/50000000000000 : ℝ)^3307
        have hw : |(2159488269/5000000000 : ℝ)|=(2159488269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2250402689/5000000000 : ℝ)|^4331 ≤ (35150610346147/100000000000000 : ℝ)^3307
        have hw : |(2250402689/5000000000 : ℝ)|=(2250402689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(414400141/1000000000 : ℝ)|^4331 ≤ (15773403786813/50000000000000 : ℝ)^3307
        have hw : |(414400141/1000000000 : ℝ)|=(414400141/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1371_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155872451/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1873/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2743/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5587/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14769/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1873/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2743/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1873/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2743/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1873/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2743/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1873/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2743/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1873/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2743/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1873/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2743/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2743/25000 : ℝ) ^ (2165/512 : ℝ) ≤ (1093310498066391/12500000000000000000 : ℝ) := by
    have hpowers : (2743/25000 : ℝ)^2165 ≤ (1093310498066391/12500000000000000000 : ℝ)^512 := by
      have hnat : (2743 : ℕ)^2165*12500000000000000000^512 ≤ 1093310498066391^512*25000^2165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2743 25000 1093310498066391 12500000000000000000 2165 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2743/25000 : ℝ)) (X := (1093310498066391/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1873/12500 : ℝ) ^ (2165/512 : ℝ) ≤ (8167123624408559/25000000000000000000 : ℝ) := by
    have hpowers : (1873/12500 : ℝ)^2165 ≤ (8167123624408559/25000000000000000000 : ℝ)^512 := by
      have hnat : (1873 : ℕ)^2165*25000000000000000000^512 ≤ 8167123624408559^512*12500^2165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1873 12500 8167123624408559 25000000000000000000 2165 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1873/12500 : ℝ)) (X := (8167123624408559/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251093310498066391/6250000000000000000 : ℝ) ≤ (625025853930573/625000000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (6251093310498066391/6250000000000000000 : ℝ)^512 ≤ (625025853930573/625000000000000 : ℝ)^2165 := by
      have hnat : (6251093310498066391 : ℕ)^512*625000000000000^2165 ≤ 625025853930573^2165*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251093310498066391 6250000000000000000 625025853930573 625000000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625025853930573/625000000000000 : ℝ)) (X := (6251093310498066391/6250000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010353744620541341/25000000000000000000 : ℝ) ≤ (1250122408298447/1250000000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (25010353744620541341/25000000000000000000 : ℝ)^512 ≤ (1250122408298447/1250000000000000 : ℝ)^2165 := by
      have hnat : (25010353744620541341 : ℕ)^512*1250000000000000^2165 ≤ 1250122408298447^2165*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010353744620541341 25000000000000000000 1250122408298447 1250000000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250122408298447/1250000000000000 : ℝ)) (X := (25010353744620541341/25000000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508167123624408559/12500000000000000000 : ℝ) ≤ (312548277183937/312500000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (12508167123624408559/12500000000000000000 : ℝ)^512 ≤ (312548277183937/312500000000000 : ℝ)^2165 := by
      have hnat : (12508167123624408559 : ℕ)^512*312500000000000^2165 ≤ 312548277183937^2165*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508167123624408559 12500000000000000000 312548277183937 312500000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312548277183937/312500000000000 : ℝ)) (X := (12508167123624408559/12500000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1093310498066391/12500000000000000000 : ℝ) ≤ ((9216279414600707/9218750000000000 : ℝ)+2*(4158849253/2950000000000 : ℝ)*(2743/25000 : ℝ))^(2165/512 : ℝ) := by
    rw [show (9216279414600707/9218750000000000 : ℝ)+2*(4158849253/2950000000000 : ℝ)*(2743/25000 : ℝ)=(625025853930573/625000000000000 : ℝ) by norm_num, show 1+2*(1093310498066391/12500000000000000000 : ℝ)=(6251093310498066391/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8167123624408559/25000000000000000000 : ℝ)+(1093310498066391/12500000000000000000 : ℝ) ≤ ((9216279414600707/9218750000000000 : ℝ)+(4158849253/2950000000000 : ℝ)*((1873/12500 : ℝ)+(2743/25000 : ℝ)))^(2165/512 : ℝ) := by
    rw [show (9216279414600707/9218750000000000 : ℝ)+(4158849253/2950000000000 : ℝ)*((1873/12500 : ℝ)+(2743/25000 : ℝ))=(1250122408298447/1250000000000000 : ℝ) by norm_num, show 1+(8167123624408559/25000000000000000000 : ℝ)+(1093310498066391/12500000000000000000 : ℝ)=(25010353744620541341/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8167123624408559/25000000000000000000 : ℝ) ≤ ((9216279414600707/9218750000000000 : ℝ)+2*(4158849253/2950000000000 : ℝ)*(1873/12500 : ℝ))^(2165/512 : ℝ) := by
    rw [show (9216279414600707/9218750000000000 : ℝ)+2*(4158849253/2950000000000 : ℝ)*(1873/12500 : ℝ)=(312548277183937/312500000000000 : ℝ) by norm_num, show 1+2*(8167123624408559/25000000000000000000 : ℝ)=(12508167123624408559/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9216279414600707/9218750000000000 : ℝ)*(X 1 0+X 2 0)+(4158849253/2950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (2743/25000 : ℝ)) (hi := (1873/12500 : ℝ)) (c := (9216279414600707/9218750000000000 : ℝ)) (alpha := (4158849253/2950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9216279414600707/9218750000000000 : ℝ)*(X 0 1+X 2 1)+(4158849253/2950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (2743/25000 : ℝ)) (hi := (1873/12500 : ℝ)) (c := (9216279414600707/9218750000000000 : ℝ)) (alpha := (4158849253/2950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9216279414600707/9218750000000000 : ℝ)*(X 0 2+X 1 2)+(4158849253/2950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (2743/25000 : ℝ)) (hi := (1873/12500 : ℝ)) (c := (9216279414600707/9218750000000000 : ℝ)) (alpha := (4158849253/2950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1009469559/5000000000 : ℝ)*X 0 0+(169165363/312500000 : ℝ)*X 0 1+(655441769/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674506419/5000000000 : ℝ)*X 1 0+(-263180893/1250000000 : ℝ)*X 1 1+(5243534053/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337253201/2500000000 : ℝ)*X 2 0+(5243534241/10000000000 : ℝ)*X 2 1+(-105272347/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1079737443/2500000000 : ℝ)*X 0 0+(1035668389/2500000000 : ℝ)*X 0 1+(2251063003/5000000000 : ℝ)*X 0 2+(1079737443/2500000000 : ℝ)*X 1 0+(1035668389/2500000000 : ℝ)*X 1 1+(2251063003/5000000000 : ℝ)*X 1 2+(1079737443/2500000000 : ℝ)*X 2 0+(1035668389/2500000000 : ℝ)*X 2 1+(2251063003/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-403790381/2000000000 : ℝ)*X 0 0+(5244157913/10000000000 : ℝ)*X 0 1+(2706332267/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652572299/5000000000 : ℝ)*X 1 0+(-1936316873/10000000000 : ℝ)*X 1 1+(5412664377/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326286171/2500000000 : ℝ)*X 2 0+(2706332139/5000000000 : ℝ)*X 2 1+(-1936316891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2159488269/5000000000 : ℝ)*X 0 0+(2250402689/5000000000 : ℝ)*X 0 1+(414400141/1000000000 : ℝ)*X 0 2+(2159488269/5000000000 : ℝ)*X 1 0+(2250402689/5000000000 : ℝ)*X 1 1+(414400141/1000000000 : ℝ)*X 1 2+(2159488269/5000000000 : ℝ)*X 2 0+(2250402689/5000000000 : ℝ)*X 2 1+(414400141/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9868329115655501505680523/921875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (530986053/25000000000000 : ℝ)*(base19) + (1972219863/100000000000000 : ℝ)*(base23) + (1910271/3125000000000 : ℝ)*(lower2) + (122210057/100000000000000 : ℝ)*(upper3) + (139629229/50000000000000 : ℝ)*(upper5) + (2168224491660261/50000000000000 : ℝ)*(major0) + (2168224491660261/50000000000000 : ℝ)*(major1) + (2168224491660261/50000000000000 : ℝ)*(major2) + (5890798898225443/100000000000000 : ℝ)*(sp0) + (5890845832136547/100000000000000 : ℝ)*(sp1) + (184088936995653/3125000000000 : ℝ)*(sp2) + (1391015140492781/50000000000000 : ℝ)*(sp3) + (12264463829/25000000000000 : ℝ)*(sp4) + (9686376889/50000000000000 : ℝ)*(sp7) + (139102482686967/5000000000000 : ℝ)*(f.failure) + (5890847956080759/100000000000000 : ℝ)*(f.sum) + (457955415599/147500000000000000000000000 : ℝ)*base66 + (253385579904337/115234375000000000000000000000 : ℝ)*base68 + (728546053185587/115234375000000000000000000000 : ℝ)*base70 + (941048310695473/460937500000000000000000000000 : ℝ)*base72 + (171353290959/36875000000000000000000000 : ℝ)*base73 + (3060402953437179/921875000000000000000000000000 : ℝ)*base75 + (2126885084574299/230468750000000000000000000000 : ℝ)*base78 + (3612715198324299/230468750000000000000000000000 : ℝ)*base80 + (119358444273/73750000000000000000000000 : ℝ)*base81 + (2046117/500000000000000000000 : ℝ)*base89 + (2046117/500000000000000000000 : ℝ)*base91 + (2046117/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10358427442461751057577409/921875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1940735011/100000000000000 : ℝ)*(base19) + (517924569/25000000000000 : ℝ)*(base23) + (11097547/50000000000000 : ℝ)*(upper2) + (161152711/100000000000000 : ℝ)*(upper3) + (105053959/50000000000000 : ℝ)*(upper5) + (2184286528534087/50000000000000 : ℝ)*(major0) + (2184286528534087/50000000000000 : ℝ)*(major1) + (2184286528534087/50000000000000 : ℝ)*(major2) + (37601543949/100000000000000 : ℝ)*(sp1) + (36745955311/100000000000000 : ℝ)*(sp2) + (5934486880352949/100000000000000 : ℝ)*(sp4) + (5934447338073989/100000000000000 : ℝ)*(sp5) + (5934448062699363/100000000000000 : ℝ)*(sp6) + (87583089351293/3125000000000 : ℝ)*(sp7) + (87583089351293/3125000000000 : ℝ)*(f.failure) + (5934486880352949/100000000000000 : ℝ)*(f.sum) + (583379007359/295000000000000000000000000 : ℝ)*base65 + (11833237544933393/921875000000000000000000000000 : ℝ)*base67 + (2700383410755759/460937500000000000000000000000 : ℝ)*base69 + (2752602335401317/230468750000000000000000000000 : ℝ)*base71 + (1026364685919/295000000000000000000000000 : ℝ)*base73 + (7515532718130759/460937500000000000000000000000 : ℝ)*base75 + (941803082802221/115234375000000000000000000000 : ℝ)*base77 + (3024182490254107/921875000000000000000000000000 : ℝ)*base80 + (832983538879/295000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3820857/312500000000000000000 : ℝ)*base90 + (3820857/312500000000000000000 : ℝ)*base92 + (3820857/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1371_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155872451/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1873/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2743/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5587/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1371_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1371_s5_0 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1009571907/5000000000 : ℝ)*x 0 + (2705757193/5000000000 : ℝ)*x 1 + (5245176509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1009571907/5000000000 : ℝ)^4331 ≤ (6151555318619/50000000000000 : ℝ)^3307 := by
    have hnat : (1009571907 : ℕ)^4331*50000000000000^3307 ≤ 6151555318619^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009571907 5000000000 6151555318619 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705757193/5000000000 : ℝ)^4331 ≤ (44744741266587/100000000000000 : ℝ)^3307 := by
    have hnat : (2705757193 : ℕ)^4331*100000000000000^3307 ≤ 44744741266587^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705757193 5000000000 44744741266587 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245176509/10000000000 : ℝ)^4331 ≤ (1342254627803/3125000000000 : ℝ)^3307 := by
    have hnat : (5245176509 : ℕ)^4331*3125000000000^3307 ≤ 1342254627803^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245176509 10000000000 1342254627803 3125000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1009571907/5000000000 : ℝ), (2705757193/5000000000 : ℝ), (5245176509/10000000000 : ℝ)] ![(6151555318619/50000000000000 : ℝ), (44744741266587/100000000000000 : ℝ), (1342254627803/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1009571907/5000000000 : ℝ)|^4331 ≤ (6151555318619/50000000000000 : ℝ)^3307
        have hw : |(-1009571907/5000000000 : ℝ)|=(1009571907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705757193/5000000000 : ℝ)|^4331 ≤ (44744741266587/100000000000000 : ℝ)^3307
        have hw : |(2705757193/5000000000 : ℝ)|=(2705757193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245176509/10000000000 : ℝ)|^4331 ≤ (1342254627803/3125000000000 : ℝ)^3307
        have hw : |(5245176509/10000000000 : ℝ)|=(5245176509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s5_1 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348556567/10000000000 : ℝ)*x 0 + (-2103877167/10000000000 : ℝ)*x 1 + (209807059/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348556567/10000000000 : ℝ)^4331 ≤ (1377006871463/3125000000000 : ℝ)^3307 := by
    have hnat : (5348556567 : ℕ)^4331*3125000000000^3307 ≤ 1377006871463^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348556567 10000000000 1377006871463 3125000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2103877167/10000000000 : ℝ)^4331 ≤ (649181618829/5000000000000 : ℝ)^3307 := by
    have hnat : (2103877167 : ℕ)^4331*5000000000000^3307 ≤ 649181618829^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103877167 10000000000 649181618829 5000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209807059/400000000 : ℝ)^4331 ≤ (42952147725061/100000000000000 : ℝ)^3307 := by
    have hnat : (209807059 : ℕ)^4331*100000000000000^3307 ≤ 42952147725061^3307*400000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209807059 400000000 42952147725061 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348556567/10000000000 : ℝ), (-2103877167/10000000000 : ℝ), (209807059/400000000 : ℝ)] ![(1377006871463/3125000000000 : ℝ), (649181618829/5000000000000 : ℝ), (42952147725061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348556567/10000000000 : ℝ)|^4331 ≤ (1377006871463/3125000000000 : ℝ)^3307
        have hw : |(5348556567/10000000000 : ℝ)|=(5348556567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2103877167/10000000000 : ℝ)|^4331 ≤ (649181618829/5000000000000 : ℝ)^3307
        have hw : |(-2103877167/10000000000 : ℝ)|=(2103877167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209807059/400000000 : ℝ)|^4331 ≤ (42952147725061/100000000000000 : ℝ)^3307
        have hw : |(209807059/400000000 : ℝ)|=(209807059/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s5_2 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334284789/625000000 : ℝ)*x 0 + (5245176497/10000000000 : ℝ)*x 1 + (-2103877061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334284789/625000000 : ℝ)^4331 ≤ (44064220501821/100000000000000 : ℝ)^3307 := by
    have hnat : (334284789 : ℕ)^4331*100000000000000^3307 ≤ 44064220501821^3307*625000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334284789 625000000 44064220501821 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245176497/10000000000 : ℝ)^4331 ≤ (42952147961001/100000000000000 : ℝ)^3307 := by
    have hnat : (5245176497 : ℕ)^4331*100000000000000^3307 ≤ 42952147961001^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245176497 10000000000 42952147961001 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2103877061/10000000000 : ℝ)^4331 ≤ (12983631519867/100000000000000 : ℝ)^3307 := by
    have hnat : (2103877061 : ℕ)^4331*100000000000000^3307 ≤ 12983631519867^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103877061 10000000000 12983631519867 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334284789/625000000 : ℝ), (5245176497/10000000000 : ℝ), (-2103877061/10000000000 : ℝ)] ![(44064220501821/100000000000000 : ℝ), (42952147961001/100000000000000 : ℝ), (12983631519867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334284789/625000000 : ℝ)|^4331 ≤ (44064220501821/100000000000000 : ℝ)^3307
        have hw : |(334284789/625000000 : ℝ)|=(334284789/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245176497/10000000000 : ℝ)|^4331 ≤ (42952147961001/100000000000000 : ℝ)^3307
        have hw : |(5245176497/10000000000 : ℝ)|=(5245176497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2103877061/10000000000 : ℝ)|^4331 ≤ (12983631519867/100000000000000 : ℝ)^3307
        have hw : |(-2103877061/10000000000 : ℝ)|=(2103877061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s5_3 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4319072119/10000000000 : ℝ)*x 0 + (2073139521/5000000000 : ℝ)*x 1 + (1124622629/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319072119/10000000000 : ℝ)^4331 ≤ (16651773639501/50000000000000 : ℝ)^3307 := by
    have hnat : (4319072119 : ℕ)^4331*50000000000000^3307 ≤ 16651773639501^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319072119 10000000000 16651773639501 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2073139521/5000000000 : ℝ)^4331 ≤ (6313903440287/20000000000000 : ℝ)^3307 := by
    have hnat : (2073139521 : ℕ)^4331*20000000000000^3307 ≤ 6313903440287^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073139521 5000000000 6313903440287 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124622629/2500000000 : ℝ)^4331 ≤ (35126935501201/100000000000000 : ℝ)^3307 := by
    have hnat : (1124622629 : ℕ)^4331*100000000000000^3307 ≤ 35126935501201^3307*2500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124622629 2500000000 35126935501201 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319072119/10000000000 : ℝ), (2073139521/5000000000 : ℝ), (1124622629/2500000000 : ℝ)] ![(16651773639501/50000000000000 : ℝ), (6313903440287/20000000000000 : ℝ), (35126935501201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319072119/10000000000 : ℝ)|^4331 ≤ (16651773639501/50000000000000 : ℝ)^3307
        have hw : |(4319072119/10000000000 : ℝ)|=(4319072119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2073139521/5000000000 : ℝ)|^4331 ≤ (6313903440287/20000000000000 : ℝ)^3307
        have hw : |(2073139521/5000000000 : ℝ)|=(2073139521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124622629/2500000000 : ℝ)|^4331 ≤ (35126935501201/100000000000000 : ℝ)^3307
        have hw : |(1124622629/2500000000 : ℝ)|=(1124622629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s5_4 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1009578047/5000000000 : ℝ)*x 0 + (5245775069/10000000000 : ℝ)*x 1 + (5410912513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1009578047/5000000000 : ℝ)^4331 ≤ (12303208631453/100000000000000 : ℝ)^3307 := by
    have hnat : (1009578047 : ℕ)^4331*100000000000000^3307 ≤ 12303208631453^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009578047 5000000000 12303208631453 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245775069/10000000000 : ℝ)^4331 ≤ (5369820935649/12500000000000 : ℝ)^3307 := by
    have hnat : (5245775069 : ℕ)^4331*12500000000000^3307 ≤ 5369820935649^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245775069 10000000000 5369820935649 12500000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410912513/10000000000 : ℝ)^4331 ≤ (44738223863899/100000000000000 : ℝ)^3307 := by
    have hnat : (5410912513 : ℕ)^4331*100000000000000^3307 ≤ 44738223863899^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410912513 10000000000 44738223863899 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1009578047/5000000000 : ℝ), (5245775069/10000000000 : ℝ), (5410912513/10000000000 : ℝ)] ![(12303208631453/100000000000000 : ℝ), (5369820935649/12500000000000 : ℝ), (44738223863899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1009578047/5000000000 : ℝ)|^4331 ≤ (12303208631453/100000000000000 : ℝ)^3307
        have hw : |(-1009578047/5000000000 : ℝ)|=(1009578047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245775069/10000000000 : ℝ)|^4331 ≤ (5369820935649/12500000000000 : ℝ)^3307
        have hw : |(5245775069/10000000000 : ℝ)|=(5245775069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410912513/10000000000 : ℝ)|^4331 ≤ (44738223863899/100000000000000 : ℝ)^3307
        have hw : |(5410912513/10000000000 : ℝ)|=(5410912513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s5_5 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652786181/5000000000 : ℝ)*x 0 + (-484535271/2500000000 : ℝ)*x 1 + (1352728019/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652786181/5000000000 : ℝ)^4331 ≤ (2180050881421/5000000000000 : ℝ)^3307 := by
    have hnat : (2652786181 : ℕ)^4331*5000000000000^3307 ≤ 2180050881421^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652786181 5000000000 2180050881421 5000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (484535271/2500000000 : ℝ)^4331 ≤ (11660763234169/100000000000000 : ℝ)^3307 := by
    have hnat : (484535271 : ℕ)^4331*100000000000000^3307 ≤ 11660763234169^3307*2500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484535271 2500000000 11660763234169 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352728019/2500000000 : ℝ)^4331 ≤ (44738219131911/100000000000000 : ℝ)^3307 := by
    have hnat : (1352728019 : ℕ)^4331*100000000000000^3307 ≤ 44738219131911^3307*2500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352728019 2500000000 44738219131911 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652786181/5000000000 : ℝ), (-484535271/2500000000 : ℝ), (1352728019/2500000000 : ℝ)] ![(2180050881421/5000000000000 : ℝ), (11660763234169/100000000000000 : ℝ), (44738219131911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652786181/5000000000 : ℝ)|^4331 ≤ (2180050881421/5000000000000 : ℝ)^3307
        have hw : |(2652786181/5000000000 : ℝ)|=(2652786181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-484535271/2500000000 : ℝ)|^4331 ≤ (11660763234169/100000000000000 : ℝ)^3307
        have hw : |(-484535271/2500000000 : ℝ)|=(484535271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352728019/2500000000 : ℝ)|^4331 ≤ (44738219131911/100000000000000 : ℝ)^3307
        have hw : |(1352728019/2500000000 : ℝ)|=(1352728019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s5_6 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33159831/62500000 : ℝ)*x 0 + (5410911313/10000000000 : ℝ)*x 1 + (-969070657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33159831/62500000 : ℝ)^4331 ≤ (5450128008059/12500000000000 : ℝ)^3307 := by
    have hnat : (33159831 : ℕ)^4331*12500000000000^3307 ≤ 5450128008059^3307*62500000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33159831 62500000 5450128008059 12500000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410911313/10000000000 : ℝ)^4331 ≤ (22369105434941/50000000000000 : ℝ)^3307 := by
    have hnat : (5410911313 : ℕ)^4331*50000000000000^3307 ≤ 22369105434941^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410911313 10000000000 22369105434941 50000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (969070657/5000000000 : ℝ)^4331 ≤ (11660765046441/100000000000000 : ℝ)^3307 := by
    have hnat : (969070657 : ℕ)^4331*100000000000000^3307 ≤ 11660765046441^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969070657 5000000000 11660765046441 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33159831/62500000 : ℝ), (5410911313/10000000000 : ℝ), (-969070657/5000000000 : ℝ)] ![(5450128008059/12500000000000 : ℝ), (22369105434941/50000000000000 : ℝ), (11660765046441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33159831/62500000 : ℝ)|^4331 ≤ (5450128008059/12500000000000 : ℝ)^3307
        have hw : |(33159831/62500000 : ℝ)|=(33159831/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410911313/10000000000 : ℝ)|^4331 ≤ (22369105434941/50000000000000 : ℝ)^3307
        have hw : |(5410911313/10000000000 : ℝ)|=(5410911313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-969070657/5000000000 : ℝ)|^4331 ≤ (11660765046441/100000000000000 : ℝ)^3307
        have hw : |(-969070657/5000000000 : ℝ)|=(969070657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s5_7 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (863819601/2000000000 : ℝ)*x 0 + (4497221929/10000000000 : ℝ)*x 1 + (414755373/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863819601/2000000000 : ℝ)^4331 ≤ (4162976085913/12500000000000 : ℝ)^3307 := by
    have hnat : (863819601 : ℕ)^4331*12500000000000^3307 ≤ 4162976085913^3307*2000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863819601 2000000000 4162976085913 12500000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4497221929/10000000000 : ℝ)^4331 ≤ (35113962850147/100000000000000 : ℝ)^3307 := by
    have hnat : (4497221929 : ℕ)^4331*100000000000000^3307 ≤ 35113962850147^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497221929 10000000000 35113962850147 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (414755373/1000000000 : ℝ)^4331 ≤ (31582228442911/100000000000000 : ℝ)^3307 := by
    have hnat : (414755373 : ℕ)^4331*100000000000000^3307 ≤ 31582228442911^3307*1000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414755373 1000000000 31582228442911 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863819601/2000000000 : ℝ), (4497221929/10000000000 : ℝ), (414755373/1000000000 : ℝ)] ![(4162976085913/12500000000000 : ℝ), (35113962850147/100000000000000 : ℝ), (31582228442911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863819601/2000000000 : ℝ)|^4331 ≤ (4162976085913/12500000000000 : ℝ)^3307
        have hw : |(863819601/2000000000 : ℝ)|=(863819601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4497221929/10000000000 : ℝ)|^4331 ≤ (35113962850147/100000000000000 : ℝ)^3307
        have hw : |(4497221929/10000000000 : ℝ)|=(4497221929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(414755373/1000000000 : ℝ)|^4331 ≤ (31582228442911/100000000000000 : ℝ)^3307
        have hw : |(414755373/1000000000 : ℝ)|=(414755373/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s5_8 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-16964097/5000000000 : ℝ)*x 0 + (47101749/80000000 : ℝ)*x 1 + (5887813321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16964097/5000000000 : ℝ)^4331 ≤ (58332185499/100000000000000 : ℝ)^3307 := by
    have hnat : (16964097 : ℕ)^4331*100000000000000^3307 ≤ 58332185499^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16964097 5000000000 58332185499 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (47101749/80000000 : ℝ)^4331 ≤ (49970307611629/100000000000000 : ℝ)^3307 := by
    have hnat : (47101749 : ℕ)^4331*100000000000000^3307 ≤ 49970307611629^3307*80000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47101749 80000000 49970307611629 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5887813321/10000000000 : ℝ)^4331 ≤ (49971360183309/100000000000000 : ℝ)^3307 := by
    have hnat : (5887813321 : ℕ)^4331*100000000000000^3307 ≤ 49971360183309^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5887813321 10000000000 49971360183309 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16964097/5000000000 : ℝ), (47101749/80000000 : ℝ), (5887813321/10000000000 : ℝ)] ![(58332185499/100000000000000 : ℝ), (49970307611629/100000000000000 : ℝ), (49971360183309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16964097/5000000000 : ℝ)|^4331 ≤ (58332185499/100000000000000 : ℝ)^3307
        have hw : |(-16964097/5000000000 : ℝ)|=(16964097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(47101749/80000000 : ℝ)|^4331 ≤ (49970307611629/100000000000000 : ℝ)^3307
        have hw : |(47101749/80000000 : ℝ)|=(47101749/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5887813321/10000000000 : ℝ)|^4331 ≤ (49971360183309/100000000000000 : ℝ)^3307
        have hw : |(5887813321/10000000000 : ℝ)|=(5887813321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s5_9 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (64006819/625000000 : ℝ)*x 0 + (-1059592421/2500000000 : ℝ)*x 1 + (3490245473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64006819/625000000 : ℝ)^4331 ≤ (5057125038267/100000000000000 : ℝ)^3307 := by
    have hnat : (64006819 : ℕ)^4331*100000000000000^3307 ≤ 5057125038267^3307*625000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64006819 625000000 5057125038267 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059592421/2500000000 : ℝ)^4331 ≤ (6498189381023/20000000000000 : ℝ)^3307 := by
    have hnat : (1059592421 : ℕ)^4331*20000000000000^3307 ≤ 6498189381023^3307*2500000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059592421 2500000000 6498189381023 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3490245473/5000000000 : ℝ)^4331 ≤ (62451928038259/100000000000000 : ℝ)^3307 := by
    have hnat : (3490245473 : ℕ)^4331*100000000000000^3307 ≤ 62451928038259^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3490245473 5000000000 62451928038259 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(64006819/625000000 : ℝ), (-1059592421/2500000000 : ℝ), (3490245473/5000000000 : ℝ)] ![(5057125038267/100000000000000 : ℝ), (6498189381023/20000000000000 : ℝ), (62451928038259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(64006819/625000000 : ℝ)|^4331 ≤ (5057125038267/100000000000000 : ℝ)^3307
        have hw : |(64006819/625000000 : ℝ)|=(64006819/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1059592421/2500000000 : ℝ)|^4331 ≤ (6498189381023/20000000000000 : ℝ)^3307
        have hw : |(-1059592421/2500000000 : ℝ)|=(1059592421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3490245473/5000000000 : ℝ)|^4331 ≤ (62451928038259/100000000000000 : ℝ)^3307
        have hw : |(3490245473/5000000000 : ℝ)|=(3490245473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1371_s5_10 (p : ℝ) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1460787341/10000000000 : ℝ)*x 0 + (2893798767/5000000000 : ℝ)*x 1 + (328612659/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1460787341/10000000000 : ℝ)^4331 ≤ (1006501771403/12500000000000 : ℝ)^3307 := by
    have hnat : (1460787341 : ℕ)^4331*12500000000000^3307 ≤ 1006501771403^3307*10000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1460787341 10000000000 1006501771403 12500000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2893798767/5000000000 : ℝ)^4331 ≤ (9772075767309/20000000000000 : ℝ)^3307 := by
    have hnat : (2893798767 : ℕ)^4331*20000000000000^3307 ≤ 9772075767309^3307*5000000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2893798767 5000000000 9772075767309 20000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328612659/625000000 : ℝ)^4331 ≤ (43087606973957/100000000000000 : ℝ)^3307 := by
    have hnat : (328612659 : ℕ)^4331*100000000000000^3307 ≤ 43087606973957^3307*625000000^4331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328612659 625000000 43087606973957 100000000000000 4331 3307 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4331/1024 : ℝ)) 4331 3307 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1460787341/10000000000 : ℝ), (2893798767/5000000000 : ℝ), (328612659/625000000 : ℝ)] ![(1006501771403/12500000000000 : ℝ), (9772075767309/20000000000000 : ℝ), (43087606973957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1460787341/10000000000 : ℝ)|^4331 ≤ (1006501771403/12500000000000 : ℝ)^3307
        have hw : |(1460787341/10000000000 : ℝ)|=(1460787341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2893798767/5000000000 : ℝ)|^4331 ≤ (9772075767309/20000000000000 : ℝ)^3307
        have hw : |(2893798767/5000000000 : ℝ)|=(2893798767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328612659/625000000 : ℝ)|^4331 ≤ (43087606973957/100000000000000 : ℝ)^3307
        have hw : |(328612659/625000000 : ℝ)|=(328612659/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1371_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155872451/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5587/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11209/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14731/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14769/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5587/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14769/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5587/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14769/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5587/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14769/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5587/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14769/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5587/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14769/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5587/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5587/50000 : ℝ) ^ (2165/512 : ℝ) ≤ (4723952054423087/50000000000000000000 : ℝ) := by
    have hpowers : (5587/50000 : ℝ)^2165 ≤ (4723952054423087/50000000000000000000 : ℝ)^512 := by
      have hnat : (5587 : ℕ)^2165*50000000000000000000^512 ≤ 4723952054423087^512*50000^2165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5587 50000 4723952054423087 50000000000000000000 2165 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5587/50000 : ℝ)) (X := (4723952054423087/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14769/100000 : ℝ) ^ (2165/512 : ℝ) ≤ (1229272308765833/4000000000000000000 : ℝ) := by
    have hpowers : (14769/100000 : ℝ)^2165 ≤ (1229272308765833/4000000000000000000 : ℝ)^512 := by
      have hnat : (14769 : ℕ)^2165*4000000000000000000^512 ≤ 1229272308765833^512*100000^2165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14769 100000 1229272308765833 4000000000000000000 2165 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14769/100000 : ℝ)) (X := (1229272308765833/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004723952054423087/25000000000000000000 : ℝ) ≤ (312513963562351/312500000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (25004723952054423087/25000000000000000000 : ℝ)^512 ≤ (312513963562351/312500000000000 : ℝ)^2165 := by
      have hnat : (25004723952054423087 : ℕ)^512*312500000000000^2165 ≤ 312513963562351^2165*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004723952054423087 25000000000000000000 312513963562351 312500000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312513963562351/312500000000000 : ℝ)) (X := (25004723952054423087/25000000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040179711827991999/100000000000000000000 : ℝ) ≤ (10000950062711241/10000000000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (100040179711827991999/100000000000000000000 : ℝ)^512 ≤ (10000950062711241/10000000000000000 : ℝ)^2165 := by
      have hnat : (100040179711827991999 : ℕ)^512*10000000000000000^2165 ≤ 10000950062711241^2165*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040179711827991999 100000000000000000000 10000950062711241 10000000000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000950062711241/10000000000000000 : ℝ)) (X := (100040179711827991999/100000000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001229272308765833/2000000000000000000 : ℝ) ≤ (40005813165709/40000000000000 : ℝ) ^ (2165/512 : ℝ) := by
    have hpowers : (2001229272308765833/2000000000000000000 : ℝ)^512 ≤ (40005813165709/40000000000000 : ℝ)^2165 := by
      have hnat : (2001229272308765833 : ℕ)^512*40000000000000^2165 ≤ 40005813165709^2165*2000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001229272308765833 2000000000000000000 40005813165709 40000000000000 512 2165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40005813165709/40000000000000 : ℝ)) (X := (2001229272308765833/2000000000000000000 : ℝ)) (by norm_num) 2165 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4723952054423087/50000000000000000000 : ℝ) ≤ ((8985090053216872477/8987500000000000000 : ℝ)+2*(503228716009/359500000000000 : ℝ)*(5587/50000 : ℝ))^(2165/512 : ℝ) := by
    rw [show (8985090053216872477/8987500000000000000 : ℝ)+2*(503228716009/359500000000000 : ℝ)*(5587/50000 : ℝ)=(312513963562351/312500000000000 : ℝ) by norm_num, show 1+2*(4723952054423087/50000000000000000000 : ℝ)=(25004723952054423087/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1229272308765833/4000000000000000000 : ℝ)+(4723952054423087/50000000000000000000 : ℝ) ≤ ((8985090053216872477/8987500000000000000 : ℝ)+(503228716009/359500000000000 : ℝ)*((14769/100000 : ℝ)+(5587/50000 : ℝ)))^(2165/512 : ℝ) := by
    rw [show (8985090053216872477/8987500000000000000 : ℝ)+(503228716009/359500000000000 : ℝ)*((14769/100000 : ℝ)+(5587/50000 : ℝ))=(10000950062711241/10000000000000000 : ℝ) by norm_num, show 1+(1229272308765833/4000000000000000000 : ℝ)+(4723952054423087/50000000000000000000 : ℝ)=(100040179711827991999/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1229272308765833/4000000000000000000 : ℝ) ≤ ((8985090053216872477/8987500000000000000 : ℝ)+2*(503228716009/359500000000000 : ℝ)*(14769/100000 : ℝ))^(2165/512 : ℝ) := by
    rw [show (8985090053216872477/8987500000000000000 : ℝ)+2*(503228716009/359500000000000 : ℝ)*(14769/100000 : ℝ)=(40005813165709/40000000000000 : ℝ) by norm_num, show 1+2*(1229272308765833/4000000000000000000 : ℝ)=(2001229272308765833/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8985090053216872477/8987500000000000000 : ℝ)*(X 1 0+X 2 0)+(503228716009/359500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (5587/50000 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (8985090053216872477/8987500000000000000 : ℝ)) (alpha := (503228716009/359500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8985090053216872477/8987500000000000000 : ℝ)*(X 0 1+X 2 1)+(503228716009/359500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (5587/50000 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (8985090053216872477/8987500000000000000 : ℝ)) (alpha := (503228716009/359500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8985090053216872477/8987500000000000000 : ℝ)*(X 0 2+X 1 2)+(503228716009/359500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2165/512 : ℝ)) (lo := (5587/50000 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (8985090053216872477/8987500000000000000 : ℝ)) (alpha := (503228716009/359500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1009571907/5000000000 : ℝ)*X 0 0+(2705757193/5000000000 : ℝ)*X 0 1+(5245176509/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348556567/10000000000 : ℝ)*X 1 0+(-2103877167/10000000000 : ℝ)*X 1 1+(209807059/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334284789/625000000 : ℝ)*X 2 0+(5245176497/10000000000 : ℝ)*X 2 1+(-2103877061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4319072119/10000000000 : ℝ)*X 0 0+(2073139521/5000000000 : ℝ)*X 0 1+(1124622629/2500000000 : ℝ)*X 0 2+(4319072119/10000000000 : ℝ)*X 1 0+(2073139521/5000000000 : ℝ)*X 1 1+(1124622629/2500000000 : ℝ)*X 1 2+(4319072119/10000000000 : ℝ)*X 2 0+(2073139521/5000000000 : ℝ)*X 2 1+(1124622629/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1009578047/5000000000 : ℝ)*X 0 0+(5245775069/10000000000 : ℝ)*X 0 1+(5410912513/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652786181/5000000000 : ℝ)*X 1 0+(-484535271/2500000000 : ℝ)*X 1 1+(1352728019/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((33159831/62500000 : ℝ)*X 2 0+(5410911313/10000000000 : ℝ)*X 2 1+(-969070657/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((863819601/2000000000 : ℝ)*X 0 0+(4497221929/10000000000 : ℝ)*X 0 1+(414755373/1000000000 : ℝ)*X 0 2+(863819601/2000000000 : ℝ)*X 1 0+(4497221929/10000000000 : ℝ)*X 1 1+(414755373/1000000000 : ℝ)*X 1 2+(863819601/2000000000 : ℝ)*X 2 0+(4497221929/10000000000 : ℝ)*X 2 1+(414755373/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-16964097/5000000000 : ℝ)*X 0 0+(47101749/80000000 : ℝ)*X 0 1+(5887813321/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s5_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((64006819/625000000 : ℝ)*X 1 0+(-1059592421/2500000000 : ℝ)*X 1 1+(3490245473/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s5_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1460787341/10000000000 : ℝ)*X 0 0+(2893798767/5000000000 : ℝ)*X 0 1+(328612659/625000000 : ℝ)*X 0 2+(1460787341/10000000000 : ℝ)*X 1 0+(2893798767/5000000000 : ℝ)*X 1 1+(328612659/625000000 : ℝ)*X 1 2+(1460787341/10000000000 : ℝ)*X 2 0+(2893798767/5000000000 : ℝ)*X 2 1+(328612659/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1371_s5_10 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1858700239723740059431179933/112343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54407403/6250000000000 : ℝ)*(lower2) + (113240493/100000000000000 : ℝ)*(lower3) + (390294843/100000000000000 : ℝ)*(lower4) + (192804181/100000000000000 : ℝ)*(lower5) + (2212762880806557/50000000000000 : ℝ)*(major0) + (2212762880806557/50000000000000 : ℝ)*(major1) + (2212762880806557/50000000000000 : ℝ)*(major2) + (1502962048873309/25000000000000 : ℝ)*(sp0) + (3005922953518153/50000000000000 : ℝ)*(sp1) + (6011854094273779/100000000000000 : ℝ)*(sp2) + (1419598438730239/50000000000000 : ℝ)*(sp3) + (722783687/10000000000000 : ℝ)*(sp5) + (46084223/781250000000 : ℝ)*(sp8) + (239850151/25000000000000 : ℝ)*(sp9) + (1419598438730239/50000000000000 : ℝ)*(f.failure) + (6011854094273779/100000000000000 : ℝ)*(f.sum) + (22559285154269/4493750000000000000000000000 : ℝ)*base65 + (4223365870837631/625000000000000000000000000000 : ℝ)*base67 + (376103855837631/625000000000000000000000000000 : ℝ)*base69 + (4217245265837631/625000000000000000000000000000 : ℝ)*base71 + (2231640501061/1123437500000000000000000000 : ℝ)*base73 + (3684930585412369/625000000000000000000000000000 : ℝ)*base76 + (30642148492087631/625000000000000000000000000000 : ℝ)*base77 + (5962086453962631/625000000000000000000000000000 : ℝ)*base79 + (91494241601749/17975000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (19254211/5000000000000000000000 : ℝ)*base90 + (19254211/5000000000000000000000 : ℝ)*base92 + (19254211/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (444756327131052158877481359/224687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (160586267/50000000000000 : ℝ)*(lower2) + (290728683/100000000000000 : ℝ)*(lower3) + (571757029/100000000000000 : ℝ)*(lower5) + (2228868147655863/50000000000000 : ℝ)*(major0) + (2228868147655863/50000000000000 : ℝ)*(major1) + (2228868147655863/50000000000000 : ℝ)*(major2) + (10728304911/50000000000000 : ℝ)*(sp0) + (4763726891/50000000000000 : ℝ)*(sp1) + (3027792411852931/50000000000000 : ℝ)*(sp4) + (1211120289165603/20000000000000 : ℝ)*(sp5) + (6055610973281797/100000000000000 : ℝ)*(sp6) + (1429929780596767/50000000000000 : ℝ)*(sp7) + (4692966113/100000000000000 : ℝ)*(sp8) + (24877083/1250000000000 : ℝ)*(sp10) + (1429930775680087/50000000000000 : ℝ)*(f.failure) + (6055610973281797/100000000000000 : ℝ)*(f.sum) + (29377435984083/8987500000000000000000000000 : ℝ)*base66 + (3789762475177771/625000000000000000000000000000 : ℝ)*base68 + (11437354110177771/625000000000000000000000000000 : ℝ)*base70 + (14717219033302771/625000000000000000000000000000 : ℝ)*base72 + (155820254995167/8987500000000000000000000000 : ℝ)*base73 + (9059525180802771/625000000000000000000000000000 : ℝ)*base76 + (11922844843302771/625000000000000000000000000000 : ℝ)*base78 + (15358300641427771/625000000000000000000000000000 : ℝ)*base80 + (639574251763/561718750000000000000000000 : ℝ)*base82 + (52583237/5000000000000000000000 : ℝ)*base89 + (52583237/5000000000000000000000 : ℝ)*base91 + (52583237/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1371_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155872451/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5587/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11209/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1371_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1371_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155872451/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7997/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2007/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11209/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1371_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1371_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1371_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2165/512 : ℝ) ≤ p) (hpb : p ≤ (4331/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155872451/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7997/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2007/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11209/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1371_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
