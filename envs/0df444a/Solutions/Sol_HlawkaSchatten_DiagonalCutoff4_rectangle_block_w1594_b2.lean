-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1594_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:37:43.290074+00:00
-- url     : https://prove2.me/submissions/5ddf6587-80c9-48ad-b535-45c794db80e0

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
theorem support_rectangle_w1594_box_0 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-366352727/2500000000 : ℝ)*x 0 + (84722219/156250000 : ℝ)*x 1 + (1084444403/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (366352727/2500000000 : ℝ)^4695 ≤ (8576489935563/100000000000000 : ℝ)^3671 := by
    have hnat : (366352727 : ℕ)^4695*100000000000000^3671 ≤ 8576489935563^3671*2500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366352727 2500000000 8576489935563 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84722219/156250000 : ℝ)^4695 ≤ (45711755029703/100000000000000 : ℝ)^3671 := by
    have hnat : (84722219 : ℕ)^4695*100000000000000^3671 ≤ 45711755029703^3671*156250000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84722219 156250000 45711755029703 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084444403/2000000000 : ℝ)^4695 ≤ (45711755018921/100000000000000 : ℝ)^3671 := by
    have hnat : (1084444403 : ℕ)^4695*100000000000000^3671 ≤ 45711755018921^3671*2000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084444403 2000000000 45711755018921 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-366352727/2500000000 : ℝ), (84722219/156250000 : ℝ), (1084444403/2000000000 : ℝ)] ![(8576489935563/100000000000000 : ℝ), (45711755029703/100000000000000 : ℝ), (45711755018921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-366352727/2500000000 : ℝ)|^4695 ≤ (8576489935563/100000000000000 : ℝ)^3671
        have hw : |(-366352727/2500000000 : ℝ)|=(366352727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84722219/156250000 : ℝ)|^4695 ≤ (45711755029703/100000000000000 : ℝ)^3671
        have hw : |(84722219/156250000 : ℝ)|=(84722219/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084444403/2000000000 : ℝ)|^4695 ≤ (45711755018921/100000000000000 : ℝ)^3671
        have hw : |(1084444403/2000000000 : ℝ)|=(1084444403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_box_1 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250874557/10000000000 : ℝ)*x 0 + (-852917391/5000000000 : ℝ)*x 1 + (5422222019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250874557/10000000000 : ℝ)^4695 ≤ (8774496300937/20000000000000 : ℝ)^3671 := by
    have hnat : (5250874557 : ℕ)^4695*20000000000000^3671 ≤ 8774496300937^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250874557 10000000000 8774496300937 20000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (852917391/5000000000 : ℝ)^4695 ≤ (5207881707409/50000000000000 : ℝ)^3671 := by
    have hnat : (852917391 : ℕ)^4695*50000000000000^3671 ≤ 5207881707409^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852917391 5000000000 5207881707409 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422222019/10000000000 : ℝ)^4695 ≤ (914235101241/2000000000000 : ℝ)^3671 := by
    have hnat : (5422222019 : ℕ)^4695*2000000000000^3671 ≤ 914235101241^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422222019 10000000000 914235101241 2000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250874557/10000000000 : ℝ), (-852917391/5000000000 : ℝ), (5422222019/10000000000 : ℝ)] ![(8774496300937/20000000000000 : ℝ), (5207881707409/50000000000000 : ℝ), (914235101241/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250874557/10000000000 : ℝ)|^4695 ≤ (8774496300937/20000000000000 : ℝ)^3671
        have hw : |(5250874557/10000000000 : ℝ)|=(5250874557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-852917391/5000000000 : ℝ)|^4695 ≤ (5207881707409/50000000000000 : ℝ)^3671
        have hw : |(-852917391/5000000000 : ℝ)|=(852917391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422222019/10000000000 : ℝ)|^4695 ≤ (914235101241/2000000000000 : ℝ)^3671
        have hw : |(5422222019/10000000000 : ℝ)|=(5422222019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_box_2 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250874561/10000000000 : ℝ)*x 0 + (1355555503/2500000000 : ℝ)*x 1 + (-1705834787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250874561/10000000000 : ℝ)^4695 ≤ (43872481547429/100000000000000 : ℝ)^3671 := by
    have hnat : (5250874561 : ℕ)^4695*100000000000000^3671 ≤ 43872481547429^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250874561 10000000000 43872481547429 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355555503/2500000000 : ℝ)^4695 ≤ (1828470199463/4000000000000 : ℝ)^3671 := by
    have hnat : (1355555503 : ℕ)^4695*4000000000000^3671 ≤ 1828470199463^3671*2500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355555503 2500000000 1828470199463 4000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1705834787/10000000000 : ℝ)^4695 ≤ (1301970431733/12500000000000 : ℝ)^3671 := by
    have hnat : (1705834787 : ℕ)^4695*12500000000000^3671 ≤ 1301970431733^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1705834787 10000000000 1301970431733 12500000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250874561/10000000000 : ℝ), (1355555503/2500000000 : ℝ), (-1705834787/10000000000 : ℝ)] ![(43872481547429/100000000000000 : ℝ), (1828470199463/4000000000000 : ℝ), (1301970431733/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250874561/10000000000 : ℝ)|^4695 ≤ (43872481547429/100000000000000 : ℝ)^3671
        have hw : |(5250874561/10000000000 : ℝ)|=(5250874561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355555503/2500000000 : ℝ)|^4695 ≤ (1828470199463/4000000000000 : ℝ)^3671
        have hw : |(1355555503/2500000000 : ℝ)|=(1355555503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1705834787/10000000000 : ℝ)|^4695 ≤ (1301970431733/12500000000000 : ℝ)^3671
        have hw : |(-1705834787/10000000000 : ℝ)|=(1705834787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_box_3 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2253634607/5000000000 : ℝ)*x 0 + (4098323953/10000000000 : ℝ)*x 1 + (4098323949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2253634607/5000000000 : ℝ)^4695 ≤ (36089018307389/100000000000000 : ℝ)^3671 := by
    have hnat : (2253634607 : ℕ)^4695*100000000000000^3671 ≤ 36089018307389^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253634607 5000000000 36089018307389 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4098323953/10000000000 : ℝ)^4695 ≤ (7988872715337/25000000000000 : ℝ)^3671 := by
    have hnat : (4098323953 : ℕ)^4695*25000000000000^3671 ≤ 7988872715337^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4098323953 10000000000 7988872715337 25000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4098323949/10000000000 : ℝ)^4695 ≤ (31955490821459/100000000000000 : ℝ)^3671 := by
    have hnat : (4098323949 : ℕ)^4695*100000000000000^3671 ≤ 31955490821459^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4098323949 10000000000 31955490821459 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2253634607/5000000000 : ℝ), (4098323953/10000000000 : ℝ), (4098323949/10000000000 : ℝ)] ![(36089018307389/100000000000000 : ℝ), (7988872715337/25000000000000 : ℝ), (31955490821459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2253634607/5000000000 : ℝ)|^4695 ≤ (36089018307389/100000000000000 : ℝ)^3671
        have hw : |(2253634607/5000000000 : ℝ)|=(2253634607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4098323953/10000000000 : ℝ)|^4695 ≤ (7988872715337/25000000000000 : ℝ)^3671
        have hw : |(4098323953/10000000000 : ℝ)|=(4098323953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4098323949/10000000000 : ℝ)|^4695 ≤ (31955490821459/100000000000000 : ℝ)^3671
        have hw : |(4098323949/10000000000 : ℝ)|=(4098323949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_box_4 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-509049847/2500000000 : ℝ)*x 0 + (1042612553/2000000000 : ℝ)*x 1 + (2606531629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (509049847/2500000000 : ℝ)^4695 ≤ (2612465196213/20000000000000 : ℝ)^3671 := by
    have hnat : (509049847 : ℕ)^4695*20000000000000^3671 ≤ 2612465196213^3671*2500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509049847 2500000000 2612465196213 20000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042612553/2000000000 : ℝ)^4695 ≤ (10867208593019/25000000000000 : ℝ)^3671 := by
    have hnat : (1042612553 : ℕ)^4695*25000000000000^3671 ≤ 10867208593019^3671*2000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042612553 2000000000 10867208593019 25000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2606531629/5000000000 : ℝ)^4695 ≤ (43468839629623/100000000000000 : ℝ)^3671 := by
    have hnat : (2606531629 : ℕ)^4695*100000000000000^3671 ≤ 43468839629623^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606531629 5000000000 43468839629623 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-509049847/2500000000 : ℝ), (1042612553/2000000000 : ℝ), (2606531629/5000000000 : ℝ)] ![(2612465196213/20000000000000 : ℝ), (10867208593019/25000000000000 : ℝ), (43468839629623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-509049847/2500000000 : ℝ)|^4695 ≤ (2612465196213/20000000000000 : ℝ)^3671
        have hw : |(-509049847/2500000000 : ℝ)|=(509049847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042612553/2000000000 : ℝ)|^4695 ≤ (10867208593019/25000000000000 : ℝ)^3671
        have hw : |(1042612553/2000000000 : ℝ)|=(1042612553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2606531629/5000000000 : ℝ)|^4695 ≤ (43468839629623/100000000000000 : ℝ)^3671
        have hw : |(2606531629/5000000000 : ℝ)|=(2606531629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_box_5 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107911231/200000000 : ℝ)*x 0 + (-448420967/2500000000 : ℝ)*x 1 + (2606531737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107911231/200000000 : ℝ)^4695 ≤ (45424497601231/100000000000000 : ℝ)^3671 := by
    have hnat : (107911231 : ℕ)^4695*100000000000000^3671 ≤ 45424497601231^3671*200000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107911231 200000000 45424497601231 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448420967/2500000000 : ℝ)^4695 ≤ (11106660456813/100000000000000 : ℝ)^3671 := by
    have hnat : (448420967 : ℕ)^4695*100000000000000^3671 ≤ 11106660456813^3671*2500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448420967 2500000000 11106660456813 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2606531737/5000000000 : ℝ)^4695 ≤ (43468841933133/100000000000000 : ℝ)^3671 := by
    have hnat : (2606531737 : ℕ)^4695*100000000000000^3671 ≤ 43468841933133^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606531737 5000000000 43468841933133 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107911231/200000000 : ℝ), (-448420967/2500000000 : ℝ), (2606531737/5000000000 : ℝ)] ![(45424497601231/100000000000000 : ℝ), (11106660456813/100000000000000 : ℝ), (43468841933133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107911231/200000000 : ℝ)|^4695 ≤ (45424497601231/100000000000000 : ℝ)^3671
        have hw : |(107911231/200000000 : ℝ)|=(107911231/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-448420967/2500000000 : ℝ)|^4695 ≤ (11106660456813/100000000000000 : ℝ)^3671
        have hw : |(-448420967/2500000000 : ℝ)|=(448420967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2606531737/5000000000 : ℝ)|^4695 ≤ (43468841933133/100000000000000 : ℝ)^3671
        have hw : |(2606531737/5000000000 : ℝ)|=(2606531737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_box_6 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2697781363/5000000000 : ℝ)*x 0 + (2606531073/5000000000 : ℝ)*x 1 + (-1793684057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2697781363/5000000000 : ℝ)^4695 ≤ (22712255131757/50000000000000 : ℝ)^3671 := by
    have hnat : (2697781363 : ℕ)^4695*50000000000000^3671 ≤ 22712255131757^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697781363 5000000000 22712255131757 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2606531073/5000000000 : ℝ)^4695 ≤ (8693765554163/20000000000000 : ℝ)^3671 := by
    have hnat : (2606531073 : ℕ)^4695*20000000000000^3671 ≤ 8693765554163^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606531073 5000000000 8693765554163 20000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1793684057/10000000000 : ℝ)^4695 ≤ (347083186049/3125000000000 : ℝ)^3671 := by
    have hnat : (1793684057 : ℕ)^4695*3125000000000^3671 ≤ 347083186049^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793684057 10000000000 347083186049 3125000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2697781363/5000000000 : ℝ), (2606531073/5000000000 : ℝ), (-1793684057/10000000000 : ℝ)] ![(22712255131757/50000000000000 : ℝ), (8693765554163/20000000000000 : ℝ), (347083186049/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2697781363/5000000000 : ℝ)|^4695 ≤ (22712255131757/50000000000000 : ℝ)^3671
        have hw : |(2697781363/5000000000 : ℝ)|=(2697781363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2606531073/5000000000 : ℝ)|^4695 ≤ (8693765554163/20000000000000 : ℝ)^3671
        have hw : |(2606531073/5000000000 : ℝ)|=(2606531073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1793684057/10000000000 : ℝ)|^4695 ≤ (347083186049/3125000000000 : ℝ)^3671
        have hw : |(-1793684057/10000000000 : ℝ)|=(1793684057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_box_7 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (123093851/312500000 : ℝ)*x 0 + (4382104401/10000000000 : ℝ)*x 1 + (4382105199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (123093851/312500000 : ℝ)^4695 ≤ (3037541086203/10000000000000 : ℝ)^3671 := by
    have hnat : (123093851 : ℕ)^4695*10000000000000^3671 ≤ 3037541086203^3671*312500000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123093851 312500000 3037541086203 10000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4382104401/10000000000 : ℝ)^4695 ≤ (1740614525421/5000000000000 : ℝ)^3671 := by
    have hnat : (4382104401 : ℕ)^4695*5000000000000^3671 ≤ 1740614525421^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4382104401 10000000000 1740614525421 5000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4382105199/10000000000 : ℝ)^4695 ≤ (17406149308119/50000000000000 : ℝ)^3671 := by
    have hnat : (4382105199 : ℕ)^4695*50000000000000^3671 ≤ 17406149308119^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4382105199 10000000000 17406149308119 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(123093851/312500000 : ℝ), (4382104401/10000000000 : ℝ), (4382105199/10000000000 : ℝ)] ![(3037541086203/10000000000000 : ℝ), (1740614525421/5000000000000 : ℝ), (17406149308119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(123093851/312500000 : ℝ)|^4695 ≤ (3037541086203/10000000000000 : ℝ)^3671
        have hw : |(123093851/312500000 : ℝ)|=(123093851/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4382104401/10000000000 : ℝ)|^4695 ≤ (1740614525421/5000000000000 : ℝ)^3671
        have hw : |(4382104401/10000000000 : ℝ)|=(4382104401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4382105199/10000000000 : ℝ)|^4695 ≤ (17406149308119/50000000000000 : ℝ)^3671
        have hw : |(4382105199/10000000000 : ℝ)|=(4382105199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_box_8 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-95751901/500000000 : ℝ)*x 0 + (1012816517/2000000000 : ℝ)*x 1 + (5452358727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (95751901/500000000 : ℝ)^4695 ≤ (3019157515589/25000000000000 : ℝ)^3671 := by
    have hnat : (95751901 : ℕ)^4695*25000000000000^3671 ≤ 3019157515589^3671*500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95751901 500000000 3019157515589 25000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1012816517/2000000000 : ℝ)^4695 ≤ (20943213735739/50000000000000 : ℝ)^3671 := by
    have hnat : (1012816517 : ℕ)^4695*50000000000000^3671 ≤ 20943213735739^3671*2000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012816517 2000000000 20943213735739 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5452358727/10000000000 : ℝ)^4695 ≤ (46036942455389/100000000000000 : ℝ)^3671 := by
    have hnat : (5452358727 : ℕ)^4695*100000000000000^3671 ≤ 46036942455389^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452358727 10000000000 46036942455389 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-95751901/500000000 : ℝ), (1012816517/2000000000 : ℝ), (5452358727/10000000000 : ℝ)] ![(3019157515589/25000000000000 : ℝ), (20943213735739/50000000000000 : ℝ), (46036942455389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-95751901/500000000 : ℝ)|^4695 ≤ (3019157515589/25000000000000 : ℝ)^3671
        have hw : |(-95751901/500000000 : ℝ)|=(95751901/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1012816517/2000000000 : ℝ)|^4695 ≤ (20943213735739/50000000000000 : ℝ)^3671
        have hw : |(1012816517/2000000000 : ℝ)|=(1012816517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5452358727/10000000000 : ℝ)|^4695 ≤ (46036942455389/100000000000000 : ℝ)^3671
        have hw : |(5452358727/10000000000 : ℝ)|=(5452358727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_box_9 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (209200813/400000000 : ℝ)*x 0 + (-846349819/5000000000 : ℝ)*x 1 + (2726179361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209200813/400000000 : ℝ)^4695 ≤ (8729951696873/20000000000000 : ℝ)^3671 := by
    have hnat : (209200813 : ℕ)^4695*20000000000000^3671 ≤ 8729951696873^3671*400000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209200813 400000000 8729951696873 20000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846349819/5000000000 : ℝ)^4695 ≤ (322290596699/3125000000000 : ℝ)^3671 := by
    have hnat : (846349819 : ℕ)^4695*3125000000000^3671 ≤ 322290596699^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846349819 5000000000 322290596699 3125000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2726179361/5000000000 : ℝ)^4695 ≤ (9207388480279/20000000000000 : ℝ)^3671 := by
    have hnat : (2726179361 : ℕ)^4695*20000000000000^3671 ≤ 9207388480279^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726179361 5000000000 9207388480279 20000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209200813/400000000 : ℝ), (-846349819/5000000000 : ℝ), (2726179361/5000000000 : ℝ)] ![(8729951696873/20000000000000 : ℝ), (322290596699/3125000000000 : ℝ), (9207388480279/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209200813/400000000 : ℝ)|^4695 ≤ (8729951696873/20000000000000 : ℝ)^3671
        have hw : |(209200813/400000000 : ℝ)|=(209200813/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-846349819/5000000000 : ℝ)|^4695 ≤ (322290596699/3125000000000 : ℝ)^3671
        have hw : |(-846349819/5000000000 : ℝ)|=(846349819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2726179361/5000000000 : ℝ)|^4695 ≤ (9207388480279/20000000000000 : ℝ)^3671
        have hw : |(2726179361/5000000000 : ℝ)|=(2726179361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_box_10 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2615010207/5000000000 : ℝ)*x 0 + (5452358713/10000000000 : ℝ)*x 1 + (-169269953/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2615010207/5000000000 : ℝ)^4695 ≤ (43649759434357/100000000000000 : ℝ)^3671 := by
    have hnat : (2615010207 : ℕ)^4695*100000000000000^3671 ≤ 43649759434357^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615010207 5000000000 43649759434357 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5452358713/10000000000 : ℝ)^4695 ≤ (46036942304207/100000000000000 : ℝ)^3671 := by
    have hnat : (5452358713 : ℕ)^4695*100000000000000^3671 ≤ 46036942304207^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452358713 10000000000 46036942304207 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169269953/1000000000 : ℝ)^4695 ≤ (5156649126397/50000000000000 : ℝ)^3671 := by
    have hnat : (169269953 : ℕ)^4695*50000000000000^3671 ≤ 5156649126397^3671*1000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169269953 1000000000 5156649126397 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2615010207/5000000000 : ℝ), (5452358713/10000000000 : ℝ), (-169269953/1000000000 : ℝ)] ![(43649759434357/100000000000000 : ℝ), (46036942304207/100000000000000 : ℝ), (5156649126397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2615010207/5000000000 : ℝ)|^4695 ≤ (43649759434357/100000000000000 : ℝ)^3671
        have hw : |(2615010207/5000000000 : ℝ)|=(2615010207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5452358713/10000000000 : ℝ)|^4695 ≤ (46036942304207/100000000000000 : ℝ)^3671
        have hw : |(5452358713/10000000000 : ℝ)|=(5452358713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-169269953/1000000000 : ℝ)|^4695 ≤ (5156649126397/50000000000000 : ℝ)^3671
        have hw : |(-169269953/1000000000 : ℝ)|=(169269953/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_box_11 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4586741693/10000000000 : ℝ)*x 0 + (4057362397/10000000000 : ℝ)*x 1 + (2028680991/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4586741693/10000000000 : ℝ)^4695 ≤ (18452416717981/50000000000000 : ℝ)^3671 := by
    have hnat : (4586741693 : ℕ)^4695*50000000000000^3671 ≤ 18452416717981^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4586741693 10000000000 18452416717981 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4057362397/10000000000 : ℝ)^4695 ≤ (31547585339093/100000000000000 : ℝ)^3671 := by
    have hnat : (4057362397 : ℕ)^4695*100000000000000^3671 ≤ 31547585339093^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4057362397 10000000000 31547585339093 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2028680991/5000000000 : ℝ)^4695 ≤ (6309516242443/20000000000000 : ℝ)^3671 := by
    have hnat : (2028680991 : ℕ)^4695*20000000000000^3671 ≤ 6309516242443^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028680991 5000000000 6309516242443 20000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4586741693/10000000000 : ℝ), (4057362397/10000000000 : ℝ), (2028680991/5000000000 : ℝ)] ![(18452416717981/50000000000000 : ℝ), (31547585339093/100000000000000 : ℝ), (6309516242443/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4586741693/10000000000 : ℝ)|^4695 ≤ (18452416717981/50000000000000 : ℝ)^3671
        have hw : |(4586741693/10000000000 : ℝ)|=(4586741693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4057362397/10000000000 : ℝ)|^4695 ≤ (31547585339093/100000000000000 : ℝ)^3671
        have hw : |(4057362397/10000000000 : ℝ)|=(4057362397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2028680991/5000000000 : ℝ)|^4695 ≤ (6309516242443/20000000000000 : ℝ)^3671
        have hw : |(2028680991/5000000000 : ℝ)|=(2028680991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_box_12 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1585604143/10000000000 : ℝ)*x 0 + (695623309/1250000000 : ℝ)*x 1 + (162287377/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1585604143/10000000000 : ℝ)^4695 ≤ (4743125901177/50000000000000 : ℝ)^3671 := by
    have hnat : (1585604143 : ℕ)^4695*50000000000000^3671 ≤ 4743125901177^3671*10000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1585604143 10000000000 4743125901177 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (695623309/1250000000 : ℝ)^4695 ≤ (23628333726639/50000000000000 : ℝ)^3671 := by
    have hnat : (695623309 : ℕ)^4695*50000000000000^3671 ≤ 23628333726639^3671*1250000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      695623309 1250000000 23628333726639 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (162287377/312500000 : ℝ)^4695 ≤ (8651416144939/20000000000000 : ℝ)^3671 := by
    have hnat : (162287377 : ℕ)^4695*20000000000000^3671 ≤ 8651416144939^3671*312500000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162287377 312500000 8651416144939 20000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1585604143/10000000000 : ℝ), (695623309/1250000000 : ℝ), (162287377/312500000 : ℝ)] ![(4743125901177/50000000000000 : ℝ), (23628333726639/50000000000000 : ℝ), (8651416144939/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1585604143/10000000000 : ℝ)|^4695 ≤ (4743125901177/50000000000000 : ℝ)^3671
        have hw : |(-1585604143/10000000000 : ℝ)|=(1585604143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(695623309/1250000000 : ℝ)|^4695 ≤ (23628333726639/50000000000000 : ℝ)^3671
        have hw : |(695623309/1250000000 : ℝ)|=(695623309/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(162287377/312500000 : ℝ)|^4695 ≤ (8651416144939/20000000000000 : ℝ)^3671
        have hw : |(162287377/312500000 : ℝ)|=(162287377/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_box_13 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2704655171/5000000000 : ℝ)*x 0 + (-360343739/2000000000 : ℝ)*x 1 + (519319623/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2704655171/5000000000 : ℝ)^4695 ≤ (45572586826267/100000000000000 : ℝ)^3671 := by
    have hnat : (2704655171 : ℕ)^4695*100000000000000^3671 ≤ 45572586826267^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704655171 5000000000 45572586826267 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (360343739/2000000000 : ℝ)^4695 ≤ (2234066133617/20000000000000 : ℝ)^3671 := by
    have hnat : (360343739 : ℕ)^4695*20000000000000^3671 ≤ 2234066133617^3671*2000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360343739 2000000000 2234066133617 20000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519319623/1000000000 : ℝ)^4695 ≤ (43257082493101/100000000000000 : ℝ)^3671 := by
    have hnat : (519319623 : ℕ)^4695*100000000000000^3671 ≤ 43257082493101^3671*1000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519319623 1000000000 43257082493101 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2704655171/5000000000 : ℝ), (-360343739/2000000000 : ℝ), (519319623/1000000000 : ℝ)] ![(45572586826267/100000000000000 : ℝ), (2234066133617/20000000000000 : ℝ), (43257082493101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2704655171/5000000000 : ℝ)|^4695 ≤ (45572586826267/100000000000000 : ℝ)^3671
        have hw : |(2704655171/5000000000 : ℝ)|=(2704655171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-360343739/2000000000 : ℝ)|^4695 ≤ (2234066133617/20000000000000 : ℝ)^3671
        have hw : |(-360343739/2000000000 : ℝ)|=(360343739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(519319623/1000000000 : ℝ)|^4695 ≤ (43257082493101/100000000000000 : ℝ)^3671
        have hw : |(519319623/1000000000 : ℝ)|=(519319623/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_box_14 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1081862127/2000000000 : ℝ)*x 0 + (1298298991/2500000000 : ℝ)*x 1 + (-900859327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081862127/2000000000 : ℝ)^4695 ≤ (45572589983311/100000000000000 : ℝ)^3671 := by
    have hnat : (1081862127 : ℕ)^4695*100000000000000^3671 ≤ 45572589983311^3671*2000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081862127 2000000000 45572589983311 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1298298991/2500000000 : ℝ)^4695 ≤ (43257079659391/100000000000000 : ℝ)^3671 := by
    have hnat : (1298298991 : ℕ)^4695*100000000000000^3671 ≤ 43257079659391^3671*2500000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298298991 2500000000 43257079659391 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900859327/5000000000 : ℝ)^4695 ≤ (11170330342987/100000000000000 : ℝ)^3671 := by
    have hnat : (900859327 : ℕ)^4695*100000000000000^3671 ≤ 11170330342987^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900859327 5000000000 11170330342987 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081862127/2000000000 : ℝ), (1298298991/2500000000 : ℝ), (-900859327/5000000000 : ℝ)] ![(45572589983311/100000000000000 : ℝ), (43257079659391/100000000000000 : ℝ), (11170330342987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081862127/2000000000 : ℝ)|^4695 ≤ (45572589983311/100000000000000 : ℝ)^3671
        have hw : |(1081862127/2000000000 : ℝ)|=(1081862127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1298298991/2500000000 : ℝ)|^4695 ≤ (43257079659391/100000000000000 : ℝ)^3671
        have hw : |(1298298991/2500000000 : ℝ)|=(1298298991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-900859327/5000000000 : ℝ)|^4695 ≤ (11170330342987/100000000000000 : ℝ)^3671
        have hw : |(-900859327/5000000000 : ℝ)|=(900859327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1594_box_15 (p : ℝ) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1941703491/5000000000 : ℝ)*x 0 + (137781637/312500000 : ℝ)*x 1 + (440901199/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1941703491/5000000000 : ℝ)^4695 ≤ (29828175892883/100000000000000 : ℝ)^3671 := by
    have hnat : (1941703491 : ℕ)^4695*100000000000000^3671 ≤ 29828175892883^3671*5000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1941703491 5000000000 29828175892883 100000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137781637/312500000 : ℝ)^4695 ≤ (2192869628351/6250000000000 : ℝ)^3671 := by
    have hnat : (137781637 : ℕ)^4695*6250000000000^3671 ≤ 2192869628351^3671*312500000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137781637 312500000 2192869628351 6250000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (440901199/1000000000 : ℝ)^4695 ≤ (17542955021833/50000000000000 : ℝ)^3671 := by
    have hnat : (440901199 : ℕ)^4695*50000000000000^3671 ≤ 17542955021833^3671*1000000000^4695 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440901199 1000000000 17542955021833 50000000000000 4695 3671 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4695/1024 : ℝ)) 4695 3671 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1941703491/5000000000 : ℝ), (137781637/312500000 : ℝ), (440901199/1000000000 : ℝ)] ![(29828175892883/100000000000000 : ℝ), (2192869628351/6250000000000 : ℝ), (17542955021833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1941703491/5000000000 : ℝ)|^4695 ≤ (29828175892883/100000000000000 : ℝ)^3671
        have hw : |(1941703491/5000000000 : ℝ)|=(1941703491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(137781637/312500000 : ℝ)|^4695 ≤ (2192869628351/6250000000000 : ℝ)^3671
        have hw : |(137781637/312500000 : ℝ)|=(137781637/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(440901199/1000000000 : ℝ)|^4695 ≤ (17542955021833/50000000000000 : ℝ)^3671
        have hw : |(440901199/1000000000 : ℝ)|=(440901199/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1594_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85141271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16367/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (413/4000 : ℝ)*pair X i i ≤ pair X i h) :
    -(64871/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58021/100000 : ℝ) ∧ (20027/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (87659/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16367/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (413/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16367/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (413/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16367/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (413/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16367/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (413/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16367/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (413/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16367/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (413/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (413/4000 : ℝ) ^ (4691/1024 : ℝ) ≤ (1518960368735043/50000000000000000000 : ℝ) := by
    have hpowers : (413/4000 : ℝ)^4691 ≤ (1518960368735043/50000000000000000000 : ℝ)^1024 := by
      have hnat : (413 : ℕ)^4691*50000000000000000000^1024 ≤ 1518960368735043^1024*4000^4691 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        413 4000 1518960368735043 50000000000000000000 4691 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (413/4000 : ℝ)) (X := (1518960368735043/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16367/100000 : ℝ) ^ (4691/1024 : ℝ) ≤ (6267428514465511/25000000000000000000 : ℝ) := by
    have hpowers : (16367/100000 : ℝ)^4691 ≤ (6267428514465511/25000000000000000000 : ℝ)^1024 := by
      have hnat : (16367 : ℕ)^4691*25000000000000000000^1024 ≤ 6267428514465511^1024*100000^4691 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16367 100000 6267428514465511 25000000000000000000 4691 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16367/100000 : ℝ)) (X := (6267428514465511/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001518960368735043/25000000000000000000 : ℝ) ≤ (5000066313301273/5000000000000000 : ℝ) ^ (4691/1024 : ℝ) := by
    have hpowers : (25001518960368735043/25000000000000000000 : ℝ)^1024 ≤ (5000066313301273/5000000000000000 : ℝ)^4691 := by
      have hnat : (25001518960368735043 : ℕ)^1024*5000000000000000^4691 ≤ 5000066313301273^4691*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001518960368735043 25000000000000000000 5000066313301273 5000000000000000 1024 4691 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000066313301273/5000000000000000 : ℝ)) (X := (25001518960368735043/25000000000000000000 : ℝ)) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10002810763479533213/10000000000000000000 : ℝ) ≤ (10000613495129873/10000000000000000 : ℝ) ^ (4691/1024 : ℝ) := by
    have hpowers : (10002810763479533213/10000000000000000000 : ℝ)^1024 ≤ (10000613495129873/10000000000000000 : ℝ)^4691 := by
      have hnat : (10002810763479533213 : ℕ)^1024*10000000000000000^4691 ≤ 10000613495129873^4691*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002810763479533213 10000000000000000000 10000613495129873 10000000000000000 1024 4691 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000613495129873/10000000000000000 : ℝ)) (X := (10002810763479533213/10000000000000000000 : ℝ)) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506267428514465511/12500000000000000000 : ℝ) ≤ (25002735909143/25000000000000 : ℝ) ^ (4691/1024 : ℝ) := by
    have hpowers : (12506267428514465511/12500000000000000000 : ℝ)^1024 ≤ (25002735909143/25000000000000 : ℝ)^4691 := by
      have hnat : (12506267428514465511 : ℕ)^1024*25000000000000^4691 ≤ 25002735909143^4691*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506267428514465511 12500000000000000000 25002735909143 25000000000000 1024 4691 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (25002735909143/25000000000000 : ℝ)) (X := (12506267428514465511/12500000000000000000 : ℝ)) (by norm_num) 4691 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1518960368735043/50000000000000000000 : ℝ) ≤ ((10068478565807213397/10070000000000000000 : ℝ)+2*(160289509109/201400000000000 : ℝ)*(413/4000 : ℝ))^(4691/1024 : ℝ) := by
    rw [show (10068478565807213397/10070000000000000000 : ℝ)+2*(160289509109/201400000000000 : ℝ)*(413/4000 : ℝ)=(5000066313301273/5000000000000000 : ℝ) by norm_num, show 1+2*(1518960368735043/50000000000000000000 : ℝ)=(25001518960368735043/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6267428514465511/25000000000000000000 : ℝ)+(1518960368735043/50000000000000000000 : ℝ) ≤ ((10068478565807213397/10070000000000000000 : ℝ)+(160289509109/201400000000000 : ℝ)*((16367/100000 : ℝ)+(413/4000 : ℝ)))^(4691/1024 : ℝ) := by
    rw [show (10068478565807213397/10070000000000000000 : ℝ)+(160289509109/201400000000000 : ℝ)*((16367/100000 : ℝ)+(413/4000 : ℝ))=(10000613495129873/10000000000000000 : ℝ) by norm_num, show 1+(6267428514465511/25000000000000000000 : ℝ)+(1518960368735043/50000000000000000000 : ℝ)=(10002810763479533213/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6267428514465511/25000000000000000000 : ℝ) ≤ ((10068478565807213397/10070000000000000000 : ℝ)+2*(160289509109/201400000000000 : ℝ)*(16367/100000 : ℝ))^(4691/1024 : ℝ) := by
    rw [show (10068478565807213397/10070000000000000000 : ℝ)+2*(160289509109/201400000000000 : ℝ)*(16367/100000 : ℝ)=(25002735909143/25000000000000 : ℝ) by norm_num, show 1+2*(6267428514465511/25000000000000000000 : ℝ)=(12506267428514465511/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10068478565807213397/10070000000000000000 : ℝ)*(X 1 0+X 2 0)+(160289509109/201400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4691/1024 : ℝ)) (lo := (413/4000 : ℝ)) (hi := (16367/100000 : ℝ)) (c := (10068478565807213397/10070000000000000000 : ℝ)) (alpha := (160289509109/201400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10068478565807213397/10070000000000000000 : ℝ)*(X 0 1+X 2 1)+(160289509109/201400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4691/1024 : ℝ)) (lo := (413/4000 : ℝ)) (hi := (16367/100000 : ℝ)) (c := (10068478565807213397/10070000000000000000 : ℝ)) (alpha := (160289509109/201400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10068478565807213397/10070000000000000000 : ℝ)*(X 0 2+X 1 2)+(160289509109/201400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4691/1024 : ℝ)) (lo := (413/4000 : ℝ)) (hi := (16367/100000 : ℝ)) (c := (10068478565807213397/10070000000000000000 : ℝ)) (alpha := (160289509109/201400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-366352727/2500000000 : ℝ)*X 0 0+(84722219/156250000 : ℝ)*X 0 1+(1084444403/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5250874557/10000000000 : ℝ)*X 1 0+(-852917391/5000000000 : ℝ)*X 1 1+(5422222019/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5250874561/10000000000 : ℝ)*X 2 0+(1355555503/2500000000 : ℝ)*X 2 1+(-1705834787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2253634607/5000000000 : ℝ)*X 0 0+(4098323953/10000000000 : ℝ)*X 0 1+(4098323949/10000000000 : ℝ)*X 0 2+(2253634607/5000000000 : ℝ)*X 1 0+(4098323953/10000000000 : ℝ)*X 1 1+(4098323949/10000000000 : ℝ)*X 1 2+(2253634607/5000000000 : ℝ)*X 2 0+(4098323953/10000000000 : ℝ)*X 2 1+(4098323949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-509049847/2500000000 : ℝ)*X 0 0+(1042612553/2000000000 : ℝ)*X 0 1+(2606531629/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((107911231/200000000 : ℝ)*X 1 0+(-448420967/2500000000 : ℝ)*X 1 1+(2606531737/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2697781363/5000000000 : ℝ)*X 2 0+(2606531073/5000000000 : ℝ)*X 2 1+(-1793684057/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((123093851/312500000 : ℝ)*X 0 0+(4382104401/10000000000 : ℝ)*X 0 1+(4382105199/10000000000 : ℝ)*X 0 2+(123093851/312500000 : ℝ)*X 1 0+(4382104401/10000000000 : ℝ)*X 1 1+(4382105199/10000000000 : ℝ)*X 1 2+(123093851/312500000 : ℝ)*X 2 0+(4382104401/10000000000 : ℝ)*X 2 1+(4382105199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-95751901/500000000 : ℝ)*X 0 0+(1012816517/2000000000 : ℝ)*X 0 1+(5452358727/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((209200813/400000000 : ℝ)*X 1 0+(-846349819/5000000000 : ℝ)*X 1 1+(2726179361/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2615010207/5000000000 : ℝ)*X 2 0+(5452358713/10000000000 : ℝ)*X 2 1+(-169269953/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4586741693/10000000000 : ℝ)*X 0 0+(4057362397/10000000000 : ℝ)*X 0 1+(2028680991/5000000000 : ℝ)*X 0 2+(4586741693/10000000000 : ℝ)*X 1 0+(4057362397/10000000000 : ℝ)*X 1 1+(2028680991/5000000000 : ℝ)*X 1 2+(4586741693/10000000000 : ℝ)*X 2 0+(4057362397/10000000000 : ℝ)*X 2 1+(2028680991/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1585604143/10000000000 : ℝ)*X 0 0+(695623309/1250000000 : ℝ)*X 0 1+(162287377/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2704655171/5000000000 : ℝ)*X 1 0+(-360343739/2000000000 : ℝ)*X 1 1+(519319623/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1081862127/2000000000 : ℝ)*X 2 0+(1298298991/2500000000 : ℝ)*X 2 1+(-900859327/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1941703491/5000000000 : ℝ)*X 0 0+(137781637/312500000 : ℝ)*X 0 1+(440901199/1000000000 : ℝ)*X 0 2+(1941703491/5000000000 : ℝ)*X 1 0+(137781637/312500000 : ℝ)*X 1 1+(440901199/1000000000 : ℝ)*X 1 2+(1941703491/5000000000 : ℝ)*X 2 0+(137781637/312500000 : ℝ)*X 2 1+(440901199/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1594_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-64871/100000 : ℝ) ≤ (-1719024319637565065415382751421/2650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11501261/100000000000000 : ℝ)*(upper0) + (16491937/50000000000000 : ℝ)*(lower2) + (19669649/25000000000000 : ℝ)*(lower3) + (5538499/6250000000000 : ℝ)*(upper5) + (165015233499911/10000000000000 : ℝ)*(major0) + (165015233499911/10000000000000 : ℝ)*(major1) + (165015233499911/10000000000000 : ℝ)*(major2) + (2130014539/20000000000000 : ℝ)*(sp2) + (930314843/100000000000000 : ℝ)*(sp3) + (4705720748913/200000000000 : ℝ)*(sp4) + (73524849737371/3125000000000 : ℝ)*(sp5) + (588212431095951/25000000000000 : ℝ)*(sp6) + (969066312643693/100000000000000 : ℝ)*(sp7) + (16295715157/25000000000000 : ℝ)*(sp13) + (121133405369817/12500000000000 : ℝ)*(f.failure) + (4705720748913/200000000000 : ℝ)*(f.sum) + (113503602687/53000000000000000000000000 : ℝ)*base65 + (21905306116733807/5300000000000000000000000000000 : ℝ)*base68 + (6469915469333807/5300000000000000000000000000000 : ℝ)*base70 + (28822048761333807/5300000000000000000000000000000 : ℝ)*base72 + (756406495573/53000000000000000000000000 : ℝ)*base73 + (28561029739733807/5300000000000000000000000000000 : ℝ)*base76 + (40768195556766193/5300000000000000000000000000000 : ℝ)*base77 + (132988130796066193/5300000000000000000000000000000 : ℝ)*base79 + (9695906573/13250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (6917407/625000000000000000000 : ℝ)*base89 + (6917407/625000000000000000000 : ℝ)*base91 + (6917407/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58021/100000 : ℝ) ≤ (73036972373897816036257303243683/125875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33437/10000000000000 : ℝ)*(lower0) + (228619/100000000000000 : ℝ)*(upper2) + (112973/50000000000000 : ℝ)*(upper3) + (316817/100000000000000 : ℝ)*(lower5) + (433178114236787/25000000000000 : ℝ)*(major0) + (433178114236787/25000000000000 : ℝ)*(major1) + (433178114236787/25000000000000 : ℝ)*(major2) + (1214266168311783/50000000000000 : ℝ)*(sp0) + (1214266150491171/50000000000000 : ℝ)*(sp1) + (242853200846359/10000000000000 : ℝ)*(sp2) + (1017551435341251/100000000000000 : ℝ)*(sp3) + (4455153/12500000000000 : ℝ)*(sp5) + (785821/20000000000000 : ℝ)*(sp7) + (41019997/12500000000000 : ℝ)*(sp10) + (254387859817589/25000000000000 : ℝ)*(f.failure) + (1214266168311783/50000000000000 : ℝ)*(f.sum) + (928260926193/629375000000000000000000000 : ℝ)*base66 + (460296169851214561/251750000000000000000000000000000 : ℝ)*base68 + (761840010013785439/251750000000000000000000000000000 : ℝ)*base69 + (569381871941785439/251750000000000000000000000000000 : ℝ)*base71 + (53394965379777/2517500000000000000000000000 : ℝ)*base74 + (58794102441785439/251750000000000000000000000000000 : ℝ)*base75 + (206843151811785439/251750000000000000000000000000000 : ℝ)*base77 + (392420571447214561/251750000000000000000000000000000 : ℝ)*base80 + (3762800425687/2517500000000000000000000000 : ℝ)*base82 + (5615619/1250000000000000000000 : ℝ)*base89 + (5615619/1250000000000000000000 : ℝ)*base91 + (5615619/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (20027/25000 : ℝ) ≤ (201677090876172370994654509013679/251750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (914547/25000000000000 : ℝ)*(upper1) + (3248091/100000000000000 : ℝ)*(upper3) + (53434187/100000000000000 : ℝ)*(upper4) + (29387423/100000000000000 : ℝ)*(lower5) + (920972484198523/50000000000000 : ℝ)*(major0) + (920972484198523/50000000000000 : ℝ)*(major1) + (920972484198523/50000000000000 : ℝ)*(major2) + (291221477/100000000000000 : ℝ)*(sp0) + (2926262097/20000000000000 : ℝ)*(sp2) + (945479659/25000000000000 : ℝ)*(sp3) + (321935880863873/12500000000000 : ℝ)*(sp8) + (128774366906623/5000000000000 : ℝ)*(sp9) + (103018908272879/4000000000000 : ℝ)*(sp10) + (43267818457863/4000000000000 : ℝ)*(sp11) + (108169924336521/10000000000000 : ℝ)*(f.failure) + (128774366906623/5000000000000 : ℝ)*(f.sum) + (2282898001801/2517500000000000000000000000 : ℝ)*base65 + (3653031650418937369/503500000000000000000000000000000 : ℝ)*base68 + (8129156258205937369/503500000000000000000000000000000 : ℝ)*base70 + (2664255039402937369/503500000000000000000000000000000 : ℝ)*base72 + (1801338215299/2517500000000000000000000000 : ℝ)*base74 + (897658955795437369/503500000000000000000000000000000 : ℝ)*base76 + (4049192327725437369/503500000000000000000000000000000 : ℝ)*base78 + (3584285131449437369/503500000000000000000000000000000 : ℝ)*base80 + (2343088272273/1258750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (341809/500000000000000000000 : ℝ)*base90 + (341809/500000000000000000000 : ℝ)*base92 + (341809/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-87659/100000 : ℝ) ≤ (-1765393615983513533599324089/2014000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30651419/50000000000000 : ℝ)*(lower2) + (11335079/25000000000000 : ℝ)*(upper3) + (115127/500000000000 : ℝ)*(upper5) + (376639301706647/20000000000000 : ℝ)*(major0) + (376639301706647/20000000000000 : ℝ)*(major1) + (376639301706647/20000000000000 : ℝ)*(major2) + (299532241/100000000000000 : ℝ)*(sp0) + (3801018077/100000000000000 : ℝ)*(sp5) + (16534103429/100000000000000 : ℝ)*(sp6) + (3038285121/100000000000000 : ℝ)*(sp7) + (33621085264999/1250000000000 : ℝ)*(sp12) + (672420829928521/25000000000000 : ℝ)*(sp13) + (2689670586628733/100000000000000 : ℝ)*(sp14) + (221184310821963/20000000000000 : ℝ)*(sp15) + (138240574049367/12500000000000 : ℝ)*(f.failure) + (1344843560366081/50000000000000 : ℝ)*(f.sum) + (10761338084673/2014000000000000000000000000 : ℝ)*base66 + (462597045809300141/201400000000000000000000000000000 : ℝ)*base68 + (864919001004899859/201400000000000000000000000000000 : ℝ)*base69 + (152182717126499859/201400000000000000000000000000000 : ℝ)*base71 + (2079181962187/2014000000000000000000000000 : ℝ)*base74 + (1010828805152699859/201400000000000000000000000000000 : ℝ)*base75 + (1735794622636900141/201400000000000000000000000000000 : ℝ)*base78 + (1085171200819300141/201400000000000000000000000000000 : ℝ)*base80 + (2922939832207/2014000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (4375457/625000000000000000000 : ℝ)*base89 + (4375457/625000000000000000000 : ℝ)*base91 + (4375457/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1594_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85141271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16367/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (413/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64871/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58021/100000 : ℝ) else (20027/25000 : ℝ) ≤ X j i ∧ X j i ≤ (87659/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1594_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1594_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85141271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16367/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (413/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64871/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58021/100000 : ℝ) else (20027/25000 : ℝ) ≤ X j i ∧ X j i ≤ (87659/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1594_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4691/1024 : ℝ) ≤ p) (hpb : p ≤ (4695/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85141271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16367/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (413/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64871/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58021/100000 : ℝ) else (20027/25000 : ℝ) ≤ X j i ∧ X j i ≤ (87659/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1594_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
