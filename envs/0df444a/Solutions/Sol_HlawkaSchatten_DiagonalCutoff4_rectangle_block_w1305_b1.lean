-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1305_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:37:57.849867+00:00
-- url     : https://prove2.me/submissions/95af4173-96c7-42cc-92e8-d27b67e47ec0

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
theorem support_rectangle_w1305_s3_0 (p : ℝ) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2074188787/10000000000 : ℝ)*x 0 + (2716089771/5000000000 : ℝ)*x 1 + (2613633599/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2074188787/10000000000 : ℝ)^4265 ≤ (12618427060063/100000000000000 : ℝ)^3241 := by
    have hnat : (2074188787 : ℕ)^4265*100000000000000^3241 ≤ 12618427060063^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074188787 10000000000 12618427060063 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716089771/5000000000 : ℝ)^4265 ≤ (44795943965561/100000000000000 : ℝ)^3241 := by
    have hnat : (2716089771 : ℕ)^4265*100000000000000^3241 ≤ 44795943965561^3241*5000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716089771 5000000000 44795943965561 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2613633599/5000000000 : ℝ)^4265 ≤ (42585628950481/100000000000000 : ℝ)^3241 := by
    have hnat : (2613633599 : ℕ)^4265*100000000000000^3241 ≤ 42585628950481^3241*5000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613633599 5000000000 42585628950481 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4265/1024 : ℝ)) 4265 3241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2074188787/10000000000 : ℝ), (2716089771/5000000000 : ℝ), (2613633599/5000000000 : ℝ)] ![(12618427060063/100000000000000 : ℝ), (44795943965561/100000000000000 : ℝ), (42585628950481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2074188787/10000000000 : ℝ)|^4265 ≤ (12618427060063/100000000000000 : ℝ)^3241
        have hw : |(-2074188787/10000000000 : ℝ)|=(2074188787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716089771/5000000000 : ℝ)|^4265 ≤ (44795943965561/100000000000000 : ℝ)^3241
        have hw : |(2716089771/5000000000 : ℝ)|=(2716089771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2613633599/5000000000 : ℝ)|^4265 ≤ (42585628950481/100000000000000 : ℝ)^3241
        have hw : |(2613633599/5000000000 : ℝ)|=(2613633599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1305_s3_1 (p : ℝ) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334628433/625000000 : ℝ)*x 0 + (-2179019819/10000000000 : ℝ)*x 1 + (81676049/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334628433/625000000 : ℝ)^4265 ≤ (43950078348771/100000000000000 : ℝ)^3241 := by
    have hnat : (334628433 : ℕ)^4265*100000000000000^3241 ≤ 43950078348771^3241*625000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334628433 625000000 43950078348771 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2179019819/10000000000 : ℝ)^4265 ≤ (13464293344823/100000000000000 : ℝ)^3241 := by
    have hnat : (2179019819 : ℕ)^4265*100000000000000^3241 ≤ 13464293344823^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179019819 10000000000 13464293344823 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81676049/156250000 : ℝ)^4265 ≤ (4258562828579/10000000000000 : ℝ)^3241 := by
    have hnat : (81676049 : ℕ)^4265*10000000000000^3241 ≤ 4258562828579^3241*156250000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81676049 156250000 4258562828579 10000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4265/1024 : ℝ)) 4265 3241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334628433/625000000 : ℝ), (-2179019819/10000000000 : ℝ), (81676049/156250000 : ℝ)] ![(43950078348771/100000000000000 : ℝ), (13464293344823/100000000000000 : ℝ), (4258562828579/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334628433/625000000 : ℝ)|^4265 ≤ (43950078348771/100000000000000 : ℝ)^3241
        have hw : |(334628433/625000000 : ℝ)|=(334628433/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2179019819/10000000000 : ℝ)|^4265 ≤ (13464293344823/100000000000000 : ℝ)^3241
        have hw : |(-2179019819/10000000000 : ℝ)|=(2179019819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81676049/156250000 : ℝ)|^4265 ≤ (4258562828579/10000000000000 : ℝ)^3241
        have hw : |(81676049/156250000 : ℝ)|=(81676049/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1305_s3_2 (p : ℝ) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354054849/10000000000 : ℝ)*x 0 + (2613633667/5000000000 : ℝ)*x 1 + (-2179019663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354054849/10000000000 : ℝ)^4265 ≤ (10987519373847/25000000000000 : ℝ)^3241 := by
    have hnat : (5354054849 : ℕ)^4265*25000000000000^3241 ≤ 10987519373847^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354054849 10000000000 10987519373847 25000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2613633667/5000000000 : ℝ)^4265 ≤ (21292815204257/50000000000000 : ℝ)^3241 := by
    have hnat : (2613633667 : ℕ)^4265*50000000000000^3241 ≤ 21292815204257^3241*5000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613633667 5000000000 21292815204257 50000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2179019663/10000000000 : ℝ)^4265 ≤ (13464292076333/100000000000000 : ℝ)^3241 := by
    have hnat : (2179019663 : ℕ)^4265*100000000000000^3241 ≤ 13464292076333^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179019663 10000000000 13464292076333 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4265/1024 : ℝ)) 4265 3241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354054849/10000000000 : ℝ), (2613633667/5000000000 : ℝ), (-2179019663/10000000000 : ℝ)] ![(10987519373847/25000000000000 : ℝ), (21292815204257/50000000000000 : ℝ), (13464292076333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354054849/10000000000 : ℝ)|^4265 ≤ (10987519373847/25000000000000 : ℝ)^3241
        have hw : |(5354054849/10000000000 : ℝ)|=(5354054849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2613633667/5000000000 : ℝ)|^4265 ≤ (21292815204257/50000000000000 : ℝ)^3241
        have hw : |(2613633667/5000000000 : ℝ)|=(2613633667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2179019663/10000000000 : ℝ)|^4265 ≤ (13464292076333/100000000000000 : ℝ)^3241
        have hw : |(-2179019663/10000000000 : ℝ)|=(2179019663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1305_s3_3 (p : ℝ) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4335071623/10000000000 : ℝ)*x 0 + (825671769/2000000000 : ℝ)*x 1 + (4551594991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4335071623/10000000000 : ℝ)^4265 ≤ (16644646563237/50000000000000 : ℝ)^3241 := by
    have hnat : (4335071623 : ℕ)^4265*50000000000000^3241 ≤ 16644646563237^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4335071623 10000000000 16644646563237 50000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (825671769/2000000000 : ℝ)^4265 ≤ (31216312874531/100000000000000 : ℝ)^3241 := by
    have hnat : (825671769 : ℕ)^4265*100000000000000^3241 ≤ 31216312874531^3241*2000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825671769 2000000000 31216312874531 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4551594991/10000000000 : ℝ)^4265 ≤ (4436799247219/12500000000000 : ℝ)^3241 := by
    have hnat : (4551594991 : ℕ)^4265*12500000000000^3241 ≤ 4436799247219^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4551594991 10000000000 4436799247219 12500000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4265/1024 : ℝ)) 4265 3241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4335071623/10000000000 : ℝ), (825671769/2000000000 : ℝ), (4551594991/10000000000 : ℝ)] ![(16644646563237/50000000000000 : ℝ), (31216312874531/100000000000000 : ℝ), (4436799247219/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4335071623/10000000000 : ℝ)|^4265 ≤ (16644646563237/50000000000000 : ℝ)^3241
        have hw : |(4335071623/10000000000 : ℝ)|=(4335071623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(825671769/2000000000 : ℝ)|^4265 ≤ (31216312874531/100000000000000 : ℝ)^3241
        have hw : |(825671769/2000000000 : ℝ)|=(825671769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4551594991/10000000000 : ℝ)|^4265 ≤ (4436799247219/12500000000000 : ℝ)^3241
        have hw : |(4551594991/10000000000 : ℝ)|=(4551594991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1305_s3_4 (p : ℝ) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2592763/12500000 : ℝ)*x 0 + (5228141599/10000000000 : ℝ)*x 1 + (5431299711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2592763/12500000 : ℝ)^4265 ≤ (12618600086599/100000000000000 : ℝ)^3241 := by
    have hnat : (2592763 : ℕ)^4265*100000000000000^3241 ≤ 12618600086599^3241*12500000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592763 12500000 12618600086599 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5228141599/10000000000 : ℝ)^4265 ≤ (42595003501817/100000000000000 : ℝ)^3241 := by
    have hnat : (5228141599 : ℕ)^4265*100000000000000^3241 ≤ 42595003501817^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228141599 10000000000 42595003501817 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431299711/10000000000 : ℝ)^4265 ≤ (22393198199127/50000000000000 : ℝ)^3241 := by
    have hnat : (5431299711 : ℕ)^4265*50000000000000^3241 ≤ 22393198199127^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431299711 10000000000 22393198199127 50000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4265/1024 : ℝ)) 4265 3241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2592763/12500000 : ℝ), (5228141599/10000000000 : ℝ), (5431299711/10000000000 : ℝ)] ![(12618600086599/100000000000000 : ℝ), (42595003501817/100000000000000 : ℝ), (22393198199127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2592763/12500000 : ℝ)|^4265 ≤ (12618600086599/100000000000000 : ℝ)^3241
        have hw : |(-2592763/12500000 : ℝ)|=(2592763/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5228141599/10000000000 : ℝ)|^4265 ≤ (42595003501817/100000000000000 : ℝ)^3241
        have hw : |(5228141599/10000000000 : ℝ)|=(5228141599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431299711/10000000000 : ℝ)|^4265 ≤ (22393198199127/50000000000000 : ℝ)^3241
        have hw : |(5431299711/10000000000 : ℝ)|=(5431299711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1305_s3_5 (p : ℝ) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1060300711/2000000000 : ℝ)*x 0 + (-1974987137/10000000000 : ℝ)*x 1 + (1357824919/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060300711/2000000000 : ℝ)^4265 ≤ (43383284067943/100000000000000 : ℝ)^3241 := by
    have hnat : (1060300711 : ℕ)^4265*100000000000000^3241 ≤ 43383284067943^3241*2000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060300711 2000000000 43383284067943 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1974987137/10000000000 : ℝ)^4265 ≤ (2957579972319/25000000000000 : ℝ)^3241 := by
    have hnat : (1974987137 : ℕ)^4265*25000000000000^3241 ≤ 2957579972319^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1974987137 10000000000 2957579972319 25000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357824919/2500000000 : ℝ)^4265 ≤ (22393198009229/50000000000000 : ℝ)^3241 := by
    have hnat : (1357824919 : ℕ)^4265*50000000000000^3241 ≤ 22393198009229^3241*2500000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357824919 2500000000 22393198009229 50000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4265/1024 : ℝ)) 4265 3241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060300711/2000000000 : ℝ), (-1974987137/10000000000 : ℝ), (1357824919/2500000000 : ℝ)] ![(43383284067943/100000000000000 : ℝ), (2957579972319/25000000000000 : ℝ), (22393198009229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060300711/2000000000 : ℝ)|^4265 ≤ (43383284067943/100000000000000 : ℝ)^3241
        have hw : |(1060300711/2000000000 : ℝ)|=(1060300711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1974987137/10000000000 : ℝ)|^4265 ≤ (2957579972319/25000000000000 : ℝ)^3241
        have hw : |(-1974987137/10000000000 : ℝ)|=(1974987137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357824919/2500000000 : ℝ)|^4265 ≤ (22393198009229/50000000000000 : ℝ)^3241
        have hw : |(1357824919/2500000000 : ℝ)|=(1357824919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1305_s3_6 (p : ℝ) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2650751833/5000000000 : ℝ)*x 0 + (5431299563/10000000000 : ℝ)*x 1 + (-1974987143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650751833/5000000000 : ℝ)^4265 ≤ (43383285263269/100000000000000 : ℝ)^3241 := by
    have hnat : (2650751833 : ℕ)^4265*100000000000000^3241 ≤ 43383285263269^3241*5000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650751833 5000000000 43383285263269 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431299563/10000000000 : ℝ)^4265 ≤ (2239319739613/5000000000000 : ℝ)^3241 := by
    have hnat : (5431299563 : ℕ)^4265*5000000000000^3241 ≤ 2239319739613^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431299563 10000000000 2239319739613 5000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1974987143/10000000000 : ℝ)^4265 ≤ (2957579984143/25000000000000 : ℝ)^3241 := by
    have hnat : (1974987143 : ℕ)^4265*25000000000000^3241 ≤ 2957579984143^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1974987143 10000000000 2957579984143 25000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4265/1024 : ℝ)) 4265 3241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650751833/5000000000 : ℝ), (5431299563/10000000000 : ℝ), (-1974987143/10000000000 : ℝ)] ![(43383285263269/100000000000000 : ℝ), (2239319739613/5000000000000 : ℝ), (2957579984143/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650751833/5000000000 : ℝ)|^4265 ≤ (43383285263269/100000000000000 : ℝ)^3241
        have hw : |(2650751833/5000000000 : ℝ)|=(2650751833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431299563/10000000000 : ℝ)|^4265 ≤ (2239319739613/5000000000000 : ℝ)^3241
        have hw : |(5431299563/10000000000 : ℝ)|=(5431299563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1974987143/10000000000 : ℝ)|^4265 ≤ (2957579984143/25000000000000 : ℝ)^3241
        have hw : |(-1974987143/10000000000 : ℝ)|=(1974987143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1305_s3_7 (p : ℝ) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (867023287/2000000000 : ℝ)*x 0 + (454978887/1000000000 : ℝ)*x 1 + (129067993/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (867023287/2000000000 : ℝ)^4265 ≤ (4161218245621/12500000000000 : ℝ)^3241 := by
    have hnat : (867023287 : ℕ)^4265*12500000000000^3241 ≤ 4161218245621^3241*2000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867023287 2000000000 4161218245621 12500000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (454978887/1000000000 : ℝ)^4265 ≤ (17737930274481/50000000000000 : ℝ)^3241 := by
    have hnat : (454978887 : ℕ)^4265*50000000000000^3241 ≤ 17737930274481^3241*1000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454978887 1000000000 17737930274481 50000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129067993/312500000 : ℝ)^4265 ≤ (976074796023/3125000000000 : ℝ)^3241 := by
    have hnat : (129067993 : ℕ)^4265*3125000000000^3241 ≤ 976074796023^3241*312500000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129067993 312500000 976074796023 3125000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4265/1024 : ℝ)) 4265 3241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(867023287/2000000000 : ℝ), (454978887/1000000000 : ℝ), (129067993/312500000 : ℝ)] ![(4161218245621/12500000000000 : ℝ), (17737930274481/50000000000000 : ℝ), (976074796023/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(867023287/2000000000 : ℝ)|^4265 ≤ (4161218245621/12500000000000 : ℝ)^3241
        have hw : |(867023287/2000000000 : ℝ)|=(867023287/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(454978887/1000000000 : ℝ)|^4265 ≤ (17737930274481/50000000000000 : ℝ)^3241
        have hw : |(454978887/1000000000 : ℝ)|=(454978887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(129067993/312500000 : ℝ)|^4265 ≤ (976074796023/3125000000000 : ℝ)^3241
        have hw : |(129067993/312500000 : ℝ)|=(129067993/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1305_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153272553/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16259/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9599/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2143/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (301/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16259/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9599/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16259/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9599/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16259/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9599/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16259/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9599/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16259/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9599/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16259/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9599/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9599/100000 : ℝ) ^ (533/128 : ℝ) ≤ (361247987059179/6250000000000000000 : ℝ) := by
    have hpowers : (9599/100000 : ℝ)^533 ≤ (361247987059179/6250000000000000000 : ℝ)^128 := by
      have hnat : (9599 : ℕ)^533*6250000000000000000^128 ≤ 361247987059179^128*100000^533 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9599 100000 361247987059179 6250000000000000000 533 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9599/100000 : ℝ)) (X := (361247987059179/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 533 128 (by norm_num) hpowers
    exact h
  have hpowhi : (16259/100000 : ℝ) ^ (533/128 : ℝ) ≤ (1621046331041471/3125000000000000000 : ℝ) := by
    have hpowers : (16259/100000 : ℝ)^533 ≤ (1621046331041471/3125000000000000000 : ℝ)^128 := by
      have hnat : (16259 : ℕ)^533*3125000000000000000^128 ≤ 1621046331041471^128*100000^533 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16259 100000 1621046331041471 3125000000000000000 533 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16259/100000 : ℝ)) (X := (1621046331041471/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 533 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125361247987059179/3125000000000000000 : ℝ) ≤ (10000277599769903/10000000000000000 : ℝ) ^ (533/128 : ℝ) := by
    have hpowers : (3125361247987059179/3125000000000000000 : ℝ)^128 ≤ (10000277599769903/10000000000000000 : ℝ)^533 := by
      have hnat : (3125361247987059179 : ℕ)^128*10000000000000000^533 ≤ 10000277599769903^533*3125000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125361247987059179 3125000000000000000 10000277599769903 10000000000000000 128 533 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000277599769903/10000000000000000 : ℝ)) (X := (3125361247987059179/3125000000000000000 : ℝ)) (by norm_num) 533 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (6253603340649142121/6250000000000000000 : ℝ) ≤ (10001384244983181/10000000000000000 : ℝ) ^ (533/128 : ℝ) := by
    have hpowers : (6253603340649142121/6250000000000000000 : ℝ)^128 ≤ (10001384244983181/10000000000000000 : ℝ)^533 := by
      have hnat : (6253603340649142121 : ℕ)^128*10000000000000000^533 ≤ 10001384244983181^533*6250000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253603340649142121 6250000000000000000 10001384244983181 10000000000000000 128 533 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001384244983181/10000000000000000 : ℝ)) (X := (6253603340649142121/6250000000000000000 : ℝ)) (by norm_num) 533 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (1564121046331041471/1562500000000000000 : ℝ) ≤ (10002490890196459/10000000000000000 : ℝ) ^ (533/128 : ℝ) := by
    have hpowers : (1564121046331041471/1562500000000000000 : ℝ)^128 ≤ (10002490890196459/10000000000000000 : ℝ)^533 := by
      have hnat : (1564121046331041471 : ℕ)^128*10000000000000000^533 ≤ 10002490890196459^533*1562500000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1564121046331041471 1562500000000000000 10002490890196459 10000000000000000 128 533 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002490890196459/10000000000000000 : ℝ)) (X := (1564121046331041471/1562500000000000000 : ℝ)) (by norm_num) 533 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(361247987059179/6250000000000000000 : ℝ) ≤ ((8322575429957880367/8325000000000000000 : ℝ)+2*(553322606639/333000000000000 : ℝ)*(9599/100000 : ℝ))^(533/128 : ℝ) := by
    rw [show (8322575429957880367/8325000000000000000 : ℝ)+2*(553322606639/333000000000000 : ℝ)*(9599/100000 : ℝ)=(10000277599769903/10000000000000000 : ℝ) by norm_num, show 1+2*(361247987059179/6250000000000000000 : ℝ)=(3125361247987059179/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1621046331041471/3125000000000000000 : ℝ)+(361247987059179/6250000000000000000 : ℝ) ≤ ((8322575429957880367/8325000000000000000 : ℝ)+(553322606639/333000000000000 : ℝ)*((16259/100000 : ℝ)+(9599/100000 : ℝ)))^(533/128 : ℝ) := by
    rw [show (8322575429957880367/8325000000000000000 : ℝ)+(553322606639/333000000000000 : ℝ)*((16259/100000 : ℝ)+(9599/100000 : ℝ))=(10001384244983181/10000000000000000 : ℝ) by norm_num, show 1+(1621046331041471/3125000000000000000 : ℝ)+(361247987059179/6250000000000000000 : ℝ)=(6253603340649142121/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1621046331041471/3125000000000000000 : ℝ) ≤ ((8322575429957880367/8325000000000000000 : ℝ)+2*(553322606639/333000000000000 : ℝ)*(16259/100000 : ℝ))^(533/128 : ℝ) := by
    rw [show (8322575429957880367/8325000000000000000 : ℝ)+2*(553322606639/333000000000000 : ℝ)*(16259/100000 : ℝ)=(10002490890196459/10000000000000000 : ℝ) by norm_num, show 1+2*(1621046331041471/3125000000000000000 : ℝ)=(1564121046331041471/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8322575429957880367/8325000000000000000 : ℝ)*(X 1 0+X 2 0)+(553322606639/333000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (533/128 : ℝ)) (lo := (9599/100000 : ℝ)) (hi := (16259/100000 : ℝ)) (c := (8322575429957880367/8325000000000000000 : ℝ)) (alpha := (553322606639/333000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8322575429957880367/8325000000000000000 : ℝ)*(X 0 1+X 2 1)+(553322606639/333000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (533/128 : ℝ)) (lo := (9599/100000 : ℝ)) (hi := (16259/100000 : ℝ)) (c := (8322575429957880367/8325000000000000000 : ℝ)) (alpha := (553322606639/333000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8322575429957880367/8325000000000000000 : ℝ)*(X 0 2+X 1 2)+(553322606639/333000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (533/128 : ℝ)) (lo := (9599/100000 : ℝ)) (hi := (16259/100000 : ℝ)) (c := (8322575429957880367/8325000000000000000 : ℝ)) (alpha := (553322606639/333000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2074188787/10000000000 : ℝ)*X 0 0+(2716089771/5000000000 : ℝ)*X 0 1+(2613633599/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1305_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334628433/625000000 : ℝ)*X 1 0+(-2179019819/10000000000 : ℝ)*X 1 1+(81676049/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1305_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354054849/10000000000 : ℝ)*X 2 0+(2613633667/5000000000 : ℝ)*X 2 1+(-2179019663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1305_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4335071623/10000000000 : ℝ)*X 0 0+(825671769/2000000000 : ℝ)*X 0 1+(4551594991/10000000000 : ℝ)*X 0 2+(4335071623/10000000000 : ℝ)*X 1 0+(825671769/2000000000 : ℝ)*X 1 1+(4551594991/10000000000 : ℝ)*X 1 2+(4335071623/10000000000 : ℝ)*X 2 0+(825671769/2000000000 : ℝ)*X 2 1+(4551594991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1305_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2592763/12500000 : ℝ)*X 0 0+(5228141599/10000000000 : ℝ)*X 0 1+(5431299711/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1305_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060300711/2000000000 : ℝ)*X 1 0+(-1974987137/10000000000 : ℝ)*X 1 1+(1357824919/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1305_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2650751833/5000000000 : ℝ)*X 2 0+(5431299563/10000000000 : ℝ)*X 2 1+(-1974987143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1305_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((867023287/2000000000 : ℝ)*X 0 0+(454978887/1000000000 : ℝ)*X 0 1+(129067993/312500000 : ℝ)*X 0 2+(867023287/2000000000 : ℝ)*X 1 0+(454978887/1000000000 : ℝ)*X 1 1+(129067993/312500000 : ℝ)*X 1 2+(867023287/2000000000 : ℝ)*X 2 0+(454978887/1000000000 : ℝ)*X 2 1+(129067993/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1305_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53213613348381384499996101/23125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (66016793/20000000000000 : ℝ)*(base19) + (94298073/50000000000000 : ℝ)*(base23) + (2599201/6250000000000 : ℝ)*(upper4) + (28119133/50000000000000 : ℝ)*(upper5) + (1810724733765003/50000000000000 : ℝ)*(major0) + (1810724733765003/50000000000000 : ℝ)*(major1) + (1810724733765003/50000000000000 : ℝ)*(major2) + (1220035083942481/25000000000000 : ℝ)*(sp0) + (4880146244071511/100000000000000 : ℝ)*(sp1) + (488014722036599/10000000000000 : ℝ)*(sp2) + (7383592578139/312500000000 : ℝ)*(sp3) + (1768298053/25000000000000 : ℝ)*(sp4) + (41740333/5000000000000 : ℝ)*(sp5) + (1824389077/100000000000000 : ℝ)*(sp7) + (590687862348389/25000000000000 : ℝ)*(f.failure) + (610018426120267/12500000000000 : ℝ)*(f.sum) + (7270696533143/1387500000000000000000000000 : ℝ)*base66 + (863592742659353211/46250000000000000000000000000000 : ℝ)*base68 + (786625422671853211/46250000000000000000000000000000 : ℝ)*base70 + (655752811795603211/46250000000000000000000000000000 : ℝ)*base72 + (4205322939409/693750000000000000000000000 : ℝ)*base74 + (304774467626853211/46250000000000000000000000000000 : ℝ)*base76 + (671133388138103211/46250000000000000000000000000000 : ℝ)*base78 + (1131835752619353211/46250000000000000000000000000000 : ℝ)*base80 + (13840684795411/2775000000000000000000000000 : ℝ)*base82 + (7467117/2500000000000000000000 : ℝ)*base89 + (7467117/2500000000000000000000 : ℝ)*base91 + (7467117/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2292459979627051658898623/250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2079182533/100000000000000 : ℝ)*(base19) + (457094601/20000000000000 : ℝ)*(base23) + (220895301/100000000000000 : ℝ)*(upper3) + (1850517/4000000000000 : ℝ)*(lower4) + (228347597/100000000000000 : ℝ)*(upper5) + (730542260538853/20000000000000 : ℝ)*(major0) + (730542260538853/20000000000000 : ℝ)*(major1) + (730542260538853/20000000000000 : ℝ)*(major2) + (17443122791/50000000000000 : ℝ)*(sp1) + (1140535869/3125000000000 : ℝ)*(sp2) + (4922274612029797/100000000000000 : ℝ)*(sp4) + (4922237646601683/100000000000000 : ℝ)*(sp5) + (615279478676123/12500000000000 : ℝ)*(sp6) + (595786921924349/25000000000000 : ℝ)*(sp7) + (595786921924349/25000000000000 : ℝ)*(f.failure) + (4922274612029797/100000000000000 : ℝ)*(f.sum) + (465508727209/90000000000000000000000000 : ℝ)*base66 + (6567050104875153/500000000000000000000000000000 : ℝ)*base68 + (1375080124875153/500000000000000000000000000000 : ℝ)*base70 + (4891553353875153/500000000000000000000000000000 : ℝ)*base72 + (485581141999/90000000000000000000000000 : ℝ)*base74 + (886709721375153/500000000000000000000000000000 : ℝ)*base76 + (672875941375153/500000000000000000000000000000 : ℝ)*base78 + (1943226335375153/500000000000000000000000000000 : ℝ)*base80 + (265746835009/90000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (19092997/2500000000000000000000 : ℝ)*base89 + (19092997/2500000000000000000000 : ℝ)*base91 + (19092997/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1305_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153272553/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16259/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9599/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2143/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (301/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1305_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1305_s4_0 (p : ℝ) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2075976821/10000000000 : ℝ)*x 0 + (541794251/1000000000 : ℝ)*x 1 + (5240331749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2075976821/10000000000 : ℝ)^4265 ≤ (1579092924349/12500000000000 : ℝ)^3241 := by
    have hnat : (2075976821 : ℕ)^4265*12500000000000^3241 ≤ 1579092924349^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075976821 10000000000 1579092924349 12500000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541794251/1000000000 : ℝ)^4265 ≤ (2790094346959/6250000000000 : ℝ)^3241 := by
    have hnat : (541794251 : ℕ)^4265*6250000000000^3241 ≤ 2790094346959^3241*1000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541794251 1000000000 2790094346959 6250000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240331749/10000000000 : ℝ)^4265 ≤ (4272574703767/10000000000000 : ℝ)^3241 := by
    have hnat : (5240331749 : ℕ)^4265*10000000000000^3241 ≤ 4272574703767^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240331749 10000000000 4272574703767 10000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4265/1024 : ℝ)) 4265 3241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2075976821/10000000000 : ℝ), (541794251/1000000000 : ℝ), (5240331749/10000000000 : ℝ)] ![(1579092924349/12500000000000 : ℝ), (2790094346959/6250000000000 : ℝ), (4272574703767/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2075976821/10000000000 : ℝ)|^4265 ≤ (1579092924349/12500000000000 : ℝ)^3241
        have hw : |(-2075976821/10000000000 : ℝ)|=(2075976821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541794251/1000000000 : ℝ)|^4265 ≤ (2790094346959/6250000000000 : ℝ)^3241
        have hw : |(541794251/1000000000 : ℝ)|=(541794251/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240331749/10000000000 : ℝ)|^4265 ≤ (4272574703767/10000000000000 : ℝ)^3241
        have hw : |(5240331749/10000000000 : ℝ)|=(5240331749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1305_s4_1 (p : ℝ) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214017949/400000000 : ℝ)*x 0 + (-2166566831/10000000000 : ℝ)*x 1 + (327520737/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214017949/400000000 : ℝ)^4265 ≤ (43911127153799/100000000000000 : ℝ)^3241 := by
    have hnat : (214017949 : ℕ)^4265*100000000000000^3241 ≤ 43911127153799^3241*400000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214017949 400000000 43911127153799 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2166566831/10000000000 : ℝ)^4265 ≤ (1670390667729/12500000000000 : ℝ)^3241 := by
    have hnat : (2166566831 : ℕ)^4265*12500000000000^3241 ≤ 1670390667729^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166566831 10000000000 1670390667729 12500000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327520737/625000000 : ℝ)^4265 ≤ (4272574749903/10000000000000 : ℝ)^3241 := by
    have hnat : (327520737 : ℕ)^4265*10000000000000^3241 ≤ 4272574749903^3241*625000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327520737 625000000 4272574749903 10000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4265/1024 : ℝ)) 4265 3241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214017949/400000000 : ℝ), (-2166566831/10000000000 : ℝ), (327520737/625000000 : ℝ)] ![(43911127153799/100000000000000 : ℝ), (1670390667729/12500000000000 : ℝ), (4272574749903/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214017949/400000000 : ℝ)|^4265 ≤ (43911127153799/100000000000000 : ℝ)^3241
        have hw : |(214017949/400000000 : ℝ)|=(214017949/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2166566831/10000000000 : ℝ)|^4265 ≤ (1670390667729/12500000000000 : ℝ)^3241
        have hw : |(-2166566831/10000000000 : ℝ)|=(2166566831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327520737/625000000 : ℝ)|^4265 ≤ (4272574749903/10000000000000 : ℝ)^3241
        have hw : |(327520737/625000000 : ℝ)|=(327520737/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1305_s4_2 (p : ℝ) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337612193/2500000000 : ℝ)*x 0 + (2620165891/5000000000 : ℝ)*x 1 + (-108328339/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337612193/2500000000 : ℝ)^4265 ≤ (219555638307/500000000000 : ℝ)^3241 := by
    have hnat : (1337612193 : ℕ)^4265*500000000000^3241 ≤ 219555638307^3241*2500000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337612193 2500000000 219555638307 500000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620165891/5000000000 : ℝ)^4265 ≤ (42725747391737/100000000000000 : ℝ)^3241 := by
    have hnat : (2620165891 : ℕ)^4265*100000000000000^3241 ≤ 42725747391737^3241*5000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620165891 5000000000 42725747391737 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108328339/500000000 : ℝ)^4265 ≤ (13363124927883/100000000000000 : ℝ)^3241 := by
    have hnat : (108328339 : ℕ)^4265*100000000000000^3241 ≤ 13363124927883^3241*500000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108328339 500000000 13363124927883 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4265/1024 : ℝ)) 4265 3241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337612193/2500000000 : ℝ), (2620165891/5000000000 : ℝ), (-108328339/500000000 : ℝ)] ![(219555638307/500000000000 : ℝ), (42725747391737/100000000000000 : ℝ), (13363124927883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337612193/2500000000 : ℝ)|^4265 ≤ (219555638307/500000000000 : ℝ)^3241
        have hw : |(1337612193/2500000000 : ℝ)|=(1337612193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620165891/5000000000 : ℝ)|^4265 ≤ (42725747391737/100000000000000 : ℝ)^3241
        have hw : |(2620165891/5000000000 : ℝ)|=(2620165891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-108328339/500000000 : ℝ)|^4265 ≤ (13363124927883/100000000000000 : ℝ)^3241
        have hw : |(-108328339/500000000 : ℝ)|=(108328339/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1305_s4_3 (p : ℝ) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (867230977/2000000000 : ℝ)*x 0 + (4156417907/10000000000 : ℝ)*x 1 + (904652829/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (867230977/2000000000 : ℝ)^4265 ≤ (16650120111557/50000000000000 : ℝ)^3241 := by
    have hnat : (867230977 : ℕ)^4265*50000000000000^3241 ≤ 16650120111557^3241*2000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867230977 2000000000 16650120111557 50000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4156417907/10000000000 : ℝ)^4265 ≤ (3936976677039/12500000000000 : ℝ)^3241 := by
    have hnat : (4156417907 : ℕ)^4265*12500000000000^3241 ≤ 3936976677039^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4156417907 10000000000 3936976677039 12500000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (904652829/2000000000 : ℝ)^4265 ≤ (35203946344697/100000000000000 : ℝ)^3241 := by
    have hnat : (904652829 : ℕ)^4265*100000000000000^3241 ≤ 35203946344697^3241*2000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904652829 2000000000 35203946344697 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4265/1024 : ℝ)) 4265 3241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(867230977/2000000000 : ℝ), (4156417907/10000000000 : ℝ), (904652829/2000000000 : ℝ)] ![(16650120111557/50000000000000 : ℝ), (3936976677039/12500000000000 : ℝ), (35203946344697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(867230977/2000000000 : ℝ)|^4265 ≤ (16650120111557/50000000000000 : ℝ)^3241
        have hw : |(867230977/2000000000 : ℝ)|=(867230977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4156417907/10000000000 : ℝ)|^4265 ≤ (3936976677039/12500000000000 : ℝ)^3241
        have hw : |(4156417907/10000000000 : ℝ)|=(4156417907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(904652829/2000000000 : ℝ)|^4265 ≤ (35203946344697/100000000000000 : ℝ)^3241
        have hw : |(904652829/2000000000 : ℝ)|=(904652829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1305_s4_4 (p : ℝ) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2075990877/10000000000 : ℝ)*x 0 + (2620494639/5000000000 : ℝ)*x 1 + (5417281463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2075990877/10000000000 : ℝ)^4265 ≤ (12632855953057/100000000000000 : ℝ)^3241 := by
    have hnat : (2075990877 : ℕ)^4265*100000000000000^3241 ≤ 12632855953057^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075990877 10000000000 12632855953057 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620494639/5000000000 : ℝ)^4265 ≤ (10683200498817/25000000000000 : ℝ)^3241 := by
    have hnat : (2620494639 : ℕ)^4265*25000000000000^3241 ≤ 10683200498817^3241*5000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620494639 5000000000 10683200498817 25000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417281463/10000000000 : ℝ)^4265 ≤ (11158585509743/25000000000000 : ℝ)^3241 := by
    have hnat : (5417281463 : ℕ)^4265*25000000000000^3241 ≤ 11158585509743^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417281463 10000000000 11158585509743 25000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4265/1024 : ℝ)) 4265 3241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2075990877/10000000000 : ℝ), (2620494639/5000000000 : ℝ), (5417281463/10000000000 : ℝ)] ![(12632855953057/100000000000000 : ℝ), (10683200498817/25000000000000 : ℝ), (11158585509743/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2075990877/10000000000 : ℝ)|^4265 ≤ (12632855953057/100000000000000 : ℝ)^3241
        have hw : |(-2075990877/10000000000 : ℝ)|=(2075990877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620494639/5000000000 : ℝ)|^4265 ≤ (10683200498817/25000000000000 : ℝ)^3241
        have hw : |(2620494639/5000000000 : ℝ)|=(2620494639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417281463/10000000000 : ℝ)|^4265 ≤ (11158585509743/25000000000000 : ℝ)^3241
        have hw : |(5417281463/10000000000 : ℝ)|=(5417281463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1305_s4_5 (p : ℝ) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652450763/5000000000 : ℝ)*x 0 + (-994808601/5000000000 : ℝ)*x 1 + (1354320369/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652450763/5000000000 : ℝ)^4265 ≤ (2170993975533/5000000000000 : ℝ)^3241 := by
    have hnat : (2652450763 : ℕ)^4265*5000000000000^3241 ≤ 2170993975533^3241*5000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652450763 5000000000 2170993975533 5000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (994808601/5000000000 : ℝ)^4265 ≤ (11945778293631/100000000000000 : ℝ)^3241 := by
    have hnat : (994808601 : ℕ)^4265*100000000000000^3241 ≤ 11945778293631^3241*5000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994808601 5000000000 11945778293631 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354320369/2500000000 : ℝ)^4265 ≤ (11158585544981/25000000000000 : ℝ)^3241 := by
    have hnat : (1354320369 : ℕ)^4265*25000000000000^3241 ≤ 11158585544981^3241*2500000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354320369 2500000000 11158585544981 25000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4265/1024 : ℝ)) 4265 3241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652450763/5000000000 : ℝ), (-994808601/5000000000 : ℝ), (1354320369/2500000000 : ℝ)] ![(2170993975533/5000000000000 : ℝ), (11945778293631/100000000000000 : ℝ), (11158585544981/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652450763/5000000000 : ℝ)|^4265 ≤ (2170993975533/5000000000000 : ℝ)^3241
        have hw : |(2652450763/5000000000 : ℝ)|=(2652450763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-994808601/5000000000 : ℝ)|^4265 ≤ (11945778293631/100000000000000 : ℝ)^3241
        have hw : |(-994808601/5000000000 : ℝ)|=(994808601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1354320369/2500000000 : ℝ)|^4265 ≤ (11158585544981/25000000000000 : ℝ)^3241
        have hw : |(1354320369/2500000000 : ℝ)|=(1354320369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1305_s4_6 (p : ℝ) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304901581/10000000000 : ℝ)*x 0 + (5417281433/10000000000 : ℝ)*x 1 + (-1989617187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304901581/10000000000 : ℝ)^4265 ≤ (43419880103059/100000000000000 : ℝ)^3241 := by
    have hnat : (5304901581 : ℕ)^4265*100000000000000^3241 ≤ 43419880103059^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304901581 10000000000 43419880103059 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417281433/10000000000 : ℝ)^4265 ≤ (22317170856849/50000000000000 : ℝ)^3241 := by
    have hnat : (5417281433 : ℕ)^4265*50000000000000^3241 ≤ 22317170856849^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417281433 10000000000 22317170856849 50000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1989617187/10000000000 : ℝ)^4265 ≤ (2389155635023/20000000000000 : ℝ)^3241 := by
    have hnat : (1989617187 : ℕ)^4265*20000000000000^3241 ≤ 2389155635023^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989617187 10000000000 2389155635023 20000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4265/1024 : ℝ)) 4265 3241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304901581/10000000000 : ℝ), (5417281433/10000000000 : ℝ), (-1989617187/10000000000 : ℝ)] ![(43419880103059/100000000000000 : ℝ), (22317170856849/50000000000000 : ℝ), (2389155635023/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304901581/10000000000 : ℝ)|^4265 ≤ (43419880103059/100000000000000 : ℝ)^3241
        have hw : |(5304901581/10000000000 : ℝ)|=(5304901581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417281433/10000000000 : ℝ)|^4265 ≤ (22317170856849/50000000000000 : ℝ)^3241
        have hw : |(5417281433/10000000000 : ℝ)|=(5417281433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1989617187/10000000000 : ℝ)|^4265 ≤ (2389155635023/20000000000000 : ℝ)^3241
        have hw : |(-1989617187/10000000000 : ℝ)|=(1989617187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1305_s4_7 (p : ℝ) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2168091983/5000000000 : ℝ)*x 0 + (4521905989/10000000000 : ℝ)*x 1 + (2078891619/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168091983/5000000000 : ℝ)^4265 ≤ (16650267059119/50000000000000 : ℝ)^3241 := by
    have hnat : (2168091983 : ℕ)^4265*50000000000000^3241 ≤ 16650267059119^3241*5000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168091983 5000000000 16650267059119 50000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4521905989/10000000000 : ℝ)^4265 ≤ (35190036942687/100000000000000 : ℝ)^3241 := by
    have hnat : (4521905989 : ℕ)^4265*100000000000000^3241 ≤ 35190036942687^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521905989 10000000000 35190036942687 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2078891619/5000000000 : ℝ)^4265 ≤ (15754714466267/50000000000000 : ℝ)^3241 := by
    have hnat : (2078891619 : ℕ)^4265*50000000000000^3241 ≤ 15754714466267^3241*5000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078891619 5000000000 15754714466267 50000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4265/1024 : ℝ)) 4265 3241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2168091983/5000000000 : ℝ), (4521905989/10000000000 : ℝ), (2078891619/5000000000 : ℝ)] ![(16650267059119/50000000000000 : ℝ), (35190036942687/100000000000000 : ℝ), (15754714466267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2168091983/5000000000 : ℝ)|^4265 ≤ (16650267059119/50000000000000 : ℝ)^3241
        have hw : |(2168091983/5000000000 : ℝ)|=(2168091983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4521905989/10000000000 : ℝ)|^4265 ≤ (35190036942687/100000000000000 : ℝ)^3241
        have hw : |(4521905989/10000000000 : ℝ)|=(4521905989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2078891619/5000000000 : ℝ)|^4265 ≤ (15754714466267/50000000000000 : ℝ)^3241
        have hw : |(2078891619/5000000000 : ℝ)|=(2078891619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1305_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153272553/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (301/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2143/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5497/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (461/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (301/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2143/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (301/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2143/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (301/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2143/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (301/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2143/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (301/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2143/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (301/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2143/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2143/20000 : ℝ) ^ (533/128 : ℝ) ≤ (1142185929423083/12500000000000000000 : ℝ) := by
    have hpowers : (2143/20000 : ℝ)^533 ≤ (1142185929423083/12500000000000000000 : ℝ)^128 := by
      have hnat : (2143 : ℕ)^533*12500000000000000000^128 ≤ 1142185929423083^128*20000^533 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2143 20000 1142185929423083 12500000000000000000 533 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2143/20000 : ℝ)) (X := (1142185929423083/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 533 128 (by norm_num) hpowers
    exact h
  have hpowhi : (301/2000 : ℝ) ^ (533/128 : ℝ) ≤ (18800984270498651/50000000000000000000 : ℝ) := by
    have hpowers : (301/2000 : ℝ)^533 ≤ (18800984270498651/50000000000000000000 : ℝ)^128 := by
      have hnat : (301 : ℕ)^533*50000000000000000000^128 ≤ 18800984270498651^128*2000^533 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        301 2000 18800984270498651 50000000000000000000 533 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (301/2000 : ℝ)) (X := (18800984270498651/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 533 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251142185929423083/6250000000000000000 : ℝ) ≤ (10000438843224701/10000000000000000 : ℝ) ^ (533/128 : ℝ) := by
    have hpowers : (6251142185929423083/6250000000000000000 : ℝ)^128 ≤ (10000438843224701/10000000000000000 : ℝ)^533 := by
      have hnat : (6251142185929423083 : ℕ)^128*10000000000000000^533 ≤ 10000438843224701^533*6250000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251142185929423083 6250000000000000000 10000438843224701 10000000000000000 128 533 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000438843224701/10000000000000000 : ℝ)) (X := (6251142185929423083/6250000000000000000 : ℝ)) (by norm_num) 533 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023369727988190983/50000000000000000000 : ℝ) ≤ (2000224449841947/2000000000000000 : ℝ) ^ (533/128 : ℝ) := by
    have hpowers : (50023369727988190983/50000000000000000000 : ℝ)^128 ≤ (2000224449841947/2000000000000000 : ℝ)^533 := by
      have hnat : (50023369727988190983 : ℕ)^128*2000000000000000^533 ≤ 2000224449841947^533*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023369727988190983 50000000000000000000 2000224449841947 2000000000000000 128 533 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000224449841947/2000000000000000 : ℝ)) (X := (50023369727988190983/50000000000000000000 : ℝ)) (by norm_num) 533 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018800984270498651/25000000000000000000 : ℝ) ≤ (10001805655194769/10000000000000000 : ℝ) ^ (533/128 : ℝ) := by
    have hpowers : (25018800984270498651/25000000000000000000 : ℝ)^128 ≤ (10001805655194769/10000000000000000 : ℝ)^533 := by
      have hnat : (25018800984270498651 : ℕ)^128*10000000000000000^533 ≤ 10001805655194769^533*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018800984270498651 25000000000000000000 10001805655194769 10000000000000000 128 533 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001805655194769/10000000000000000 : ℝ)) (X := (25018800984270498651/25000000000000000000 : ℝ)) (by norm_num) 533 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1142185929423083/12500000000000000000 : ℝ) ≤ ((8667451399023960043/8670000000000000000 : ℝ)+2*(341702992517/216750000000000 : ℝ)*(2143/20000 : ℝ))^(533/128 : ℝ) := by
    rw [show (8667451399023960043/8670000000000000000 : ℝ)+2*(341702992517/216750000000000 : ℝ)*(2143/20000 : ℝ)=(10000438843224701/10000000000000000 : ℝ) by norm_num, show 1+2*(1142185929423083/12500000000000000000 : ℝ)=(6251142185929423083/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18800984270498651/50000000000000000000 : ℝ)+(1142185929423083/12500000000000000000 : ℝ) ≤ ((8667451399023960043/8670000000000000000 : ℝ)+(341702992517/216750000000000 : ℝ)*((301/2000 : ℝ)+(2143/20000 : ℝ)))^(533/128 : ℝ) := by
    rw [show (8667451399023960043/8670000000000000000 : ℝ)+(341702992517/216750000000000 : ℝ)*((301/2000 : ℝ)+(2143/20000 : ℝ))=(2000224449841947/2000000000000000 : ℝ) by norm_num, show 1+(18800984270498651/50000000000000000000 : ℝ)+(1142185929423083/12500000000000000000 : ℝ)=(50023369727988190983/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18800984270498651/50000000000000000000 : ℝ) ≤ ((8667451399023960043/8670000000000000000 : ℝ)+2*(341702992517/216750000000000 : ℝ)*(301/2000 : ℝ))^(533/128 : ℝ) := by
    rw [show (8667451399023960043/8670000000000000000 : ℝ)+2*(341702992517/216750000000000 : ℝ)*(301/2000 : ℝ)=(10001805655194769/10000000000000000 : ℝ) by norm_num, show 1+2*(18800984270498651/50000000000000000000 : ℝ)=(25018800984270498651/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8667451399023960043/8670000000000000000 : ℝ)*(X 1 0+X 2 0)+(341702992517/216750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (533/128 : ℝ)) (lo := (2143/20000 : ℝ)) (hi := (301/2000 : ℝ)) (c := (8667451399023960043/8670000000000000000 : ℝ)) (alpha := (341702992517/216750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8667451399023960043/8670000000000000000 : ℝ)*(X 0 1+X 2 1)+(341702992517/216750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (533/128 : ℝ)) (lo := (2143/20000 : ℝ)) (hi := (301/2000 : ℝ)) (c := (8667451399023960043/8670000000000000000 : ℝ)) (alpha := (341702992517/216750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8667451399023960043/8670000000000000000 : ℝ)*(X 0 2+X 1 2)+(341702992517/216750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (533/128 : ℝ)) (lo := (2143/20000 : ℝ)) (hi := (301/2000 : ℝ)) (c := (8667451399023960043/8670000000000000000 : ℝ)) (alpha := (341702992517/216750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2075976821/10000000000 : ℝ)*X 0 0+(541794251/1000000000 : ℝ)*X 0 1+(5240331749/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1305_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((214017949/400000000 : ℝ)*X 1 0+(-2166566831/10000000000 : ℝ)*X 1 1+(327520737/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1305_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337612193/2500000000 : ℝ)*X 2 0+(2620165891/5000000000 : ℝ)*X 2 1+(-108328339/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1305_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((867230977/2000000000 : ℝ)*X 0 0+(4156417907/10000000000 : ℝ)*X 0 1+(904652829/2000000000 : ℝ)*X 0 2+(867230977/2000000000 : ℝ)*X 1 0+(4156417907/10000000000 : ℝ)*X 1 1+(904652829/2000000000 : ℝ)*X 1 2+(867230977/2000000000 : ℝ)*X 2 0+(4156417907/10000000000 : ℝ)*X 2 1+(904652829/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1305_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2075990877/10000000000 : ℝ)*X 0 0+(2620494639/5000000000 : ℝ)*X 0 1+(5417281463/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1305_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652450763/5000000000 : ℝ)*X 1 0+(-994808601/5000000000 : ℝ)*X 1 1+(1354320369/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1305_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304901581/10000000000 : ℝ)*X 2 0+(5417281433/10000000000 : ℝ)*X 2 1+(-1989617187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1305_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2168091983/5000000000 : ℝ)*X 0 0+(4521905989/10000000000 : ℝ)*X 0 1+(2078891619/5000000000 : ℝ)*X 0 2+(2168091983/5000000000 : ℝ)*X 1 0+(4521905989/10000000000 : ℝ)*X 1 1+(2078891619/5000000000 : ℝ)*X 1 2+(2168091983/5000000000 : ℝ)*X 2 0+(4521905989/10000000000 : ℝ)*X 2 1+(2078891619/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1305_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21743599606261837944563541/9031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (433021057/100000000000000 : ℝ)*(base19) + (225177459/50000000000000 : ℝ)*(base23) + (8594033/50000000000000 : ℝ)*(lower2) + (20072889/100000000000000 : ℝ)*(upper3) + (31773827/50000000000000 : ℝ)*(upper5) + (261133072982521/6250000000000 : ℝ)*(major0) + (261133072982521/6250000000000 : ℝ)*(major1) + (261133072982521/6250000000000 : ℝ)*(major2) + (5630298977500247/100000000000000 : ℝ)*(sp0) + (5630310425883183/100000000000000 : ℝ)*(sp1) + (2815155204274661/50000000000000 : ℝ)*(sp2) + (2725942693942093/100000000000000 : ℝ)*(sp3) + (11881403993/100000000000000 : ℝ)*(sp4) + (2351170569/50000000000000 : ℝ)*(sp7) + (85185856133851/3125000000000 : ℝ)*(f.failure) + (70378885736303/1250000000000 : ℝ)*(f.sum) + (55497911535049/21675000000000000000000000000 : ℝ)*base65 + (30554908676500301/18062500000000000000000000000000 : ℝ)*base67 + (86545005824875301/18062500000000000000000000000000 : ℝ)*base69 + (143112507579062801/18062500000000000000000000000000 : ℝ)*base71 + (5057246878339/1354687500000000000000000000 : ℝ)*base73 + (143432304557000301/18062500000000000000000000000000 : ℝ)*base75 + (238572081160250301/18062500000000000000000000000000 : ℝ)*base77 + (31729607337750301/18062500000000000000000000000000 : ℝ)*base79 + (80273385813349/21675000000000000000000000000 : ℝ)*base81 + (2491603/312500000000000000000 : ℝ)*base89 + (2491603/312500000000000000000 : ℝ)*base91 + (2491603/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (200763854672487670729324413/72250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38004781/10000000000000 : ℝ)*(base19) + (510932941/100000000000000 : ℝ)*(base23) + (4697533/10000000000000 : ℝ)*(upper3) + (33225931/100000000000000 : ℝ)*(lower4) + (79533929/100000000000000 : ℝ)*(upper5) + (2104682085966409/50000000000000 : ℝ)*(major0) + (2104682085966409/50000000000000 : ℝ)*(major1) + (2104682085966409/50000000000000 : ℝ)*(major2) + (7604648017/100000000000000 : ℝ)*(sp1) + (1088052133/12500000000000 : ℝ)*(sp2) + (177262566313743/3125000000000 : ℝ)*(sp4) + (5672394137343949/100000000000000 : ℝ)*(sp5) + (5672392906689771/100000000000000 : ℝ)*(sp6) + (2746326129201239/100000000000000 : ℝ)*(sp7) + (2746326129201239/100000000000000 : ℝ)*(f.failure) + (177262566313743/3125000000000 : ℝ)*(f.sum) + (31799818858231/10837500000000000000000000000 : ℝ)*base65 + (35676886534061471/144500000000000000000000000000000 : ℝ)*base68 + (576690694206438529/144500000000000000000000000000000 : ℝ)*base69 + (25805553127061471/144500000000000000000000000000000 : ℝ)*base72 + (4649982368131/10837500000000000000000000000 : ℝ)*base73 + (151893510156438529/144500000000000000000000000000000 : ℝ)*base75 + (344016351602938529/144500000000000000000000000000000 : ℝ)*base77 + (1599177593912438529/144500000000000000000000000000000 : ℝ)*base79 + (134589739405937/21675000000000000000000000000 : ℝ)*base81 + (47706833/10000000000000000000000 : ℝ)*base90 + (47706833/10000000000000000000000 : ℝ)*base92 + (47706833/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1305_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153272553/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (301/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2143/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5497/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (461/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1305_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1305_s5_0 (p : ℝ) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2076306467/10000000000 : ℝ)*x 0 + (216605999/400000000 : ℝ)*x 1 + (262145369/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2076306467/10000000000 : ℝ)^4265 ≤ (6317691606083/50000000000000 : ℝ)^3241 := by
    have hnat : (2076306467 : ℕ)^4265*50000000000000^3241 ≤ 6317691606083^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076306467 10000000000 6317691606083 50000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216605999/400000000 : ℝ)^4265 ≤ (44611232906873/100000000000000 : ℝ)^3241 := by
    have hnat : (216605999 : ℕ)^4265*100000000000000^3241 ≤ 44611232906873^3241*400000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216605999 400000000 44611232906873 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262145369/500000000 : ℝ)^4265 ≤ (2672086491809/6250000000000 : ℝ)^3241 := by
    have hnat : (262145369 : ℕ)^4265*6250000000000^3241 ≤ 2672086491809^3241*500000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262145369 500000000 2672086491809 6250000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4265/1024 : ℝ)) 4265 3241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2076306467/10000000000 : ℝ), (216605999/400000000 : ℝ), (262145369/500000000 : ℝ)] ![(6317691606083/50000000000000 : ℝ), (44611232906873/100000000000000 : ℝ), (2672086491809/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2076306467/10000000000 : ℝ)|^4265 ≤ (6317691606083/50000000000000 : ℝ)^3241
        have hw : |(-2076306467/10000000000 : ℝ)|=(2076306467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216605999/400000000 : ℝ)|^4265 ≤ (44611232906873/100000000000000 : ℝ)^3241
        have hw : |(216605999/400000000 : ℝ)|=(216605999/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262145369/500000000 : ℝ)|^4265 ≤ (2672086491809/6250000000000 : ℝ)^3241
        have hw : |(262145369/500000000 : ℝ)|=(262145369/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1305_s5_1 (p : ℝ) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534973869/1000000000 : ℝ)*x 0 + (-1082053141/5000000000 : ℝ)*x 1 + (2621453673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534973869/1000000000 : ℝ)^4265 ≤ (43903458925483/100000000000000 : ℝ)^3241 := by
    have hnat : (534973869 : ℕ)^4265*100000000000000^3241 ≤ 43903458925483^3241*1000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534973869 1000000000 43903458925483 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082053141/5000000000 : ℝ)^4265 ≤ (1667894693811/12500000000000 : ℝ)^3241 := by
    have hnat : (1082053141 : ℕ)^4265*12500000000000^3241 ≤ 1667894693811^3241*5000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082053141 5000000000 1667894693811 12500000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621453673/5000000000 : ℝ)^4265 ≤ (10688345876023/25000000000000 : ℝ)^3241 := by
    have hnat : (2621453673 : ℕ)^4265*25000000000000^3241 ≤ 10688345876023^3241*5000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621453673 5000000000 10688345876023 25000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4265/1024 : ℝ)) 4265 3241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534973869/1000000000 : ℝ), (-1082053141/5000000000 : ℝ), (2621453673/5000000000 : ℝ)] ![(43903458925483/100000000000000 : ℝ), (1667894693811/12500000000000 : ℝ), (10688345876023/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534973869/1000000000 : ℝ)|^4265 ≤ (43903458925483/100000000000000 : ℝ)^3241
        have hw : |(534973869/1000000000 : ℝ)|=(534973869/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1082053141/5000000000 : ℝ)|^4265 ≤ (1667894693811/12500000000000 : ℝ)^3241
        have hw : |(-1082053141/5000000000 : ℝ)|=(1082053141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621453673/5000000000 : ℝ)|^4265 ≤ (10688345876023/25000000000000 : ℝ)^3241
        have hw : |(2621453673/5000000000 : ℝ)|=(2621453673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1305_s5_2 (p : ℝ) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349738631/10000000000 : ℝ)*x 0 + (2621453703/5000000000 : ℝ)*x 1 + (-2164106281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349738631/10000000000 : ℝ)^4265 ≤ (43903458288309/100000000000000 : ℝ)^3241 := by
    have hnat : (5349738631 : ℕ)^4265*100000000000000^3241 ≤ 43903458288309^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349738631 10000000000 43903458288309 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621453703/5000000000 : ℝ)^4265 ≤ (42753384147949/100000000000000 : ℝ)^3241 := by
    have hnat : (2621453703 : ℕ)^4265*100000000000000^3241 ≤ 42753384147949^3241*5000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621453703 5000000000 42753384147949 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2164106281/10000000000 : ℝ)^4265 ≤ (106745260339/800000000000 : ℝ)^3241 := by
    have hnat : (2164106281 : ℕ)^4265*800000000000^3241 ≤ 106745260339^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164106281 10000000000 106745260339 800000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4265/1024 : ℝ)) 4265 3241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349738631/10000000000 : ℝ), (2621453703/5000000000 : ℝ), (-2164106281/10000000000 : ℝ)] ![(43903458288309/100000000000000 : ℝ), (42753384147949/100000000000000 : ℝ), (106745260339/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349738631/10000000000 : ℝ)|^4265 ≤ (43903458288309/100000000000000 : ℝ)^3241
        have hw : |(5349738631/10000000000 : ℝ)|=(5349738631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621453703/5000000000 : ℝ)|^4265 ≤ (42753384147949/100000000000000 : ℝ)^3241
        have hw : |(2621453703/5000000000 : ℝ)|=(2621453703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2164106281/10000000000 : ℝ)|^4265 ≤ (106745260339/800000000000 : ℝ)^3241
        have hw : |(-2164106281/10000000000 : ℝ)|=(2164106281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1305_s5_3 (p : ℝ) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4336349641/10000000000 : ℝ)*x 0 + (4161937283/10000000000 : ℝ)*x 1 + (2258847963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4336349641/10000000000 : ℝ)^4265 ≤ (520347007127/1562500000000 : ℝ)^3241 := by
    have hnat : (4336349641 : ℕ)^4265*1562500000000^3241 ≤ 520347007127^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4336349641 10000000000 520347007127 1562500000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4161937283/10000000000 : ℝ)^4265 ≤ (31550863080713/100000000000000 : ℝ)^3241 := by
    have hnat : (4161937283 : ℕ)^4265*100000000000000^3241 ≤ 31550863080713^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4161937283 10000000000 31550863080713 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2258847963/5000000000 : ℝ)^4265 ≤ (17573464222013/50000000000000 : ℝ)^3241 := by
    have hnat : (2258847963 : ℕ)^4265*50000000000000^3241 ≤ 17573464222013^3241*5000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258847963 5000000000 17573464222013 50000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4265/1024 : ℝ)) 4265 3241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4336349641/10000000000 : ℝ), (4161937283/10000000000 : ℝ), (2258847963/5000000000 : ℝ)] ![(520347007127/1562500000000 : ℝ), (31550863080713/100000000000000 : ℝ), (17573464222013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4336349641/10000000000 : ℝ)|^4265 ≤ (520347007127/1562500000000 : ℝ)^3241
        have hw : |(4336349641/10000000000 : ℝ)|=(4336349641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4161937283/10000000000 : ℝ)|^4265 ≤ (31550863080713/100000000000000 : ℝ)^3241
        have hw : |(4161937283/10000000000 : ℝ)|=(4161937283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2258847963/5000000000 : ℝ)|^4265 ≤ (17573464222013/50000000000000 : ℝ)^3241
        have hw : |(2258847963/5000000000 : ℝ)|=(2258847963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1305_s5_4 (p : ℝ) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-207631931/1000000000 : ℝ)*x 0 + (1048705157/2000000000 : ℝ)*x 1 + (676816043/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207631931/1000000000 : ℝ)^4265 ≤ (6317743031033/50000000000000 : ℝ)^3241 := by
    have hnat : (207631931 : ℕ)^4265*50000000000000^3241 ≤ 6317743031033^3241*1000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207631931 1000000000 6317743031033 50000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048705157/2000000000 : ℝ)^4265 ≤ (21380010033947/50000000000000 : ℝ)^3241 := by
    have hnat : (1048705157 : ℕ)^4265*50000000000000^3241 ≤ 21380010033947^3241*2000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048705157 2000000000 21380010033947 50000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676816043/1250000000 : ℝ)^4265 ≤ (44604493859191/100000000000000 : ℝ)^3241 := by
    have hnat : (676816043 : ℕ)^4265*100000000000000^3241 ≤ 44604493859191^3241*1250000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676816043 1250000000 44604493859191 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4265/1024 : ℝ)) 4265 3241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-207631931/1000000000 : ℝ), (1048705157/2000000000 : ℝ), (676816043/1250000000 : ℝ)] ![(6317743031033/50000000000000 : ℝ), (21380010033947/50000000000000 : ℝ), (44604493859191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-207631931/1000000000 : ℝ)|^4265 ≤ (6317743031033/50000000000000 : ℝ)^3241
        have hw : |(-207631931/1000000000 : ℝ)|=(207631931/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048705157/2000000000 : ℝ)|^4265 ≤ (21380010033947/50000000000000 : ℝ)^3241
        have hw : |(1048705157/2000000000 : ℝ)|=(1048705157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676816043/1250000000 : ℝ)|^4265 ≤ (44604493859191/100000000000000 : ℝ)^3241
        have hw : |(676816043/1250000000 : ℝ)|=(676816043/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1305_s5_5 (p : ℝ) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326392097/2500000000 : ℝ)*x 0 + (-996242669/5000000000 : ℝ)*x 1 + (21150501/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326392097/2500000000 : ℝ)^4265 ≤ (43427062345601/100000000000000 : ℝ)^3241 := by
    have hnat : (1326392097 : ℕ)^4265*100000000000000^3241 ≤ 43427062345601^3241*2500000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326392097 2500000000 43427062345601 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (996242669/5000000000 : ℝ)^4265 ≤ (11968444744673/100000000000000 : ℝ)^3241 := by
    have hnat : (996242669 : ℕ)^4265*100000000000000^3241 ≤ 11968444744673^3241*5000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996242669 5000000000 11968444744673 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21150501/39062500 : ℝ)^4265 ≤ (5575561613151/12500000000000 : ℝ)^3241 := by
    have hnat : (21150501 : ℕ)^4265*12500000000000^3241 ≤ 5575561613151^3241*39062500^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21150501 39062500 5575561613151 12500000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4265/1024 : ℝ)) 4265 3241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326392097/2500000000 : ℝ), (-996242669/5000000000 : ℝ), (21150501/39062500 : ℝ)] ![(43427062345601/100000000000000 : ℝ), (11968444744673/100000000000000 : ℝ), (5575561613151/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326392097/2500000000 : ℝ)|^4265 ≤ (43427062345601/100000000000000 : ℝ)^3241
        have hw : |(1326392097/2500000000 : ℝ)|=(1326392097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-996242669/5000000000 : ℝ)|^4265 ≤ (11968444744673/100000000000000 : ℝ)^3241
        have hw : |(-996242669/5000000000 : ℝ)|=(996242669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21150501/39062500 : ℝ)|^4265 ≤ (5575561613151/12500000000000 : ℝ)^3241
        have hw : |(21150501/39062500 : ℝ)|=(21150501/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1305_s5_6 (p : ℝ) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331598027/625000000 : ℝ)*x 0 + (1353632017/2500000000 : ℝ)*x 1 + (-62265173/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331598027/625000000 : ℝ)^4265 ≤ (43427062819539/100000000000000 : ℝ)^3241 := by
    have hnat : (331598027 : ℕ)^4265*100000000000000^3241 ≤ 43427062819539^3241*625000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331598027 625000000 43427062819539 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353632017/2500000000 : ℝ)^4265 ≤ (44604490867153/100000000000000 : ℝ)^3241 := by
    have hnat : (1353632017 : ℕ)^4265*100000000000000^3241 ≤ 44604490867153^3241*2500000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353632017 2500000000 44604490867153 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62265173/312500000 : ℝ)^4265 ≤ (11968446309793/100000000000000 : ℝ)^3241 := by
    have hnat : (62265173 : ℕ)^4265*100000000000000^3241 ≤ 11968446309793^3241*312500000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62265173 312500000 11968446309793 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4265/1024 : ℝ)) 4265 3241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331598027/625000000 : ℝ), (1353632017/2500000000 : ℝ), (-62265173/312500000 : ℝ)] ![(43427062819539/100000000000000 : ℝ), (44604490867153/100000000000000 : ℝ), (11968446309793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331598027/625000000 : ℝ)|^4265 ≤ (43427062819539/100000000000000 : ℝ)^3241
        have hw : |(331598027/625000000 : ℝ)|=(331598027/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353632017/2500000000 : ℝ)|^4265 ≤ (44604490867153/100000000000000 : ℝ)^3241
        have hw : |(1353632017/2500000000 : ℝ)|=(1353632017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-62265173/312500000 : ℝ)|^4265 ≤ (11968446309793/100000000000000 : ℝ)^3241
        have hw : |(-62265173/312500000 : ℝ)|=(62265173/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1305_s5_7 (p : ℝ) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4336376233/10000000000 : ℝ)*x 0 + (4516418221/10000000000 : ℝ)*x 1 + (130100671/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4336376233/10000000000 : ℝ)^4265 ≤ (3330247720099/10000000000000 : ℝ)^3241 := by
    have hnat : (4336376233 : ℕ)^4265*10000000000000^3241 ≤ 3330247720099^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4336376233 10000000000 3330247720099 10000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4516418221/10000000000 : ℝ)^4265 ≤ (1097932750859/3125000000000 : ℝ)^3241 := by
    have hnat : (4516418221 : ℕ)^4265*3125000000000^3241 ≤ 1097932750859^3241*10000000000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516418221 10000000000 1097932750859 3125000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130100671/312500000 : ℝ)^4265 ≤ (31563674753257/100000000000000 : ℝ)^3241 := by
    have hnat : (130100671 : ℕ)^4265*100000000000000^3241 ≤ 31563674753257^3241*312500000^4265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130100671 312500000 31563674753257 100000000000000 4265 3241 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4265/1024 : ℝ)) 4265 3241 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4336376233/10000000000 : ℝ), (4516418221/10000000000 : ℝ), (130100671/312500000 : ℝ)] ![(3330247720099/10000000000000 : ℝ), (1097932750859/3125000000000 : ℝ), (31563674753257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4336376233/10000000000 : ℝ)|^4265 ≤ (3330247720099/10000000000000 : ℝ)^3241
        have hw : |(4336376233/10000000000 : ℝ)|=(4336376233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4516418221/10000000000 : ℝ)|^4265 ≤ (1097932750859/3125000000000 : ℝ)^3241
        have hw : |(4516418221/10000000000 : ℝ)|=(4516418221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130100671/312500000 : ℝ)|^4265 ≤ (31563674753257/100000000000000 : ℝ)^3241
        have hw : |(130100671/312500000 : ℝ)|=(130100671/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1305_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153272553/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5497/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11049/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7347/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (461/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5497/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (461/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5497/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (461/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5497/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (461/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5497/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (461/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5497/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (461/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5497/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5497/50000 : ℝ) ^ (533/128 : ℝ) ≤ (406792122481673/4000000000000000000 : ℝ) := by
    have hpowers : (5497/50000 : ℝ)^533 ≤ (406792122481673/4000000000000000000 : ℝ)^128 := by
      have hnat : (5497 : ℕ)^533*4000000000000000000^128 ≤ 406792122481673^128*50000^533 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5497 50000 406792122481673 4000000000000000000 533 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5497/50000 : ℝ)) (X := (406792122481673/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 533 128 (by norm_num) hpowers
    exact h
  have hpowhi : (461/3125 : ℝ) ^ (533/128 : ℝ) ≤ (34597380363519007/100000000000000000000 : ℝ) := by
    have hpowers : (461/3125 : ℝ)^533 ≤ (34597380363519007/100000000000000000000 : ℝ)^128 := by
      have hnat : (461 : ℕ)^533*100000000000000000000^128 ≤ 34597380363519007^128*3125^533 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        461 3125 34597380363519007 100000000000000000000 533 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (461/3125 : ℝ)) (X := (34597380363519007/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 533 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000406792122481673/2000000000000000000 : ℝ) ≤ (2000097683618167/2000000000000000 : ℝ) ^ (533/128 : ℝ) := by
    have hpowers : (2000406792122481673/2000000000000000000 : ℝ)^128 ≤ (2000097683618167/2000000000000000 : ℝ)^533 := by
      have hnat : (2000406792122481673 : ℕ)^128*2000000000000000^533 ≤ 2000097683618167^533*2000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000406792122481673 2000000000000000000 2000097683618167 2000000000000000 128 533 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000097683618167/2000000000000000 : ℝ)) (X := (2000406792122481673/2000000000000000000 : ℝ)) (by norm_num) 533 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (390799871810256097/390625000000000000 : ℝ) ≤ (10001074901525753/10000000000000000 : ℝ) ^ (533/128 : ℝ) := by
    have hpowers : (390799871810256097/390625000000000000 : ℝ)^128 ≤ (10001074901525753/10000000000000000 : ℝ)^533 := by
      have hnat : (390799871810256097 : ℕ)^128*10000000000000000^533 ≤ 10001074901525753^533*390625000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390799871810256097 390625000000000000 10001074901525753 10000000000000000 128 533 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001074901525753/10000000000000000 : ℝ)) (X := (390799871810256097/390625000000000000 : ℝ)) (by norm_num) 533 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034597380363519007/50000000000000000000 : ℝ) ≤ (10001661384960671/10000000000000000 : ℝ) ^ (533/128 : ℝ) := by
    have hpowers : (50034597380363519007/50000000000000000000 : ℝ)^128 ≤ (10001661384960671/10000000000000000 : ℝ)^533 := by
      have hnat : (50034597380363519007 : ℕ)^128*10000000000000000^533 ≤ 10001661384960671^533*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034597380363519007 50000000000000000000 10001661384960671 10000000000000000 128 533 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001661384960671/10000000000000000 : ℝ)) (X := (50034597380363519007/50000000000000000000 : ℝ)) (by norm_num) 533 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(406792122481673/4000000000000000000 : ℝ) ≤ ((18784469938709190473/18790000000000000000 : ℝ)+2*(293241717459/187900000000000 : ℝ)*(5497/50000 : ℝ))^(533/128 : ℝ) := by
    rw [show (18784469938709190473/18790000000000000000 : ℝ)+2*(293241717459/187900000000000 : ℝ)*(5497/50000 : ℝ)=(2000097683618167/2000000000000000 : ℝ) by norm_num, show 1+2*(406792122481673/4000000000000000000 : ℝ)=(2000406792122481673/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34597380363519007/100000000000000000000 : ℝ)+(406792122481673/4000000000000000000 : ℝ) ≤ ((18784469938709190473/18790000000000000000 : ℝ)+(293241717459/187900000000000 : ℝ)*((461/3125 : ℝ)+(5497/50000 : ℝ)))^(533/128 : ℝ) := by
    rw [show (18784469938709190473/18790000000000000000 : ℝ)+(293241717459/187900000000000 : ℝ)*((461/3125 : ℝ)+(5497/50000 : ℝ))=(10001074901525753/10000000000000000 : ℝ) by norm_num, show 1+(34597380363519007/100000000000000000000 : ℝ)+(406792122481673/4000000000000000000 : ℝ)=(390799871810256097/390625000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34597380363519007/100000000000000000000 : ℝ) ≤ ((18784469938709190473/18790000000000000000 : ℝ)+2*(293241717459/187900000000000 : ℝ)*(461/3125 : ℝ))^(533/128 : ℝ) := by
    rw [show (18784469938709190473/18790000000000000000 : ℝ)+2*(293241717459/187900000000000 : ℝ)*(461/3125 : ℝ)=(10001661384960671/10000000000000000 : ℝ) by norm_num, show 1+2*(34597380363519007/100000000000000000000 : ℝ)=(50034597380363519007/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18784469938709190473/18790000000000000000 : ℝ)*(X 1 0+X 2 0)+(293241717459/187900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (533/128 : ℝ)) (lo := (5497/50000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (18784469938709190473/18790000000000000000 : ℝ)) (alpha := (293241717459/187900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18784469938709190473/18790000000000000000 : ℝ)*(X 0 1+X 2 1)+(293241717459/187900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (533/128 : ℝ)) (lo := (5497/50000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (18784469938709190473/18790000000000000000 : ℝ)) (alpha := (293241717459/187900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18784469938709190473/18790000000000000000 : ℝ)*(X 0 2+X 1 2)+(293241717459/187900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (533/128 : ℝ)) (lo := (5497/50000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (18784469938709190473/18790000000000000000 : ℝ)) (alpha := (293241717459/187900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2076306467/10000000000 : ℝ)*X 0 0+(216605999/400000000 : ℝ)*X 0 1+(262145369/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1305_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534973869/1000000000 : ℝ)*X 1 0+(-1082053141/5000000000 : ℝ)*X 1 1+(2621453673/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1305_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349738631/10000000000 : ℝ)*X 2 0+(2621453703/5000000000 : ℝ)*X 2 1+(-2164106281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1305_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4336349641/10000000000 : ℝ)*X 0 0+(4161937283/10000000000 : ℝ)*X 0 1+(2258847963/5000000000 : ℝ)*X 0 2+(4336349641/10000000000 : ℝ)*X 1 0+(4161937283/10000000000 : ℝ)*X 1 1+(2258847963/5000000000 : ℝ)*X 1 2+(4336349641/10000000000 : ℝ)*X 2 0+(4161937283/10000000000 : ℝ)*X 2 1+(2258847963/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1305_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-207631931/1000000000 : ℝ)*X 0 0+(1048705157/2000000000 : ℝ)*X 0 1+(676816043/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1305_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326392097/2500000000 : ℝ)*X 1 0+(-996242669/5000000000 : ℝ)*X 1 1+(21150501/39062500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1305_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((331598027/625000000 : ℝ)*X 2 0+(1353632017/2500000000 : ℝ)*X 2 1+(-62265173/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1305_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4336376233/10000000000 : ℝ)*X 0 0+(4516418221/10000000000 : ℝ)*X 0 1+(130100671/312500000 : ℝ)*X 0 2+(4336376233/10000000000 : ℝ)*X 1 0+(4516418221/10000000000 : ℝ)*X 1 1+(130100671/312500000 : ℝ)*X 1 2+(4336376233/10000000000 : ℝ)*X 2 0+(4516418221/10000000000 : ℝ)*X 2 1+(130100671/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1305_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1115245829435529921847925007/469750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (423497901/100000000000000 : ℝ)*(base19) + (325298391/100000000000000 : ℝ)*(base23) + (914003/5000000000000 : ℝ)*(lower2) + (46479111/100000000000000 : ℝ)*(upper3) + (5326609/50000000000000 : ℝ)*(upper5) + (2154171180324751/50000000000000 : ℝ)*(major0) + (2154171180324751/50000000000000 : ℝ)*(major1) + (2154171180324751/50000000000000 : ℝ)*(major2) + (5805774042242463/100000000000000 : ℝ)*(sp0) + (5805781499081723/100000000000000 : ℝ)*(sp1) + (2902890798640617/50000000000000 : ℝ)*(sp2) + (87840573841467/3125000000000 : ℝ)*(sp3) + (7880337161/100000000000000 : ℝ)*(sp4) + (2178327443/50000000000000 : ℝ)*(sp7) + (281090271958183/10000000000000 : ℝ)*(f.failure) + (725722740322453/12500000000000 : ℝ)*(f.sum) + (13494475414073/9395000000000000000000000000 : ℝ)*base65 + (5726378094809802777/939500000000000000000000000000000 : ℝ)*base68 + (3013567045843802777/939500000000000000000000000000000 : ℝ)*base70 + (6019500820847802777/939500000000000000000000000000000 : ℝ)*base72 + (14034550906989/4697500000000000000000000000 : ℝ)*base73 + (1367533765386802777/939500000000000000000000000000000 : ℝ)*base76 + (14565369243915802777/939500000000000000000000000000000 : ℝ)*base78 + (6241068320072802777/939500000000000000000000000000000 : ℝ)*base80 + (86566068301/73398437500000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2348801/1000000000000000000000 : ℝ)*base90 + (2348801/1000000000000000000000 : ℝ)*base92 + (2348801/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (267306630505768659490065633/46975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (239353113/20000000000000 : ℝ)*(base19) + (256042403/20000000000000 : ℝ)*(base23) + (637081/1562500000000 : ℝ)*(upper3) + (2390569/4000000000000 : ℝ)*(lower4) + (52106601/25000000000000 : ℝ)*(upper5) + (216978766039693/5000000000000 : ℝ)*(major0) + (216978766039693/5000000000000 : ℝ)*(major1) + (216978766039693/5000000000000 : ℝ)*(major2) + (26601596759/100000000000000 : ℝ)*(sp1) + (17269175677/100000000000000 : ℝ)*(sp2) + (1461967583256089/25000000000000 : ℝ)*(sp4) + (365490158416377/6250000000000 : ℝ)*(sp5) + (730981472954583/12500000000000 : ℝ)*(sp6) + (1415640059441647/50000000000000 : ℝ)*(sp7) + (1415640059441647/50000000000000 : ℝ)*(f.failure) + (1461967583256089/25000000000000 : ℝ)*(f.sum) + (102211381053/187900000000000000000000000 : ℝ)*base65 + (659595979399844789/93950000000000000000000000000000 : ℝ)*base67 + (1321462850177744789/93950000000000000000000000000000 : ℝ)*base69 + (32813847726455211/93950000000000000000000000000000 : ℝ)*base72 + (1025402748033/469750000000000000000000000 : ℝ)*base74 + (385634290096844789/93950000000000000000000000000000 : ℝ)*base75 + (484217189227005211/93950000000000000000000000000000 : ℝ)*base78 + (1121714462801544789/93950000000000000000000000000000 : ℝ)*base79 + (987502594243/375800000000000000000000000 : ℝ)*base81 + (9785209/5000000000000000000000 : ℝ)*base90 + (9785209/5000000000000000000000 : ℝ)*base92 + (9785209/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1305_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153272553/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5497/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11049/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1305_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1305_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153272553/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16259/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9599/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11049/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1305_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1305_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1305_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (533/128 : ℝ) ≤ p) (hpb : p ≤ (4265/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153272553/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16259/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9599/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11049/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1305_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
