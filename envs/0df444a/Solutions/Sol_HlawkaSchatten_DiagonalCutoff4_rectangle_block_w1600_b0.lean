-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1600_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:38:32.754807+00:00
-- url     : https://prove2.me/submissions/6acb6c4a-0152-4a10-a0fe-a23718de017d

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
theorem support_rectangle_w1600_s0_0 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1584602521/10000000000 : ℝ)*x 0 + (2925406303/5000000000 : ℝ)*x 1 + (4885432719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1584602521/10000000000 : ℝ)^4719 ≤ (4755139525199/50000000000000 : ℝ)^3695 := by
    have hnat : (1584602521 : ℕ)^4719*50000000000000^3695 ≤ 4755139525199^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584602521 10000000000 4755139525199 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2925406303/5000000000 : ℝ)^4719 ≤ (10086361129211/20000000000000 : ℝ)^3695 := by
    have hnat : (2925406303 : ℕ)^4719*20000000000000^3695 ≤ 10086361129211^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2925406303 5000000000 10086361129211 20000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4885432719/10000000000 : ℝ)^4719 ≤ (10014478820011/25000000000000 : ℝ)^3695 := by
    have hnat : (4885432719 : ℕ)^4719*25000000000000^3695 ≤ 10014478820011^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4885432719 10000000000 10014478820011 25000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1584602521/10000000000 : ℝ), (2925406303/5000000000 : ℝ), (4885432719/10000000000 : ℝ)] ![(4755139525199/50000000000000 : ℝ), (10086361129211/20000000000000 : ℝ), (10014478820011/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1584602521/10000000000 : ℝ)|^4719 ≤ (4755139525199/50000000000000 : ℝ)^3695
        have hw : |(-1584602521/10000000000 : ℝ)|=(1584602521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2925406303/5000000000 : ℝ)|^4719 ≤ (10086361129211/20000000000000 : ℝ)^3695
        have hw : |(2925406303/5000000000 : ℝ)|=(2925406303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4885432719/10000000000 : ℝ)|^4719 ≤ (10014478820011/25000000000000 : ℝ)^3695
        have hw : |(4885432719/10000000000 : ℝ)|=(4885432719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s0_1 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5457858073/10000000000 : ℝ)*x 0 + (-265040107/1250000000 : ℝ)*x 1 + (4885432557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5457858073/10000000000 : ℝ)^4719 ≤ (23073468491737/50000000000000 : ℝ)^3695 := by
    have hnat : (5457858073 : ℕ)^4719*50000000000000^3695 ≤ 23073468491737^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457858073 10000000000 23073468491737 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265040107/1250000000 : ℝ)^4719 ≤ (13795149419147/100000000000000 : ℝ)^3695 := by
    have hnat : (265040107 : ℕ)^4719*100000000000000^3695 ≤ 13795149419147^3695*1250000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265040107 1250000000 13795149419147 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4885432557/10000000000 : ℝ)^4719 ≤ (20028956791807/50000000000000 : ℝ)^3695 := by
    have hnat : (4885432557 : ℕ)^4719*50000000000000^3695 ≤ 20028956791807^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4885432557 10000000000 20028956791807 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5457858073/10000000000 : ℝ), (-265040107/1250000000 : ℝ), (4885432557/10000000000 : ℝ)] ![(23073468491737/50000000000000 : ℝ), (13795149419147/100000000000000 : ℝ), (20028956791807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5457858073/10000000000 : ℝ)|^4719 ≤ (23073468491737/50000000000000 : ℝ)^3695
        have hw : |(5457858073/10000000000 : ℝ)|=(5457858073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-265040107/1250000000 : ℝ)|^4719 ≤ (13795149419147/100000000000000 : ℝ)^3695
        have hw : |(-265040107/1250000000 : ℝ)|=(265040107/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4885432557/10000000000 : ℝ)|^4719 ≤ (20028956791807/50000000000000 : ℝ)^3695
        have hw : |(4885432557/10000000000 : ℝ)|=(4885432557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s0_2 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2728928993/5000000000 : ℝ)*x 0 + (610679073/1250000000 : ℝ)*x 1 + (-424064187/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2728928993/5000000000 : ℝ)^4719 ≤ (2307346802201/5000000000000 : ℝ)^3695 := by
    have hnat : (2728928993 : ℕ)^4719*5000000000000^3695 ≤ 2307346802201^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728928993 5000000000 2307346802201 5000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (610679073/1250000000 : ℝ)^4719 ≤ (40057913866353/100000000000000 : ℝ)^3695 := by
    have hnat : (610679073 : ℕ)^4719*100000000000000^3695 ≤ 40057913866353^3695*1250000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610679073 1250000000 40057913866353 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424064187/2000000000 : ℝ)^4719 ≤ (551806003023/4000000000000 : ℝ)^3695 := by
    have hnat : (424064187 : ℕ)^4719*4000000000000^3695 ≤ 551806003023^3695*2000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424064187 2000000000 551806003023 4000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2728928993/5000000000 : ℝ), (610679073/1250000000 : ℝ), (-424064187/2000000000 : ℝ)] ![(2307346802201/5000000000000 : ℝ), (40057913866353/100000000000000 : ℝ), (551806003023/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2728928993/5000000000 : ℝ)|^4719 ≤ (2307346802201/5000000000000 : ℝ)^3695
        have hw : |(2728928993/5000000000 : ℝ)|=(2728928993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(610679073/1250000000 : ℝ)|^4719 ≤ (40057913866353/100000000000000 : ℝ)^3695
        have hw : |(610679073/1250000000 : ℝ)|=(610679073/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-424064187/2000000000 : ℝ)|^4719 ≤ (551806003023/4000000000000 : ℝ)^3695
        have hw : |(-424064187/2000000000 : ℝ)|=(424064187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s0_3 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4114719329/10000000000 : ℝ)*x 0 + (3072783033/10000000000 : ℝ)*x 1 + (5413844961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4114719329/10000000000 : ℝ)^4719 ≤ (32170798137873/100000000000000 : ℝ)^3695 := by
    have hnat : (4114719329 : ℕ)^4719*100000000000000^3695 ≤ 32170798137873^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4114719329 10000000000 32170798137873 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3072783033/10000000000 : ℝ)^4719 ≤ (11078500200831/50000000000000 : ℝ)^3695 := by
    have hnat : (3072783033 : ℕ)^4719*50000000000000^3695 ≤ 11078500200831^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3072783033 10000000000 11078500200831 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413844961/10000000000 : ℝ)^4719 ≤ (456722014421/1000000000000 : ℝ)^3695 := by
    have hnat : (5413844961 : ℕ)^4719*1000000000000^3695 ≤ 456722014421^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413844961 10000000000 456722014421 1000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4114719329/10000000000 : ℝ), (3072783033/10000000000 : ℝ), (5413844961/10000000000 : ℝ)] ![(32170798137873/100000000000000 : ℝ), (11078500200831/50000000000000 : ℝ), (456722014421/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4114719329/10000000000 : ℝ)|^4719 ≤ (32170798137873/100000000000000 : ℝ)^3695
        have hw : |(4114719329/10000000000 : ℝ)|=(4114719329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3072783033/10000000000 : ℝ)|^4719 ≤ (11078500200831/50000000000000 : ℝ)^3695
        have hw : |(3072783033/10000000000 : ℝ)|=(3072783033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413844961/10000000000 : ℝ)|^4719 ≤ (456722014421/1000000000000 : ℝ)^3695
        have hw : |(5413844961/10000000000 : ℝ)|=(5413844961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s0_4 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-158753499/1000000000 : ℝ)*x 0 + (4909981377/10000000000 : ℝ)*x 1 + (5825386659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (158753499/1000000000 : ℝ)^4719 ≤ (9532761994681/100000000000000 : ℝ)^3695 := by
    have hnat : (158753499 : ℕ)^4719*100000000000000^3695 ≤ 9532761994681^3695*1000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158753499 1000000000 9532761994681 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4909981377/10000000000 : ℝ)^4719 ≤ (503939529953/1250000000000 : ℝ)^3695 := by
    have hnat : (4909981377 : ℕ)^4719*1250000000000^3695 ≤ 503939529953^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4909981377 10000000000 503939529953 1250000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5825386659/10000000000 : ℝ)^4719 ≤ (6269009448897/12500000000000 : ℝ)^3695 := by
    have hnat : (5825386659 : ℕ)^4719*12500000000000^3695 ≤ 6269009448897^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5825386659 10000000000 6269009448897 12500000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-158753499/1000000000 : ℝ), (4909981377/10000000000 : ℝ), (5825386659/10000000000 : ℝ)] ![(9532761994681/100000000000000 : ℝ), (503939529953/1250000000000 : ℝ), (6269009448897/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-158753499/1000000000 : ℝ)|^4719 ≤ (9532761994681/100000000000000 : ℝ)^3695
        have hw : |(-158753499/1000000000 : ℝ)|=(158753499/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4909981377/10000000000 : ℝ)|^4719 ≤ (503939529953/1250000000000 : ℝ)^3695
        have hw : |(4909981377/10000000000 : ℝ)|=(4909981377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5825386659/10000000000 : ℝ)|^4719 ≤ (6269009448897/12500000000000 : ℝ)^3695
        have hw : |(5825386659/10000000000 : ℝ)|=(5825386659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s0_5 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5194182181/10000000000 : ℝ)*x 0 + (-1180366277/10000000000 : ℝ)*x 1 + (1456346723/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5194182181/10000000000 : ℝ)^4719 ≤ (43318967382251/100000000000000 : ℝ)^3695 := by
    have hnat : (5194182181 : ℕ)^4719*100000000000000^3695 ≤ 43318967382251^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194182181 10000000000 43318967382251 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1180366277/10000000000 : ℝ)^4719 ≤ (6528954459139/100000000000000 : ℝ)^3695 := by
    have hnat : (1180366277 : ℕ)^4719*100000000000000^3695 ≤ 6528954459139^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1180366277 10000000000 6528954459139 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1456346723/2500000000 : ℝ)^4719 ≤ (50152078153037/100000000000000 : ℝ)^3695 := by
    have hnat : (1456346723 : ℕ)^4719*100000000000000^3695 ≤ 50152078153037^3695*2500000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1456346723 2500000000 50152078153037 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5194182181/10000000000 : ℝ), (-1180366277/10000000000 : ℝ), (1456346723/2500000000 : ℝ)] ![(43318967382251/100000000000000 : ℝ), (6528954459139/100000000000000 : ℝ), (50152078153037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5194182181/10000000000 : ℝ)|^4719 ≤ (43318967382251/100000000000000 : ℝ)^3695
        have hw : |(5194182181/10000000000 : ℝ)|=(5194182181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1180366277/10000000000 : ℝ)|^4719 ≤ (6528954459139/100000000000000 : ℝ)^3695
        have hw : |(-1180366277/10000000000 : ℝ)|=(1180366277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1456346723/2500000000 : ℝ)|^4719 ≤ (50152078153037/100000000000000 : ℝ)^3695
        have hw : |(1456346723/2500000000 : ℝ)|=(1456346723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s0_6 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597091119/5000000000 : ℝ)*x 0 + (2912693339/5000000000 : ℝ)*x 1 + (-1180366523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597091119/5000000000 : ℝ)^4719 ≤ (43318967989367/100000000000000 : ℝ)^3695 := by
    have hnat : (2597091119 : ℕ)^4719*100000000000000^3695 ≤ 43318967989367^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597091119 5000000000 43318967989367 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2912693339/5000000000 : ℝ)^4719 ≤ (50152075800083/100000000000000 : ℝ)^3695 := by
    have hnat : (2912693339 : ℕ)^4719*100000000000000^3695 ≤ 50152075800083^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2912693339 5000000000 50152075800083 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1180366523/10000000000 : ℝ)^4719 ≤ (652895619693/10000000000000 : ℝ)^3695 := by
    have hnat : (1180366523 : ℕ)^4719*10000000000000^3695 ≤ 652895619693^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1180366523 10000000000 652895619693 10000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597091119/5000000000 : ℝ), (2912693339/5000000000 : ℝ), (-1180366523/10000000000 : ℝ)] ![(43318967989367/100000000000000 : ℝ), (50152075800083/100000000000000 : ℝ), (652895619693/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597091119/5000000000 : ℝ)|^4719 ≤ (43318967989367/100000000000000 : ℝ)^3695
        have hw : |(2597091119/5000000000 : ℝ)|=(2597091119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2912693339/5000000000 : ℝ)|^4719 ≤ (50152075800083/100000000000000 : ℝ)^3695
        have hw : |(2912693339/5000000000 : ℝ)|=(2912693339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1180366523/10000000000 : ℝ)|^4719 ≤ (652895619693/10000000000000 : ℝ)^3695
        have hw : |(-1180366523/10000000000 : ℝ)|=(1180366523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s0_7 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4121831441/10000000000 : ℝ)*x 0 + (2677157027/5000000000 : ℝ)*x 1 + (391805097/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4121831441/10000000000 : ℝ)^4719 ≤ (32241831063211/100000000000000 : ℝ)^3695 := by
    have hnat : (4121831441 : ℕ)^4719*100000000000000^3695 ≤ 32241831063211^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4121831441 10000000000 32241831063211 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2677157027/5000000000 : ℝ)^4719 ≤ (45031788392877/100000000000000 : ℝ)^3695 := by
    have hnat : (2677157027 : ℕ)^4719*100000000000000^3695 ≤ 45031788392877^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677157027 5000000000 45031788392877 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (391805097/1250000000 : ℝ)^4719 ≤ (11363190262819/50000000000000 : ℝ)^3695 := by
    have hnat : (391805097 : ℕ)^4719*50000000000000^3695 ≤ 11363190262819^3695*1250000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391805097 1250000000 11363190262819 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4121831441/10000000000 : ℝ), (2677157027/5000000000 : ℝ), (391805097/1250000000 : ℝ)] ![(32241831063211/100000000000000 : ℝ), (45031788392877/100000000000000 : ℝ), (11363190262819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4121831441/10000000000 : ℝ)|^4719 ≤ (32241831063211/100000000000000 : ℝ)^3695
        have hw : |(4121831441/10000000000 : ℝ)|=(4121831441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2677157027/5000000000 : ℝ)|^4719 ≤ (45031788392877/100000000000000 : ℝ)^3695
        have hw : |(2677157027/5000000000 : ℝ)|=(2677157027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(391805097/1250000000 : ℝ)|^4719 ≤ (11363190262819/50000000000000 : ℝ)^3695
        have hw : |(391805097/1250000000 : ℝ)|=(391805097/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1600_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21406347/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1901/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (979/4000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4715/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4715 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4715*1^1024 ≤ 0^1024*1^4715 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4715 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4715/1024 : ℝ) ≤ (1471256311679772167/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4715 ≤ (1471256311679772167/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4715*100000000000000000000^1024 ≤ 1471256311679772167^1024*5^4715 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1471256311679772167 100000000000000000000 4715 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1471256311679772167/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4715/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4715 := by
      have hnat : (1 : ℕ)^1024*1^4715 ≤ 1^4715*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4715 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101471256311679772167/100000000000000000000 : ℝ) ≤ (2006354043525281/2000000000000000 : ℝ) ^ (4715/1024 : ℝ) := by
    have hpowers : (101471256311679772167/100000000000000000000 : ℝ)^1024 ≤ (2006354043525281/2000000000000000 : ℝ)^4715 := by
      have hnat : (101471256311679772167 : ℕ)^1024*2000000000000000^4715 ≤ 2006354043525281^4715*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101471256311679772167 100000000000000000000 2006354043525281 2000000000000000 1024 4715 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2006354043525281/2000000000000000 : ℝ)) (X := (101471256311679772167/100000000000000000000 : ℝ)) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51471256311679772167/50000000000000000000 : ℝ) ≤ (1006354043525281/1000000000000000 : ℝ) ^ (4715/1024 : ℝ) := by
    have hpowers : (51471256311679772167/50000000000000000000 : ℝ)^1024 ≤ (1006354043525281/1000000000000000 : ℝ)^4715 := by
      have hnat : (51471256311679772167 : ℕ)^1024*1000000000000000^4715 ≤ 1006354043525281^4715*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51471256311679772167 50000000000000000000 1006354043525281 1000000000000000 1024 4715 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1006354043525281/1000000000000000 : ℝ)) (X := (51471256311679772167/50000000000000000000 : ℝ)) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(6354043525281/800000000000000 : ℝ)*(0 : ℝ))^(4715/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6354043525281/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1471256311679772167/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(6354043525281/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4715/1024 : ℝ) := by
    rw [show (1 : ℝ)+(6354043525281/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2006354043525281/2000000000000000 : ℝ) by norm_num, show 1+(1471256311679772167/100000000000000000000 : ℝ)+(0 : ℝ)=(101471256311679772167/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1471256311679772167/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(6354043525281/800000000000000 : ℝ)*(2/5 : ℝ))^(4715/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6354043525281/800000000000000 : ℝ)*(2/5 : ℝ)=(1006354043525281/1000000000000000 : ℝ) by norm_num, show 1+2*(1471256311679772167/100000000000000000000 : ℝ)=(51471256311679772167/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(6354043525281/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4715/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6354043525281/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(6354043525281/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4715/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6354043525281/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(6354043525281/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4715/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6354043525281/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1584602521/10000000000 : ℝ)*X 0 0+(2925406303/5000000000 : ℝ)*X 0 1+(4885432719/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5457858073/10000000000 : ℝ)*X 1 0+(-265040107/1250000000 : ℝ)*X 1 1+(4885432557/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2728928993/5000000000 : ℝ)*X 2 0+(610679073/1250000000 : ℝ)*X 2 1+(-424064187/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4114719329/10000000000 : ℝ)*X 0 0+(3072783033/10000000000 : ℝ)*X 0 1+(5413844961/10000000000 : ℝ)*X 0 2+(4114719329/10000000000 : ℝ)*X 1 0+(3072783033/10000000000 : ℝ)*X 1 1+(5413844961/10000000000 : ℝ)*X 1 2+(4114719329/10000000000 : ℝ)*X 2 0+(3072783033/10000000000 : ℝ)*X 2 1+(5413844961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-158753499/1000000000 : ℝ)*X 0 0+(4909981377/10000000000 : ℝ)*X 0 1+(5825386659/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5194182181/10000000000 : ℝ)*X 1 0+(-1180366277/10000000000 : ℝ)*X 1 1+(1456346723/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2597091119/5000000000 : ℝ)*X 2 0+(2912693339/5000000000 : ℝ)*X 2 1+(-1180366523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4121831441/10000000000 : ℝ)*X 0 0+(2677157027/5000000000 : ℝ)*X 0 1+(391805097/1250000000 : ℝ)*X 0 2+(4121831441/10000000000 : ℝ)*X 1 0+(2677157027/5000000000 : ℝ)*X 1 1+(391805097/1250000000 : ℝ)*X 1 2+(4121831441/10000000000 : ℝ)*X 2 0+(2677157027/5000000000 : ℝ)*X 2 1+(391805097/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31526783675451986629731/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2203353/10000000000000 : ℝ)*(base1) + (137920521/25000000000000 : ℝ)*(base19) + (535170067/100000000000000 : ℝ)*(base23) + (82502313/100000000000000 : ℝ)*(upper3) + (3350899/6250000000000 : ℝ)*(upper5) + (731511925712817/100000000000000 : ℝ)*(major0) + (731511925712817/100000000000000 : ℝ)*(major1) + (731511925712817/100000000000000 : ℝ)*(major2) + (1035863624309823/100000000000000 : ℝ)*(sp0) + (129483110210301/12500000000000 : ℝ)*(sp1) + (517932449097213/50000000000000 : ℝ)*(sp2) + (427157373543043/100000000000000 : ℝ)*(sp3) + (9155441/500000000000 : ℝ)*(sp4) + (458697643/50000000000000 : ℝ)*(sp7) + (427158312971859/100000000000000 : ℝ)*(f.failure) + (258966358341123/25000000000000 : ℝ)*(f.sum) + (88023854373423/40000000000000000000000000000 : ℝ)*base66 + (129778034853423/80000000000000000000000000000 : ℝ)*base68 + (160909378453423/80000000000000000000000000000 : ℝ)*base70 + (62283880666577/80000000000000000000000000000 : ℝ)*base71 + (98402019373423/40000000000000000000000000000 : ℝ)*base74 + (305671844026577/80000000000000000000000000000 : ℝ)*base75 + (305708619493423/80000000000000000000000000000 : ℝ)*base78 + (85385766533423/80000000000000000000000000000 : ℝ)*base80 + (41785712733423/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (2489073/1250000000000000000000 : ℝ)*base89 + (2489073/1250000000000000000000 : ℝ)*base91 + (2489073/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21947132067917188420161/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (464894271/25000000000000 : ℝ)*(base19) + (1889311947/100000000000000 : ℝ)*(base23) + (19255373/10000000000000 : ℝ)*(base32) + (6411459/2000000000000 : ℝ)*(upper3) + (30764679/20000000000000 : ℝ)*(upper5) + (96430453048173/12500000000000 : ℝ)*(major0) + (96430453048173/12500000000000 : ℝ)*(major1) + (96430453048173/12500000000000 : ℝ)*(major2) + (511920307/10000000000000 : ℝ)*(sp1) + (5468805629/100000000000000 : ℝ)*(sp2) + (546205484292563/50000000000000 : ℝ)*(sp4) + (1092403989804973/100000000000000 : ℝ)*(sp5) + (21848072209351/2000000000000 : ℝ)*(sp6) + (450475795003479/100000000000000 : ℝ)*(sp7) + (450475987557209/100000000000000 : ℝ)*(f.failure) + (546205484292563/50000000000000 : ℝ)*(f.sum) + (3519086133387/5000000000000000000000000000 : ℝ)*base66 + (44243112681613/10000000000000000000000000000 : ℝ)*base67 + (29664098981613/10000000000000000000000000000 : ℝ)*base69 + (40821498258387/10000000000000000000000000000 : ℝ)*base72 + (40959684236613/5000000000000000000000000000 : ℝ)*base73 + (113503199738387/10000000000000000000000000000 : ℝ)*base76 + (607403031613/10000000000000000000000000000 : ℝ)*base77 + (25229955341613/10000000000000000000000000000 : ℝ)*base79 + (13985596666613/5000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1794477/1250000000000000000000 : ℝ)*base90 + (1794477/1250000000000000000000 : ℝ)*base92 + (1794477/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1600_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21406347/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1901/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (979/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1600_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1600_s1_0 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-85635093/500000000 : ℝ)*x 0 + (5539552311/10000000000 : ℝ)*x 1 + (1278485081/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85635093/500000000 : ℝ)^4719 ≤ (1312867951137/12500000000000 : ℝ)^3695 := by
    have hnat : (85635093 : ℕ)^4719*12500000000000^3695 ≤ 1312867951137^3695*500000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85635093 500000000 1312867951137 12500000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5539552311/10000000000 : ℝ)^4719 ≤ (47030920584627/100000000000000 : ℝ)^3695 := by
    have hnat : (5539552311 : ℕ)^4719*100000000000000^3695 ≤ 47030920584627^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5539552311 10000000000 47030920584627 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1278485081/2500000000 : ℝ)^4719 ≤ (10616533949267/25000000000000 : ℝ)^3695 := by
    have hnat : (1278485081 : ℕ)^4719*25000000000000^3695 ≤ 10616533949267^3695*2500000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1278485081 2500000000 10616533949267 25000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85635093/500000000 : ℝ), (5539552311/10000000000 : ℝ), (1278485081/2500000000 : ℝ)] ![(1312867951137/12500000000000 : ℝ), (47030920584627/100000000000000 : ℝ), (10616533949267/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85635093/500000000 : ℝ)|^4719 ≤ (1312867951137/12500000000000 : ℝ)^3695
        have hw : |(-85635093/500000000 : ℝ)|=(85635093/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5539552311/10000000000 : ℝ)|^4719 ≤ (47030920584627/100000000000000 : ℝ)^3695
        have hw : |(5539552311/10000000000 : ℝ)|=(5539552311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1278485081/2500000000 : ℝ)|^4719 ≤ (10616533949267/25000000000000 : ℝ)^3695
        have hw : |(1278485081/2500000000 : ℝ)|=(1278485081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s1_1 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2687496783/5000000000 : ℝ)*x 0 + (-483919777/2500000000 : ℝ)*x 1 + (5113940177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687496783/5000000000 : ℝ)^4719 ≤ (9050805790099/20000000000000 : ℝ)^3695 := by
    have hnat : (2687496783 : ℕ)^4719*20000000000000^3695 ≤ 9050805790099^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687496783 5000000000 9050805790099 20000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (483919777/2500000000 : ℝ)^4719 ≤ (3069959199817/25000000000000 : ℝ)^3695 := by
    have hnat : (483919777 : ℕ)^4719*25000000000000^3695 ≤ 3069959199817^3695*2500000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483919777 2500000000 3069959199817 25000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5113940177/10000000000 : ℝ)^4719 ≤ (4246613423809/10000000000000 : ℝ)^3695 := by
    have hnat : (5113940177 : ℕ)^4719*10000000000000^3695 ≤ 4246613423809^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5113940177 10000000000 4246613423809 10000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687496783/5000000000 : ℝ), (-483919777/2500000000 : ℝ), (5113940177/10000000000 : ℝ)] ![(9050805790099/20000000000000 : ℝ), (3069959199817/25000000000000 : ℝ), (4246613423809/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687496783/5000000000 : ℝ)|^4719 ≤ (9050805790099/20000000000000 : ℝ)^3695
        have hw : |(2687496783/5000000000 : ℝ)|=(2687496783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-483919777/2500000000 : ℝ)|^4719 ≤ (3069959199817/25000000000000 : ℝ)^3695
        have hw : |(-483919777/2500000000 : ℝ)|=(483919777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5113940177/10000000000 : ℝ)|^4719 ≤ (4246613423809/10000000000000 : ℝ)^3695
        have hw : |(5113940177/10000000000 : ℝ)|=(5113940177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s1_2 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5374993193/10000000000 : ℝ)*x 0 + (5113940499/10000000000 : ℝ)*x 1 + (-1935679181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374993193/10000000000 : ℝ)^4719 ≤ (45254024939763/100000000000000 : ℝ)^3695 := by
    have hnat : (5374993193 : ℕ)^4719*100000000000000^3695 ≤ 45254024939763^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374993193 10000000000 45254024939763 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5113940499/10000000000 : ℝ)^4719 ≤ (21233068826497/50000000000000 : ℝ)^3695 := by
    have hnat : (5113940499 : ℕ)^4719*50000000000000^3695 ≤ 21233068826497^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5113940499 10000000000 21233068826497 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1935679181/10000000000 : ℝ)^4719 ≤ (6139918695359/50000000000000 : ℝ)^3695 := by
    have hnat : (1935679181 : ℕ)^4719*50000000000000^3695 ≤ 6139918695359^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935679181 10000000000 6139918695359 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374993193/10000000000 : ℝ), (5113940499/10000000000 : ℝ), (-1935679181/10000000000 : ℝ)] ![(45254024939763/100000000000000 : ℝ), (21233068826497/50000000000000 : ℝ), (6139918695359/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374993193/10000000000 : ℝ)|^4719 ≤ (45254024939763/100000000000000 : ℝ)^3695
        have hw : |(5374993193/10000000000 : ℝ)|=(5374993193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5113940499/10000000000 : ℝ)|^4719 ≤ (21233068826497/50000000000000 : ℝ)^3695
        have hw : |(5113940499/10000000000 : ℝ)|=(5113940499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1935679181/10000000000 : ℝ)|^4719 ≤ (6139918695359/50000000000000 : ℝ)^3695
        have hw : |(-1935679181/10000000000 : ℝ)|=(1935679181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s1_3 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2104211877/5000000000 : ℝ)*x 0 + (3717032209/10000000000 : ℝ)*x 1 + (2374573973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2104211877/5000000000 : ℝ)^4719 ≤ (33109392867183/100000000000000 : ℝ)^3695 := by
    have hnat : (2104211877 : ℕ)^4719*100000000000000^3695 ≤ 33109392867183^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104211877 5000000000 33109392867183 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3717032209/10000000000 : ℝ)^4719 ≤ (7063570750759/25000000000000 : ℝ)^3695 := by
    have hnat : (3717032209 : ℕ)^4719*25000000000000^3695 ≤ 7063570750759^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3717032209 10000000000 7063570750759 25000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2374573973/5000000000 : ℝ)^4719 ≤ (38636324117559/100000000000000 : ℝ)^3695 := by
    have hnat : (2374573973 : ℕ)^4719*100000000000000^3695 ≤ 38636324117559^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2374573973 5000000000 38636324117559 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2104211877/5000000000 : ℝ), (3717032209/10000000000 : ℝ), (2374573973/5000000000 : ℝ)] ![(33109392867183/100000000000000 : ℝ), (7063570750759/25000000000000 : ℝ), (38636324117559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2104211877/5000000000 : ℝ)|^4719 ≤ (33109392867183/100000000000000 : ℝ)^3695
        have hw : |(2104211877/5000000000 : ℝ)|=(2104211877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3717032209/10000000000 : ℝ)|^4719 ≤ (7063570750759/25000000000000 : ℝ)^3695
        have hw : |(3717032209/10000000000 : ℝ)|=(3717032209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2374573973/5000000000 : ℝ)|^4719 ≤ (38636324117559/100000000000000 : ℝ)^3695
        have hw : |(2374573973/5000000000 : ℝ)|=(2374573973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s1_4 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1712946947/10000000000 : ℝ)*x 0 + (319916419/625000000 : ℝ)*x 1 + (2767377603/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1712946947/10000000000 : ℝ)^4719 ≤ (10504863133713/100000000000000 : ℝ)^3695 := by
    have hnat : (1712946947 : ℕ)^4719*100000000000000^3695 ≤ 10504863133713^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1712946947 10000000000 10504863133713 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (319916419/625000000 : ℝ)^4719 ≤ (42516224421919/100000000000000 : ℝ)^3695 := by
    have hnat : (319916419 : ℕ)^4719*100000000000000^3695 ≤ 42516224421919^3695*625000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319916419 625000000 42516224421919 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2767377603/5000000000 : ℝ)^4719 ≤ (5872364053751/12500000000000 : ℝ)^3695 := by
    have hnat : (2767377603 : ℕ)^4719*12500000000000^3695 ≤ 5872364053751^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2767377603 5000000000 5872364053751 12500000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1712946947/10000000000 : ℝ), (319916419/625000000 : ℝ), (2767377603/5000000000 : ℝ)] ![(10504863133713/100000000000000 : ℝ), (42516224421919/100000000000000 : ℝ), (5872364053751/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1712946947/10000000000 : ℝ)|^4719 ≤ (10504863133713/100000000000000 : ℝ)^3695
        have hw : |(-1712946947/10000000000 : ℝ)|=(1712946947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(319916419/625000000 : ℝ)|^4719 ≤ (42516224421919/100000000000000 : ℝ)^3695
        have hw : |(319916419/625000000 : ℝ)|=(319916419/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2767377603/5000000000 : ℝ)|^4719 ≤ (5872364053751/12500000000000 : ℝ)^3695
        have hw : |(2767377603/5000000000 : ℝ)|=(2767377603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s1_5 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5261947953/10000000000 : ℝ)*x 0 + (-757432009/5000000000 : ℝ)*x 1 + (5534755491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5261947953/10000000000 : ℝ)^4719 ≤ (44042051459577/100000000000000 : ℝ)^3695 := by
    have hnat : (5261947953 : ℕ)^4719*100000000000000^3695 ≤ 44042051459577^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261947953 10000000000 44042051459577 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (757432009/5000000000 : ℝ)^4719 ≤ (4489516505833/50000000000000 : ℝ)^3695 := by
    have hnat : (757432009 : ℕ)^4719*50000000000000^3695 ≤ 4489516505833^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      757432009 5000000000 4489516505833 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5534755491/10000000000 : ℝ)^4719 ≤ (9395783103897/20000000000000 : ℝ)^3695 := by
    have hnat : (5534755491 : ℕ)^4719*20000000000000^3695 ≤ 9395783103897^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5534755491 10000000000 9395783103897 20000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5261947953/10000000000 : ℝ), (-757432009/5000000000 : ℝ), (5534755491/10000000000 : ℝ)] ![(44042051459577/100000000000000 : ℝ), (4489516505833/50000000000000 : ℝ), (9395783103897/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5261947953/10000000000 : ℝ)|^4719 ≤ (44042051459577/100000000000000 : ℝ)^3695
        have hw : |(5261947953/10000000000 : ℝ)|=(5261947953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-757432009/5000000000 : ℝ)|^4719 ≤ (4489516505833/50000000000000 : ℝ)^3695
        have hw : |(-757432009/5000000000 : ℝ)|=(757432009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5534755491/10000000000 : ℝ)|^4719 ≤ (9395783103897/20000000000000 : ℝ)^3695
        have hw : |(5534755491/10000000000 : ℝ)|=(5534755491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s1_6 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2630973701/5000000000 : ℝ)*x 0 + (2767377847/5000000000 : ℝ)*x 1 + (-302972901/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2630973701/5000000000 : ℝ)^4719 ≤ (22021022784837/50000000000000 : ℝ)^3695 := by
    have hnat : (2630973701 : ℕ)^4719*50000000000000^3695 ≤ 22021022784837^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630973701 5000000000 22021022784837 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2767377847/5000000000 : ℝ)^4719 ≤ (46978917720059/100000000000000 : ℝ)^3695 := by
    have hnat : (2767377847 : ℕ)^4719*100000000000000^3695 ≤ 46978917720059^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2767377847 5000000000 46978917720059 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (302972901/2000000000 : ℝ)^4719 ≤ (4489518349109/50000000000000 : ℝ)^3695 := by
    have hnat : (302972901 : ℕ)^4719*50000000000000^3695 ≤ 4489518349109^3695*2000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302972901 2000000000 4489518349109 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2630973701/5000000000 : ℝ), (2767377847/5000000000 : ℝ), (-302972901/2000000000 : ℝ)] ![(22021022784837/50000000000000 : ℝ), (46978917720059/100000000000000 : ℝ), (4489518349109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2630973701/5000000000 : ℝ)|^4719 ≤ (22021022784837/50000000000000 : ℝ)^3695
        have hw : |(2630973701/5000000000 : ℝ)|=(2630973701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2767377847/5000000000 : ℝ)|^4719 ≤ (46978917720059/100000000000000 : ℝ)^3695
        have hw : |(2767377847/5000000000 : ℝ)|=(2767377847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-302972901/2000000000 : ℝ)|^4719 ≤ (4489518349109/50000000000000 : ℝ)^3695
        have hw : |(-302972901/2000000000 : ℝ)|=(302972901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s1_7 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2104508647/5000000000 : ℝ)*x 0 + (14805303/31250000 : ℝ)*x 1 + (1864332177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2104508647/5000000000 : ℝ)^4719 ≤ (1655767835211/5000000000000 : ℝ)^3695 := by
    have hnat : (2104508647 : ℕ)^4719*5000000000000^3695 ≤ 1655767835211^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104508647 5000000000 1655767835211 5000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (14805303/31250000 : ℝ)^4719 ≤ (38517388122199/100000000000000 : ℝ)^3695 := by
    have hnat : (14805303 : ℕ)^4719*100000000000000^3695 ≤ 38517388122199^3695*31250000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14805303 31250000 38517388122199 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1864332177/5000000000 : ℝ)^4719 ≤ (14183627583637/50000000000000 : ℝ)^3695 := by
    have hnat : (1864332177 : ℕ)^4719*50000000000000^3695 ≤ 14183627583637^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1864332177 5000000000 14183627583637 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2104508647/5000000000 : ℝ), (14805303/31250000 : ℝ), (1864332177/5000000000 : ℝ)] ![(1655767835211/5000000000000 : ℝ), (38517388122199/100000000000000 : ℝ), (14183627583637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2104508647/5000000000 : ℝ)|^4719 ≤ (1655767835211/5000000000000 : ℝ)^3695
        have hw : |(2104508647/5000000000 : ℝ)|=(2104508647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(14805303/31250000 : ℝ)|^4719 ≤ (38517388122199/100000000000000 : ℝ)^3695
        have hw : |(14805303/31250000 : ℝ)|=(14805303/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1864332177/5000000000 : ℝ)|^4719 ≤ (14183627583637/50000000000000 : ℝ)^3695
        have hw : |(1864332177/5000000000 : ℝ)|=(1864332177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1600_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21406347/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (979/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1901/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1789/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (449/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (979/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1901/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (979/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1901/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (979/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1901/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (979/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1901/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (979/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1901/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (979/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1901/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1901/50000 : ℝ) ^ (4715/1024 : ℝ) ≤ (2895188638381/10000000000000000000 : ℝ) := by
    have hpowers : (1901/50000 : ℝ)^4715 ≤ (2895188638381/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1901 : ℕ)^4715*10000000000000000000^1024 ≤ 2895188638381^1024*50000^4715 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1901 50000 2895188638381 10000000000000000000 4715 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1901/50000 : ℝ)) (X := (2895188638381/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (979/4000 : ℝ) ^ (4715/1024 : ℝ) ≤ (76621112649552663/50000000000000000000 : ℝ) := by
    have hpowers : (979/4000 : ℝ)^4715 ≤ (76621112649552663/50000000000000000000 : ℝ)^1024 := by
      have hnat : (979 : ℕ)^4715*50000000000000000000^1024 ≤ 76621112649552663^1024*4000^4715 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        979 4000 76621112649552663 50000000000000000000 4715 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (979/4000 : ℝ)) (X := (76621112649552663/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000002895188638381/5000000000000000000 : ℝ) ≤ (10000001257549309/10000000000000000 : ℝ) ^ (4715/1024 : ℝ) := by
    have hpowers : (5000002895188638381/5000000000000000000 : ℝ)^1024 ≤ (10000001257549309/10000000000000000 : ℝ)^4715 := by
      have hnat : (5000002895188638381 : ℕ)^1024*10000000000000000^4715 ≤ 10000001257549309^4715*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000002895188638381 5000000000000000000 10000001257549309 10000000000000000 1024 4715 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001257549309/10000000000000000 : ℝ)) (X := (5000002895188638381/5000000000000000000 : ℝ)) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6259579448574093071/6250000000000000000 : ℝ) ≤ (2500831684061303/2500000000000000 : ℝ) ^ (4715/1024 : ℝ) := by
    have hpowers : (6259579448574093071/6250000000000000000 : ℝ)^1024 ≤ (2500831684061303/2500000000000000 : ℝ)^4715 := by
      have hnat : (6259579448574093071 : ℕ)^1024*2500000000000000^4715 ≤ 2500831684061303^4715*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6259579448574093071 6250000000000000000 2500831684061303 2500000000000000 1024 4715 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500831684061303/2500000000000000 : ℝ)) (X := (6259579448574093071/6250000000000000000 : ℝ)) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25076621112649552663/25000000000000000000 : ℝ) ≤ (2001330442988223/2000000000000000 : ℝ) ^ (4715/1024 : ℝ) := by
    have hpowers : (25076621112649552663/25000000000000000000 : ℝ)^1024 ≤ (2001330442988223/2000000000000000 : ℝ)^4715 := by
      have hnat : (25076621112649552663 : ℕ)^1024*2000000000000000^4715 ≤ 2001330442988223^4715*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25076621112649552663 25000000000000000000 2001330442988223 2000000000000000 1024 4715 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001330442988223/2000000000000000 : ℝ)) (X := (25076621112649552663/25000000000000000000 : ℝ)) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2895188638381/10000000000000000000 : ℝ) ≤ ((41340947811462643709/41346000000000000000 : ℝ)+2*(3325478695903/2067300000000000 : ℝ)*(1901/50000 : ℝ))^(4715/1024 : ℝ) := by
    rw [show (41340947811462643709/41346000000000000000 : ℝ)+2*(3325478695903/2067300000000000 : ℝ)*(1901/50000 : ℝ)=(10000001257549309/10000000000000000 : ℝ) by norm_num, show 1+2*(2895188638381/10000000000000000000 : ℝ)=(5000002895188638381/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(76621112649552663/50000000000000000000 : ℝ)+(2895188638381/10000000000000000000 : ℝ) ≤ ((41340947811462643709/41346000000000000000 : ℝ)+(3325478695903/2067300000000000 : ℝ)*((979/4000 : ℝ)+(1901/50000 : ℝ)))^(4715/1024 : ℝ) := by
    rw [show (41340947811462643709/41346000000000000000 : ℝ)+(3325478695903/2067300000000000 : ℝ)*((979/4000 : ℝ)+(1901/50000 : ℝ))=(2500831684061303/2500000000000000 : ℝ) by norm_num, show 1+(76621112649552663/50000000000000000000 : ℝ)+(2895188638381/10000000000000000000 : ℝ)=(6259579448574093071/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(76621112649552663/50000000000000000000 : ℝ) ≤ ((41340947811462643709/41346000000000000000 : ℝ)+2*(3325478695903/2067300000000000 : ℝ)*(979/4000 : ℝ))^(4715/1024 : ℝ) := by
    rw [show (41340947811462643709/41346000000000000000 : ℝ)+2*(3325478695903/2067300000000000 : ℝ)*(979/4000 : ℝ)=(2001330442988223/2000000000000000 : ℝ) by norm_num, show 1+2*(76621112649552663/50000000000000000000 : ℝ)=(25076621112649552663/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (41340947811462643709/41346000000000000000 : ℝ)*(X 1 0+X 2 0)+(3325478695903/2067300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4715/1024 : ℝ)) (lo := (1901/50000 : ℝ)) (hi := (979/4000 : ℝ)) (c := (41340947811462643709/41346000000000000000 : ℝ)) (alpha := (3325478695903/2067300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (41340947811462643709/41346000000000000000 : ℝ)*(X 0 1+X 2 1)+(3325478695903/2067300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4715/1024 : ℝ)) (lo := (1901/50000 : ℝ)) (hi := (979/4000 : ℝ)) (c := (41340947811462643709/41346000000000000000 : ℝ)) (alpha := (3325478695903/2067300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (41340947811462643709/41346000000000000000 : ℝ)*(X 0 2+X 1 2)+(3325478695903/2067300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4715/1024 : ℝ)) (lo := (1901/50000 : ℝ)) (hi := (979/4000 : ℝ)) (c := (41340947811462643709/41346000000000000000 : ℝ)) (alpha := (3325478695903/2067300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-85635093/500000000 : ℝ)*X 0 0+(5539552311/10000000000 : ℝ)*X 0 1+(1278485081/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2687496783/5000000000 : ℝ)*X 1 0+(-483919777/2500000000 : ℝ)*X 1 1+(5113940177/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5374993193/10000000000 : ℝ)*X 2 0+(5113940499/10000000000 : ℝ)*X 2 1+(-1935679181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2104211877/5000000000 : ℝ)*X 0 0+(3717032209/10000000000 : ℝ)*X 0 1+(2374573973/5000000000 : ℝ)*X 0 2+(2104211877/5000000000 : ℝ)*X 1 0+(3717032209/10000000000 : ℝ)*X 1 1+(2374573973/5000000000 : ℝ)*X 1 2+(2104211877/5000000000 : ℝ)*X 2 0+(3717032209/10000000000 : ℝ)*X 2 1+(2374573973/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1712946947/10000000000 : ℝ)*X 0 0+(319916419/625000000 : ℝ)*X 0 1+(2767377603/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5261947953/10000000000 : ℝ)*X 1 0+(-757432009/5000000000 : ℝ)*X 1 1+(5534755491/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2630973701/5000000000 : ℝ)*X 2 0+(2767377847/5000000000 : ℝ)*X 2 1+(-302972901/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2104508647/5000000000 : ℝ)*X 0 0+(14805303/31250000 : ℝ)*X 0 1+(1864332177/5000000000 : ℝ)*X 0 2+(2104508647/5000000000 : ℝ)*X 1 0+(14805303/31250000 : ℝ)*X 1 1+(1864332177/5000000000 : ℝ)*X 1 2+(2104508647/5000000000 : ℝ)*X 2 0+(14805303/31250000 : ℝ)*X 2 1+(1864332177/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25094519991893730998927/2871250000000000000000000000 : ℝ) := by norm_num
    linear_combination (89672503/100000000000000 : ℝ)*(base1) + (234474471/12500000000000 : ℝ)*(base19) + (1712745231/100000000000000 : ℝ)*(base23) + (231622613/100000000000000 : ℝ)*(upper3) + (80906223/50000000000000 : ℝ)*(upper5) + (103702628931963/6250000000000 : ℝ)*(major0) + (103702628931963/6250000000000 : ℝ)*(major1) + (103702628931963/6250000000000 : ℝ)*(major2) + (2349573474797647/100000000000000 : ℝ)*(sp0) + (2349585874446283/100000000000000 : ℝ)*(sp1) + (117479301874841/5000000000000 : ℝ)*(sp2) + (484444809257779/50000000000000 : ℝ)*(sp3) + (3591279227/25000000000000 : ℝ)*(sp4) + (1275212349/20000000000000 : ℝ)*(sp7) + (968896084249807/100000000000000 : ℝ)*(f.failure) + (2349587750242051/100000000000000 : ℝ)*(f.sum) + (31659347823611/17227500000000000000000000000 : ℝ)*base66 + (330266644989321089/86137500000000000000000000000000 : ℝ)*base67 + (10752406869091411/86137500000000000000000000000000 : ℝ)*base70 + (177055982049166411/86137500000000000000000000000000 : ℝ)*base72 + (36980735289709/17227500000000000000000000000 : ℝ)*base73 + (146295945371346089/86137500000000000000000000000000 : ℝ)*base75 + (225935634375058589/86137500000000000000000000000000 : ℝ)*base77 + (454110192864691411/86137500000000000000000000000000 : ℝ)*base80 + (77763543907091/17227500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (3325029/1250000000000000000000 : ℝ)*base89 + (3325029/1250000000000000000000 : ℝ)*base91 + (3325029/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1374521855763635336881330181/114850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1142577677/50000000000000 : ℝ)*(base19) + (1010057587/50000000000000 : ℝ)*(base23) + (1536173/20000000000000 : ℝ)*(upper2) + (184518293/50000000000000 : ℝ)*(upper3) + (21143871/10000000000000 : ℝ)*(upper5) + (848589379215627/50000000000000 : ℝ)*(major0) + (848589379215627/50000000000000 : ℝ)*(major1) + (848589379215627/50000000000000 : ℝ)*(major2) + (1069108313/6250000000000 : ℝ)*(sp1) + (3950862621/25000000000000 : ℝ)*(sp2) + (480661663832127/20000000000000 : ℝ)*(sp4) + (150205558017017/6250000000000 : ℝ)*(sp5) + (1201645247797489/50000000000000 : ℝ)*(sp6) + (991048798769387/100000000000000 : ℝ)*(sp7) + (991048798769387/100000000000000 : ℝ)*(f.failure) + (480661663832127/20000000000000 : ℝ)*(f.sum) + (26005018513439/34455000000000000000000000000 : ℝ)*base65 + (1817433793992779819/689100000000000000000000000000000 : ℝ)*base68 + (161475671489579819/689100000000000000000000000000000 : ℝ)*base70 + (1749524241793020181/689100000000000000000000000000000 : ℝ)*base71 + (50472392401673/17227500000000000000000000000 : ℝ)*base74 + (3198030052432620181/689100000000000000000000000000000 : ℝ)*base75 + (4557819651625379819/689100000000000000000000000000000 : ℝ)*base78 + (8372565908225579819/689100000000000000000000000000000 : ℝ)*base80 + (64224103498567/17227500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (3900711/1250000000000000000000 : ℝ)*base90 + (3900711/1250000000000000000000 : ℝ)*base92 + (3900711/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1600_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21406347/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (979/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1901/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1789/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (449/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1600_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1600_s2_0 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1728046469/10000000000 : ℝ)*x 0 + (1367792973/2500000000 : ℝ)*x 1 + (5172294837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1728046469/10000000000 : ℝ)^4719 ≤ (2655817319761/25000000000000 : ℝ)^3695 := by
    have hnat : (1728046469 : ℕ)^4719*25000000000000^3695 ≤ 2655817319761^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1728046469 10000000000 2655817319761 25000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367792973/2500000000 : ℝ)^4719 ≤ (46290752422709/100000000000000 : ℝ)^3695 := by
    have hnat : (1367792973 : ℕ)^4719*100000000000000^3695 ≤ 46290752422709^3695*2500000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367792973 2500000000 46290752422709 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5172294837/10000000000 : ℝ)^4719 ≤ (4308597828251/10000000000000 : ℝ)^3695 := by
    have hnat : (5172294837 : ℕ)^4719*10000000000000^3695 ≤ 4308597828251^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172294837 10000000000 4308597828251 10000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1728046469/10000000000 : ℝ), (1367792973/2500000000 : ℝ), (5172294837/10000000000 : ℝ)] ![(2655817319761/25000000000000 : ℝ), (46290752422709/100000000000000 : ℝ), (4308597828251/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1728046469/10000000000 : ℝ)|^4719 ≤ (2655817319761/25000000000000 : ℝ)^3695
        have hw : |(-1728046469/10000000000 : ℝ)|=(1728046469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1367792973/2500000000 : ℝ)|^4719 ≤ (46290752422709/100000000000000 : ℝ)^3695
        have hw : |(1367792973/2500000000 : ℝ)|=(1367792973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5172294837/10000000000 : ℝ)|^4719 ≤ (4308597828251/10000000000000 : ℝ)^3695
        have hw : |(5172294837/10000000000 : ℝ)|=(5172294837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s2_1 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071450969/2000000000 : ℝ)*x 0 + (-58828189/312500000 : ℝ)*x 1 + (2586147353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071450969/2000000000 : ℝ)^4719 ≤ (45063378281577/100000000000000 : ℝ)^3695 := by
    have hnat : (1071450969 : ℕ)^4719*100000000000000^3695 ≤ 45063378281577^3695*2000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071450969 2000000000 45063378281577 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (58828189/312500000 : ℝ)^4719 ≤ (11850644820231/100000000000000 : ℝ)^3695 := by
    have hnat : (58828189 : ℕ)^4719*100000000000000^3695 ≤ 11850644820231^3695*312500000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58828189 312500000 11850644820231 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2586147353/5000000000 : ℝ)^4719 ≤ (43085976888841/100000000000000 : ℝ)^3695 := by
    have hnat : (2586147353 : ℕ)^4719*100000000000000^3695 ≤ 43085976888841^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586147353 5000000000 43085976888841 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071450969/2000000000 : ℝ), (-58828189/312500000 : ℝ), (2586147353/5000000000 : ℝ)] ![(45063378281577/100000000000000 : ℝ), (11850644820231/100000000000000 : ℝ), (43085976888841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071450969/2000000000 : ℝ)|^4719 ≤ (45063378281577/100000000000000 : ℝ)^3695
        have hw : |(1071450969/2000000000 : ℝ)|=(1071450969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-58828189/312500000 : ℝ)|^4719 ≤ (11850644820231/100000000000000 : ℝ)^3695
        have hw : |(-58828189/312500000 : ℝ)|=(58828189/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2586147353/5000000000 : ℝ)|^4719 ≤ (43085976888841/100000000000000 : ℝ)^3695
        have hw : |(2586147353/5000000000 : ℝ)|=(2586147353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s2_2 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669656813/1250000000 : ℝ)*x 0 + (2586147551/5000000000 : ℝ)*x 1 + (-1882501979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669656813/1250000000 : ℝ)^4719 ≤ (22531687309143/50000000000000 : ℝ)^3695 := by
    have hnat : (669656813 : ℕ)^4719*50000000000000^3695 ≤ 22531687309143^3695*1250000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669656813 1250000000 22531687309143 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2586147551/5000000000 : ℝ)^4719 ≤ (43085981101763/100000000000000 : ℝ)^3695 := by
    have hnat : (2586147551 : ℕ)^4719*100000000000000^3695 ≤ 43085981101763^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586147551 5000000000 43085981101763 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1882501979/10000000000 : ℝ)^4719 ≤ (740665266593/6250000000000 : ℝ)^3695 := by
    have hnat : (1882501979 : ℕ)^4719*6250000000000^3695 ≤ 740665266593^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882501979 10000000000 740665266593 6250000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669656813/1250000000 : ℝ), (2586147551/5000000000 : ℝ), (-1882501979/10000000000 : ℝ)] ![(22531687309143/50000000000000 : ℝ), (43085981101763/100000000000000 : ℝ), (740665266593/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669656813/1250000000 : ℝ)|^4719 ≤ (22531687309143/50000000000000 : ℝ)^3695
        have hw : |(669656813/1250000000 : ℝ)|=(669656813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2586147551/5000000000 : ℝ)|^4719 ≤ (43085981101763/100000000000000 : ℝ)^3695
        have hw : |(2586147551/5000000000 : ℝ)|=(2586147551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1882501979/10000000000 : ℝ)|^4719 ≤ (740665266593/6250000000000 : ℝ)^3695
        have hw : |(-1882501979/10000000000 : ℝ)|=(1882501979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s2_3 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4219714129/10000000000 : ℝ)*x 0 + (3869489211/10000000000 : ℝ)*x 1 + (574283833/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4219714129/10000000000 : ℝ)^4719 ≤ (16611438738349/50000000000000 : ℝ)^3695 := by
    have hnat : (4219714129 : ℕ)^4719*50000000000000^3695 ≤ 16611438738349^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219714129 10000000000 16611438738349 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3869489211/10000000000 : ℝ)^4719 ≤ (3717830513103/12500000000000 : ℝ)^3695 := by
    have hnat : (3869489211 : ℕ)^4719*12500000000000^3695 ≤ 3717830513103^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3869489211 10000000000 3717830513103 12500000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (574283833/1250000000 : ℝ)^4719 ≤ (9258619600319/25000000000000 : ℝ)^3695 := by
    have hnat : (574283833 : ℕ)^4719*25000000000000^3695 ≤ 9258619600319^3695*1250000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574283833 1250000000 9258619600319 25000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4219714129/10000000000 : ℝ), (3869489211/10000000000 : ℝ), (574283833/1250000000 : ℝ)] ![(16611438738349/50000000000000 : ℝ), (3717830513103/12500000000000 : ℝ), (9258619600319/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4219714129/10000000000 : ℝ)|^4719 ≤ (16611438738349/50000000000000 : ℝ)^3695
        have hw : |(4219714129/10000000000 : ℝ)|=(4219714129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3869489211/10000000000 : ℝ)|^4719 ≤ (3717830513103/12500000000000 : ℝ)^3695
        have hw : |(3869489211/10000000000 : ℝ)|=(3869489211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(574283833/1250000000 : ℝ)|^4719 ≤ (9258619600319/25000000000000 : ℝ)^3695
        have hw : |(574283833/1250000000 : ℝ)|=(574283833/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s2_4 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-864065749/5000000000 : ℝ)*x 0 + (5174631073/10000000000 : ℝ)*x 1 + (2734404839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864065749/5000000000 : ℝ)^4719 ≤ (2124787373353/20000000000000 : ℝ)^3695 := by
    have hnat : (864065749 : ℕ)^4719*20000000000000^3695 ≤ 2124787373353^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864065749 5000000000 2124787373353 20000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5174631073/10000000000 : ℝ)^4719 ≤ (43110834332249/100000000000000 : ℝ)^3695 := by
    have hnat : (5174631073 : ℕ)^4719*100000000000000^3695 ≤ 43110834332249^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174631073 10000000000 43110834332249 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2734404839/5000000000 : ℝ)^4719 ≤ (46265228779311/100000000000000 : ℝ)^3695 := by
    have hnat : (2734404839 : ℕ)^4719*100000000000000^3695 ≤ 46265228779311^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734404839 5000000000 46265228779311 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-864065749/5000000000 : ℝ), (5174631073/10000000000 : ℝ), (2734404839/5000000000 : ℝ)] ![(2124787373353/20000000000000 : ℝ), (43110834332249/100000000000000 : ℝ), (46265228779311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-864065749/5000000000 : ℝ)|^4719 ≤ (2124787373353/20000000000000 : ℝ)^3695
        have hw : |(-864065749/5000000000 : ℝ)|=(864065749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5174631073/10000000000 : ℝ)|^4719 ≤ (43110834332249/100000000000000 : ℝ)^3695
        have hw : |(5174631073/10000000000 : ℝ)|=(5174631073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2734404839/5000000000 : ℝ)|^4719 ≤ (46265228779311/100000000000000 : ℝ)^3695
        have hw : |(2734404839/5000000000 : ℝ)|=(2734404839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s2_5 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278015759/10000000000 : ℝ)*x 0 + (-198248381/1250000000 : ℝ)*x 1 + (2734404747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278015759/10000000000 : ℝ)^4719 ≤ (22106940275113/50000000000000 : ℝ)^3695 := by
    have hnat : (5278015759 : ℕ)^4719*50000000000000^3695 ≤ 22106940275113^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278015759 10000000000 22106940275113 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (198248381/1250000000 : ℝ)^4719 ≤ (4760446321917/50000000000000 : ℝ)^3695 := by
    have hnat : (198248381 : ℕ)^4719*50000000000000^3695 ≤ 4760446321917^3695*1250000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198248381 1250000000 4760446321917 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2734404747/5000000000 : ℝ)^4719 ≤ (11566306697829/25000000000000 : ℝ)^3695 := by
    have hnat : (2734404747 : ℕ)^4719*25000000000000^3695 ≤ 11566306697829^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734404747 5000000000 11566306697829 25000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278015759/10000000000 : ℝ), (-198248381/1250000000 : ℝ), (2734404747/5000000000 : ℝ)] ![(22106940275113/50000000000000 : ℝ), (4760446321917/50000000000000 : ℝ), (11566306697829/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278015759/10000000000 : ℝ)|^4719 ≤ (22106940275113/50000000000000 : ℝ)^3695
        have hw : |(5278015759/10000000000 : ℝ)|=(5278015759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-198248381/1250000000 : ℝ)|^4719 ≤ (4760446321917/50000000000000 : ℝ)^3695
        have hw : |(-198248381/1250000000 : ℝ)|=(198248381/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2734404747/5000000000 : ℝ)|^4719 ≤ (11566306697829/25000000000000 : ℝ)^3695
        have hw : |(2734404747/5000000000 : ℝ)|=(2734404747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s2_6 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278015743/10000000000 : ℝ)*x 0 + (5468809581/10000000000 : ℝ)*x 1 + (-396496737/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278015743/10000000000 : ℝ)^4719 ≤ (884277607581/2000000000000 : ℝ)^3695 := by
    have hnat : (5278015743 : ℕ)^4719*2000000000000^3695 ≤ 884277607581^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278015743 10000000000 884277607581 2000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5468809581/10000000000 : ℝ)^4719 ≤ (11566306932823/25000000000000 : ℝ)^3695 := by
    have hnat : (5468809581 : ℕ)^4719*25000000000000^3695 ≤ 11566306932823^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468809581 10000000000 11566306932823 25000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (396496737/2500000000 : ℝ)^4719 ≤ (1904178375431/20000000000000 : ℝ)^3695 := by
    have hnat : (396496737 : ℕ)^4719*20000000000000^3695 ≤ 1904178375431^3695*2500000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396496737 2500000000 1904178375431 20000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278015743/10000000000 : ℝ), (5468809581/10000000000 : ℝ), (-396496737/2500000000 : ℝ)] ![(884277607581/2000000000000 : ℝ), (11566306932823/25000000000000 : ℝ), (1904178375431/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278015743/10000000000 : ℝ)|^4719 ≤ (884277607581/2000000000000 : ℝ)^3695
        have hw : |(5278015743/10000000000 : ℝ)|=(5278015743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5468809581/10000000000 : ℝ)|^4719 ≤ (11566306932823/25000000000000 : ℝ)^3695
        have hw : |(5468809581/10000000000 : ℝ)|=(5468809581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-396496737/2500000000 : ℝ)|^4719 ≤ (1904178375431/20000000000000 : ℝ)^3695
        have hw : |(-396496737/2500000000 : ℝ)|=(396496737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s2_7 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4219920187/10000000000 : ℝ)*x 0 + (2294302533/5000000000 : ℝ)*x 1 + (968804409/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4219920187/10000000000 : ℝ)^4719 ≤ (830623736013/2500000000000 : ℝ)^3695 := by
    have hnat : (4219920187 : ℕ)^4719*2500000000000^3695 ≤ 830623736013^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219920187 10000000000 830623736013 2500000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2294302533/5000000000 : ℝ)^4719 ≤ (36976161195599/100000000000000 : ℝ)^3695 := by
    have hnat : (2294302533 : ℕ)^4719*100000000000000^3695 ≤ 36976161195599^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2294302533 5000000000 36976161195599 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (968804409/2500000000 : ℝ)^4719 ≤ (3724861167677/12500000000000 : ℝ)^3695 := by
    have hnat : (968804409 : ℕ)^4719*12500000000000^3695 ≤ 3724861167677^3695*2500000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968804409 2500000000 3724861167677 12500000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4219920187/10000000000 : ℝ), (2294302533/5000000000 : ℝ), (968804409/2500000000 : ℝ)] ![(830623736013/2500000000000 : ℝ), (36976161195599/100000000000000 : ℝ), (3724861167677/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4219920187/10000000000 : ℝ)|^4719 ≤ (830623736013/2500000000000 : ℝ)^3695
        have hw : |(4219920187/10000000000 : ℝ)|=(4219920187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2294302533/5000000000 : ℝ)|^4719 ≤ (36976161195599/100000000000000 : ℝ)^3695
        have hw : |(2294302533/5000000000 : ℝ)|=(2294302533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(968804409/2500000000 : ℝ)|^4719 ≤ (3724861167677/12500000000000 : ℝ)^3695
        have hw : |(968804409/2500000000 : ℝ)|=(968804409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1600_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21406347/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (449/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1789/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5103/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8269/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (449/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1789/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (449/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1789/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (449/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1789/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (449/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1789/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (449/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1789/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (449/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1789/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1789/20000 : ℝ) ^ (4715/1024 : ℝ) ≤ (2905961979867/195312500000000000 : ℝ) := by
    have hpowers : (1789/20000 : ℝ)^4715 ≤ (2905961979867/195312500000000000 : ℝ)^1024 := by
      have hnat : (1789 : ℕ)^4715*195312500000000000^1024 ≤ 2905961979867^1024*20000^4715 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1789 20000 2905961979867 195312500000000000 4715 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1789/20000 : ℝ)) (X := (2905961979867/195312500000000000 : ℝ)) (by norm_num) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (449/2500 : ℝ) ^ (4715/1024 : ℝ) ≤ (36851853240449073/100000000000000000000 : ℝ) := by
    have hpowers : (449/2500 : ℝ)^4715 ≤ (36851853240449073/100000000000000000000 : ℝ)^1024 := by
      have hnat : (449 : ℕ)^4715*100000000000000000000^1024 ≤ 36851853240449073^1024*2500^4715 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        449 2500 36851853240449073 100000000000000000000 4715 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (449/2500 : ℝ)) (X := (36851853240449073/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (97659155961979867/97656250000000000 : ℝ) ≤ (250001615634411/250000000000000 : ℝ) ^ (4715/1024 : ℝ) := by
    have hpowers : (97659155961979867/97656250000000000 : ℝ)^1024 ≤ (250001615634411/250000000000000 : ℝ)^4715 := by
      have hnat : (97659155961979867 : ℕ)^1024*250000000000000^4715 ≤ 250001615634411^4715*97656250000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        97659155961979867 97656250000000000 250001615634411 250000000000000 1024 4715 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250001615634411/250000000000000 : ℝ)) (X := (97659155961979867/97656250000000000 : ℝ)) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038339705774140977/100000000000000000000 : ℝ) ≤ (10000832533796411/10000000000000000 : ℝ) ^ (4715/1024 : ℝ) := by
    have hpowers : (100038339705774140977/100000000000000000000 : ℝ)^1024 ≤ (10000832533796411/10000000000000000 : ℝ)^4715 := by
      have hnat : (100038339705774140977 : ℕ)^1024*10000000000000000^4715 ≤ 10000832533796411^4715*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038339705774140977 100000000000000000000 10000832533796411 10000000000000000 1024 4715 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000832533796411/10000000000000000 : ℝ)) (X := (100038339705774140977/100000000000000000000 : ℝ)) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036851853240449073/50000000000000000000 : ℝ) ≤ (5000800221108191/5000000000000000 : ℝ) ^ (4715/1024 : ℝ) := by
    have hpowers : (50036851853240449073/50000000000000000000 : ℝ)^1024 ≤ (5000800221108191/5000000000000000 : ℝ)^4715 := by
      have hnat : (50036851853240449073 : ℕ)^1024*5000000000000000^4715 ≤ 5000800221108191^4715*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036851853240449073 50000000000000000000 5000800221108191 5000000000000000 1024 4715 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000800221108191/5000000000000000 : ℝ)) (X := (50036851853240449073/50000000000000000000 : ℝ)) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2905961979867/195312500000000000 : ℝ) ≤ ((9013684471613532541/9015000000000000000 : ℝ)+2*(767908419971/901500000000000 : ℝ)*(1789/20000 : ℝ))^(4715/1024 : ℝ) := by
    rw [show (9013684471613532541/9015000000000000000 : ℝ)+2*(767908419971/901500000000000 : ℝ)*(1789/20000 : ℝ)=(250001615634411/250000000000000 : ℝ) by norm_num, show 1+2*(2905961979867/195312500000000000 : ℝ)=(97659155961979867/97656250000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36851853240449073/100000000000000000000 : ℝ)+(2905961979867/195312500000000000 : ℝ) ≤ ((9013684471613532541/9015000000000000000 : ℝ)+(767908419971/901500000000000 : ℝ)*((449/2500 : ℝ)+(1789/20000 : ℝ)))^(4715/1024 : ℝ) := by
    rw [show (9013684471613532541/9015000000000000000 : ℝ)+(767908419971/901500000000000 : ℝ)*((449/2500 : ℝ)+(1789/20000 : ℝ))=(10000832533796411/10000000000000000 : ℝ) by norm_num, show 1+(36851853240449073/100000000000000000000 : ℝ)+(2905961979867/195312500000000000 : ℝ)=(100038339705774140977/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36851853240449073/100000000000000000000 : ℝ) ≤ ((9013684471613532541/9015000000000000000 : ℝ)+2*(767908419971/901500000000000 : ℝ)*(449/2500 : ℝ))^(4715/1024 : ℝ) := by
    rw [show (9013684471613532541/9015000000000000000 : ℝ)+2*(767908419971/901500000000000 : ℝ)*(449/2500 : ℝ)=(5000800221108191/5000000000000000 : ℝ) by norm_num, show 1+2*(36851853240449073/100000000000000000000 : ℝ)=(50036851853240449073/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9013684471613532541/9015000000000000000 : ℝ)*(X 1 0+X 2 0)+(767908419971/901500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4715/1024 : ℝ)) (lo := (1789/20000 : ℝ)) (hi := (449/2500 : ℝ)) (c := (9013684471613532541/9015000000000000000 : ℝ)) (alpha := (767908419971/901500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9013684471613532541/9015000000000000000 : ℝ)*(X 0 1+X 2 1)+(767908419971/901500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4715/1024 : ℝ)) (lo := (1789/20000 : ℝ)) (hi := (449/2500 : ℝ)) (c := (9013684471613532541/9015000000000000000 : ℝ)) (alpha := (767908419971/901500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9013684471613532541/9015000000000000000 : ℝ)*(X 0 2+X 1 2)+(767908419971/901500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4715/1024 : ℝ)) (lo := (1789/20000 : ℝ)) (hi := (449/2500 : ℝ)) (c := (9013684471613532541/9015000000000000000 : ℝ)) (alpha := (767908419971/901500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1728046469/10000000000 : ℝ)*X 0 0+(1367792973/2500000000 : ℝ)*X 0 1+(5172294837/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1071450969/2000000000 : ℝ)*X 1 0+(-58828189/312500000 : ℝ)*X 1 1+(2586147353/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669656813/1250000000 : ℝ)*X 2 0+(2586147551/5000000000 : ℝ)*X 2 1+(-1882501979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4219714129/10000000000 : ℝ)*X 0 0+(3869489211/10000000000 : ℝ)*X 0 1+(574283833/1250000000 : ℝ)*X 0 2+(4219714129/10000000000 : ℝ)*X 1 0+(3869489211/10000000000 : ℝ)*X 1 1+(574283833/1250000000 : ℝ)*X 1 2+(4219714129/10000000000 : ℝ)*X 2 0+(3869489211/10000000000 : ℝ)*X 2 1+(574283833/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-864065749/5000000000 : ℝ)*X 0 0+(5174631073/10000000000 : ℝ)*X 0 1+(2734404839/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5278015759/10000000000 : ℝ)*X 1 0+(-198248381/1250000000 : ℝ)*X 1 1+(2734404747/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278015743/10000000000 : ℝ)*X 2 0+(5468809581/10000000000 : ℝ)*X 2 1+(-396496737/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4219920187/10000000000 : ℝ)*X 0 0+(2294302533/5000000000 : ℝ)*X 0 1+(968804409/2500000000 : ℝ)*X 0 2+(4219920187/10000000000 : ℝ)*X 1 0+(2294302533/5000000000 : ℝ)*X 1 1+(968804409/2500000000 : ℝ)*X 1 2+(4219920187/10000000000 : ℝ)*X 2 0+(2294302533/5000000000 : ℝ)*X 2 1+(968804409/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (418452455563514425967259659/75125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (344298207/50000000000000 : ℝ)*(base19) + (10825189/2500000000000 : ℝ)*(base23) + (1426959/6250000000000 : ℝ)*(lower2) + (2554783/2000000000000 : ℝ)*(upper3) + (55410123/50000000000000 : ℝ)*(upper5) + (1181400061795267/50000000000000 : ℝ)*(major0) + (1181400061795267/50000000000000 : ℝ)*(major1) + (1181400061795267/50000000000000 : ℝ)*(major2) + (3345863590000539/100000000000000 : ℝ)*(sp0) + (6534899075319/195312500000 : ℝ)*(sp1) + (1672934291076091/50000000000000 : ℝ)*(sp2) + (344932172048107/25000000000000 : ℝ)*(sp3) + (5425159203/100000000000000 : ℝ)*(sp4) + (2358159463/100000000000000 : ℝ)*(sp7) + (1379731046351891/100000000000000 : ℝ)*(f.failure) + (1672934507579871/50000000000000 : ℝ)*(f.sum) + (99818159549293/22537500000000000000000000000 : ℝ)*base66 + (2695078712750701149/150250000000000000000000000000000 : ℝ)*base67 + (1922432066409701149/150250000000000000000000000000000 : ℝ)*base69 + (2297273735630701149/150250000000000000000000000000000 : ℝ)*base71 + (25044264701341/11268750000000000000000000000 : ℝ)*base73 + (2848864883311951149/150250000000000000000000000000000 : ℝ)*base75 + (2311456799538701149/150250000000000000000000000000000 : ℝ)*base77 + (1715471557211451149/150250000000000000000000000000000 : ℝ)*base79 + (21576980886659/11268750000000000000000000000 : ℝ)*base82 + (12147823/1250000000000000000000 : ℝ)*base90 + (12147823/1250000000000000000000 : ℝ)*base92 + (12147823/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44833604970541745948079/7512500000000000000000000000 : ℝ) := by norm_num
    linear_combination (280088941/25000000000000 : ℝ)*(base19) + (566603613/50000000000000 : ℝ)*(base23) + (65302099/50000000000000 : ℝ)*(upper3) + (5539391/100000000000000 : ℝ)*(lower4) + (19512703/12500000000000 : ℝ)*(upper5) + (2400529417983991/100000000000000 : ℝ)*(major0) + (2400529417983991/100000000000000 : ℝ)*(major1) + (2400529417983991/100000000000000 : ℝ)*(major2) + (2121332959/20000000000000 : ℝ)*(sp1) + (11450045933/100000000000000 : ℝ)*(sp2) + (339929598576559/10000000000000 : ℝ)*(sp4) + (3399284258745031/100000000000000 : ℝ)*(sp5) + (3399283402512431/100000000000000 : ℝ)*(sp6) + (140176265127347/10000000000000 : ℝ)*(sp7) + (140176265127347/10000000000000 : ℝ)*(f.failure) + (339929598576559/10000000000000 : ℝ)*(f.sum) + (68522369345989/45075000000000000000000000000 : ℝ)*base66 + (755195063232279623/300500000000000000000000000000000 : ℝ)*base68 + (1442204128157279623/300500000000000000000000000000000 : ℝ)*base70 + (1377577512015720377/300500000000000000000000000000000 : ℝ)*base71 + (306025037083639/45075000000000000000000000000 : ℝ)*base74 + (457110907139279623/300500000000000000000000000000000 : ℝ)*base76 + (579236709635220377/300500000000000000000000000000000 : ℝ)*base77 + (1844988312914220377/300500000000000000000000000000000 : ℝ)*base79 + (95761060655057/22537500000000000000000000000 : ℝ)*base82 + (321409/125000000000000000000 : ℝ)*base89 + (321409/125000000000000000000 : ℝ)*base91 + (321409/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1600_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21406347/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (449/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1789/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5103/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8269/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1600_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1600_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21406347/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5103/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8269/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1600_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1600_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1600_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21406347/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5103/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8269/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1600_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
