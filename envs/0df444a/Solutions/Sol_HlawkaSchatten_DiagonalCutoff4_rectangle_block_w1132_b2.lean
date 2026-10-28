-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1132_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:27:00.506391+00:00
-- url     : https://prove2.me/submissions/bfcf33df-914d-4bb5-9455-2ae0e61c9687

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
theorem support_rectangle_w1132_s6_0 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-217164551/1000000000 : ℝ)*x 0 + (5393585409/10000000000 : ℝ)*x 1 + (1316306519/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217164551/1000000000 : ℝ)^8325 ≤ (659739861779/5000000000000 : ℝ)^6277 := by
    have hnat : (217164551 : ℕ)^8325*5000000000000^6277 ≤ 659739861779^6277*1000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217164551 1000000000 659739861779 5000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393585409/10000000000 : ℝ)^8325 ≤ (44095788696077/100000000000000 : ℝ)^6277 := by
    have hnat : (5393585409 : ℕ)^8325*100000000000000^6277 ≤ 44095788696077^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393585409 10000000000 44095788696077 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316306519/2500000000 : ℝ)^8325 ≤ (8541882811387/20000000000000 : ℝ)^6277 := by
    have hnat : (1316306519 : ℕ)^8325*20000000000000^6277 ≤ 8541882811387^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316306519 2500000000 8541882811387 20000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-217164551/1000000000 : ℝ), (5393585409/10000000000 : ℝ), (1316306519/2500000000 : ℝ)] ![(659739861779/5000000000000 : ℝ), (44095788696077/100000000000000 : ℝ), (8541882811387/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-217164551/1000000000 : ℝ)|^8325 ≤ (659739861779/5000000000000 : ℝ)^6277
        have hw : |(-217164551/1000000000 : ℝ)|=(217164551/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393585409/10000000000 : ℝ)|^8325 ≤ (44095788696077/100000000000000 : ℝ)^6277
        have hw : |(5393585409/10000000000 : ℝ)|=(5393585409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316306519/2500000000 : ℝ)|^8325 ≤ (8541882811387/20000000000000 : ℝ)^6277
        have hw : |(1316306519/2500000000 : ℝ)|=(1316306519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s6_1 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (167027721/312500000 : ℝ)*x 0 + (-1118379681/5000000000 : ℝ)*x 1 + (5265226073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167027721/312500000 : ℝ)^8325 ≤ (10892132322987/25000000000000 : ℝ)^6277 := by
    have hnat : (167027721 : ℕ)^8325*25000000000000^6277 ≤ 10892132322987^6277*312500000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167027721 312500000 10892132322987 25000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118379681/5000000000 : ℝ)^8325 ≤ (3430514165871/25000000000000 : ℝ)^6277 := by
    have hnat : (1118379681 : ℕ)^8325*25000000000000^6277 ≤ 3430514165871^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118379681 5000000000 3430514165871 25000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265226073/10000000000 : ℝ)^8325 ≤ (42709414024661/100000000000000 : ℝ)^6277 := by
    have hnat : (5265226073 : ℕ)^8325*100000000000000^6277 ≤ 42709414024661^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265226073 10000000000 42709414024661 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167027721/312500000 : ℝ), (-1118379681/5000000000 : ℝ), (5265226073/10000000000 : ℝ)] ![(10892132322987/25000000000000 : ℝ), (3430514165871/25000000000000 : ℝ), (42709414024661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167027721/312500000 : ℝ)|^8325 ≤ (10892132322987/25000000000000 : ℝ)^6277
        have hw : |(167027721/312500000 : ℝ)|=(167027721/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1118379681/5000000000 : ℝ)|^8325 ≤ (3430514165871/25000000000000 : ℝ)^6277
        have hw : |(-1118379681/5000000000 : ℝ)|=(1118379681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265226073/10000000000 : ℝ)|^8325 ≤ (42709414024661/100000000000000 : ℝ)^6277
        have hw : |(5265226073/10000000000 : ℝ)|=(5265226073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s6_2 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068977413/2000000000 : ℝ)*x 0 + (5265226083/10000000000 : ℝ)*x 1 + (-2236759359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068977413/2000000000 : ℝ)^8325 ≤ (43568529216271/100000000000000 : ℝ)^6277 := by
    have hnat : (1068977413 : ℕ)^8325*100000000000000^6277 ≤ 43568529216271^6277*2000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068977413 2000000000 43568529216271 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265226083/10000000000 : ℝ)^8325 ≤ (21354707066121/50000000000000 : ℝ)^6277 := by
    have hnat : (5265226083 : ℕ)^8325*50000000000000^6277 ≤ 21354707066121^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265226083 10000000000 21354707066121 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2236759359/10000000000 : ℝ)^8325 ≤ (6861028319537/50000000000000 : ℝ)^6277 := by
    have hnat : (2236759359 : ℕ)^8325*50000000000000^6277 ≤ 6861028319537^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236759359 10000000000 6861028319537 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068977413/2000000000 : ℝ), (5265226083/10000000000 : ℝ), (-2236759359/10000000000 : ℝ)] ![(43568529216271/100000000000000 : ℝ), (21354707066121/50000000000000 : ℝ), (6861028319537/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068977413/2000000000 : ℝ)|^8325 ≤ (43568529216271/100000000000000 : ℝ)^6277
        have hw : |(1068977413/2000000000 : ℝ)|=(1068977413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265226083/10000000000 : ℝ)|^8325 ≤ (21354707066121/50000000000000 : ℝ)^6277
        have hw : |(5265226083/10000000000 : ℝ)|=(5265226083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2236759359/10000000000 : ℝ)|^8325 ≤ (6861028319537/50000000000000 : ℝ)^6277
        have hw : |(-2236759359/10000000000 : ℝ)|=(2236759359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s6_3 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2183032703/5000000000 : ℝ)*x 0 + (1060121731/2500000000 : ℝ)*x 1 + (140479803/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183032703/5000000000 : ℝ)^8325 ≤ (33316724306041/100000000000000 : ℝ)^6277 := by
    have hnat : (2183032703 : ℕ)^8325*100000000000000^6277 ≤ 33316724306041^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183032703 5000000000 33316724306041 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060121731/2500000000 : ℝ)^8325 ≤ (32051803201771/100000000000000 : ℝ)^6277 := by
    have hnat : (1060121731 : ℕ)^8325*100000000000000^6277 ≤ 32051803201771^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060121731 2500000000 32051803201771 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140479803/312500000 : ℝ)^8325 ≤ (8657868118669/25000000000000 : ℝ)^6277 := by
    have hnat : (140479803 : ℕ)^8325*25000000000000^6277 ≤ 8657868118669^6277*312500000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140479803 312500000 8657868118669 25000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183032703/5000000000 : ℝ), (1060121731/2500000000 : ℝ), (140479803/312500000 : ℝ)] ![(33316724306041/100000000000000 : ℝ), (32051803201771/100000000000000 : ℝ), (8657868118669/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183032703/5000000000 : ℝ)|^8325 ≤ (33316724306041/100000000000000 : ℝ)^6277
        have hw : |(2183032703/5000000000 : ℝ)|=(2183032703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060121731/2500000000 : ℝ)|^8325 ≤ (32051803201771/100000000000000 : ℝ)^6277
        have hw : |(1060121731/2500000000 : ℝ)|=(1060121731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140479803/312500000 : ℝ)|^8325 ≤ (8657868118669/25000000000000 : ℝ)^6277
        have hw : |(140479803/312500000 : ℝ)|=(140479803/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s6_4 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2171650563/10000000000 : ℝ)*x 0 + (5265550197/10000000000 : ℝ)*x 1 + (5393260063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171650563/10000000000 : ℝ)^8325 ≤ (13194837954417/100000000000000 : ℝ)^6277 := by
    have hnat : (2171650563 : ℕ)^8325*100000000000000^6277 ≤ 13194837954417^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171650563 10000000000 13194837954417 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265550197/10000000000 : ℝ)^8325 ≤ (2669556315199/6250000000000 : ℝ)^6277 := by
    have hnat : (5265550197 : ℕ)^8325*6250000000000^6277 ≤ 2669556315199^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265550197 10000000000 2669556315199 6250000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393260063/10000000000 : ℝ)^8325 ≤ (44092260986161/100000000000000 : ℝ)^6277 := by
    have hnat : (5393260063 : ℕ)^8325*100000000000000^6277 ≤ 44092260986161^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393260063 10000000000 44092260986161 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2171650563/10000000000 : ℝ), (5265550197/10000000000 : ℝ), (5393260063/10000000000 : ℝ)] ![(13194837954417/100000000000000 : ℝ), (2669556315199/6250000000000 : ℝ), (44092260986161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2171650563/10000000000 : ℝ)|^8325 ≤ (13194837954417/100000000000000 : ℝ)^6277
        have hw : |(-2171650563/10000000000 : ℝ)|=(2171650563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265550197/10000000000 : ℝ)|^8325 ≤ (2669556315199/6250000000000 : ℝ)^6277
        have hw : |(5265550197/10000000000 : ℝ)|=(5265550197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393260063/10000000000 : ℝ)|^8325 ≤ (44092260986161/100000000000000 : ℝ)^6277
        have hw : |(5393260063/10000000000 : ℝ)|=(5393260063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s6_5 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312390903/10000000000 : ℝ)*x 0 + (-105436269/500000000 : ℝ)*x 1 + (5393260059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312390903/10000000000 : ℝ)^8325 ≤ (43217561640139/100000000000000 : ℝ)^6277 := by
    have hnat : (5312390903 : ℕ)^8325*100000000000000^6277 ≤ 43217561640139^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312390903 10000000000 43217561640139 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105436269/500000000 : ℝ)^8325 ≤ (1269017739223/10000000000000 : ℝ)^6277 := by
    have hnat : (105436269 : ℕ)^8325*10000000000000^6277 ≤ 1269017739223^6277*500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105436269 500000000 1269017739223 10000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393260059/10000000000 : ℝ)^8325 ≤ (44092260942789/100000000000000 : ℝ)^6277 := by
    have hnat : (5393260059 : ℕ)^8325*100000000000000^6277 ≤ 44092260942789^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393260059 10000000000 44092260942789 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312390903/10000000000 : ℝ), (-105436269/500000000 : ℝ), (5393260059/10000000000 : ℝ)] ![(43217561640139/100000000000000 : ℝ), (1269017739223/10000000000000 : ℝ), (44092260942789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312390903/10000000000 : ℝ)|^8325 ≤ (43217561640139/100000000000000 : ℝ)^6277
        have hw : |(5312390903/10000000000 : ℝ)|=(5312390903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-105436269/500000000 : ℝ)|^8325 ≤ (1269017739223/10000000000000 : ℝ)^6277
        have hw : |(-105436269/500000000 : ℝ)|=(105436269/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393260059/10000000000 : ℝ)|^8325 ≤ (44092260942789/100000000000000 : ℝ)^6277
        have hw : |(5393260059/10000000000 : ℝ)|=(5393260059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s6_6 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531239099/1000000000 : ℝ)*x 0 + (5393259879/10000000000 : ℝ)*x 1 + (-2108725507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531239099/1000000000 : ℝ)^8325 ≤ (43217562578827/100000000000000 : ℝ)^6277 := by
    have hnat : (531239099 : ℕ)^8325*100000000000000^6277 ≤ 43217562578827^6277*1000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531239099 1000000000 43217562578827 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393259879/10000000000 : ℝ)^8325 ≤ (22046129495539/50000000000000 : ℝ)^6277 := by
    have hnat : (5393259879 : ℕ)^8325*50000000000000^6277 ≤ 22046129495539^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393259879 10000000000 22046129495539 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2108725507/10000000000 : ℝ)^8325 ≤ (12690178405869/100000000000000 : ℝ)^6277 := by
    have hnat : (2108725507 : ℕ)^8325*100000000000000^6277 ≤ 12690178405869^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108725507 10000000000 12690178405869 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531239099/1000000000 : ℝ), (5393259879/10000000000 : ℝ), (-2108725507/10000000000 : ℝ)] ![(43217562578827/100000000000000 : ℝ), (22046129495539/50000000000000 : ℝ), (12690178405869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531239099/1000000000 : ℝ)|^8325 ≤ (43217562578827/100000000000000 : ℝ)^6277
        have hw : |(531239099/1000000000 : ℝ)|=(531239099/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393259879/10000000000 : ℝ)|^8325 ≤ (22046129495539/50000000000000 : ℝ)^6277
        have hw : |(5393259879/10000000000 : ℝ)|=(5393259879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2108725507/10000000000 : ℝ)|^8325 ≤ (12690178405869/100000000000000 : ℝ)^6277
        have hw : |(-2108725507/10000000000 : ℝ)|=(2108725507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s6_7 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2183037653/5000000000 : ℝ)*x 0 + (4494710013/10000000000 : ℝ)*x 1 + (1060283239/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183037653/5000000000 : ℝ)^8325 ≤ (2082301531221/6250000000000 : ℝ)^6277 := by
    have hnat : (2183037653 : ℕ)^8325*6250000000000^6277 ≤ 2082301531221^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183037653 5000000000 2082301531221 6250000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4494710013/10000000000 : ℝ)^8325 ≤ (17312447939843/50000000000000 : ℝ)^6277 := by
    have hnat : (4494710013 : ℕ)^8325*50000000000000^6277 ≤ 17312447939843^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494710013 10000000000 17312447939843 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060283239/2500000000 : ℝ)^8325 ≤ (32058279601953/100000000000000 : ℝ)^6277 := by
    have hnat : (1060283239 : ℕ)^8325*100000000000000^6277 ≤ 32058279601953^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060283239 2500000000 32058279601953 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183037653/5000000000 : ℝ), (4494710013/10000000000 : ℝ), (1060283239/2500000000 : ℝ)] ![(2082301531221/6250000000000 : ℝ), (17312447939843/50000000000000 : ℝ), (32058279601953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183037653/5000000000 : ℝ)|^8325 ≤ (2082301531221/6250000000000 : ℝ)^6277
        have hw : |(2183037653/5000000000 : ℝ)|=(2183037653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4494710013/10000000000 : ℝ)|^8325 ≤ (17312447939843/50000000000000 : ℝ)^6277
        have hw : |(4494710013/10000000000 : ℝ)|=(4494710013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1060283239/2500000000 : ℝ)|^8325 ≤ (32058279601953/100000000000000 : ℝ)^6277
        have hw : |(1060283239/2500000000 : ℝ)|=(1060283239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1132_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (113/1000 : ℝ)*pair X i i ≤ pair X i h) :
    (2833/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14051/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2817/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (113/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2817/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (113/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2817/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (113/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2817/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (113/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2817/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (113/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2817/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (113/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (113/1000 : ℝ) ^ (2081/512 : ℝ) ≤ (14167124826427899/100000000000000000000 : ℝ) := by
    have hpowers : (113/1000 : ℝ)^2081 ≤ (14167124826427899/100000000000000000000 : ℝ)^512 := by
      have hnat : (113 : ℕ)^2081*100000000000000000000^512 ≤ 14167124826427899^512*1000^2081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        113 1000 14167124826427899 100000000000000000000 2081 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (113/1000 : ℝ)) (X := (14167124826427899/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2817/20000 : ℝ) ^ (2081/512 : ℝ) ≤ (6937326263008059/20000000000000000000 : ℝ) := by
    have hpowers : (2817/20000 : ℝ)^2081 ≤ (6937326263008059/20000000000000000000 : ℝ)^512 := by
      have hnat : (2817 : ℕ)^2081*20000000000000000000^512 ≤ 6937326263008059^512*20000^2081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2817 20000 6937326263008059 20000000000000000000 2081 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2817/20000 : ℝ)) (X := (6937326263008059/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014167124826427899/50000000000000000000 : ℝ) ≤ (2500174262211653/2500000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (50014167124826427899/50000000000000000000 : ℝ)^512 ≤ (2500174262211653/2500000000000000 : ℝ)^2081 := by
      have hnat : (50014167124826427899 : ℕ)^512*2500000000000000^2081 ≤ 2500174262211653^2081*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014167124826427899 50000000000000000000 2500174262211653 2500000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500174262211653/2500000000000000 : ℝ)) (X := (50014167124826427899/50000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024426878070734097/50000000000000000000 : ℝ) ≤ (10001201754819487/10000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (50024426878070734097/50000000000000000000 : ℝ)^512 ≤ (10001201754819487/10000000000000000 : ℝ)^2081 := by
      have hnat : (50024426878070734097 : ℕ)^512*10000000000000000^2081 ≤ 10001201754819487^2081*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024426878070734097 50000000000000000000 10001201754819487 10000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001201754819487/10000000000000000 : ℝ)) (X := (50024426878070734097/50000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006937326263008059/10000000000000000000 : ℝ) ≤ (5000853230396181/5000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (10006937326263008059/10000000000000000000 : ℝ)^512 ≤ (5000853230396181/5000000000000000 : ℝ)^2081 := by
      have hnat : (10006937326263008059 : ℕ)^512*5000000000000000^2081 ≤ 5000853230396181^2081*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006937326263008059 10000000000000000000 5000853230396181 5000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000853230396181/5000000000000000 : ℝ)) (X := (10006937326263008059/10000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14167124826427899/100000000000000000000 : ℝ) ≤ ((1392026746302541971/1392500000000000000 : ℝ)+2*(4037647783/2228000000000 : ℝ)*(113/1000 : ℝ))^(2081/512 : ℝ) := by
    rw [show (1392026746302541971/1392500000000000000 : ℝ)+2*(4037647783/2228000000000 : ℝ)*(113/1000 : ℝ)=(2500174262211653/2500000000000000 : ℝ) by norm_num, show 1+2*(14167124826427899/100000000000000000000 : ℝ)=(50014167124826427899/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6937326263008059/20000000000000000000 : ℝ)+(14167124826427899/100000000000000000000 : ℝ) ≤ ((1392026746302541971/1392500000000000000 : ℝ)+(4037647783/2228000000000 : ℝ)*((2817/20000 : ℝ)+(113/1000 : ℝ)))^(2081/512 : ℝ) := by
    rw [show (1392026746302541971/1392500000000000000 : ℝ)+(4037647783/2228000000000 : ℝ)*((2817/20000 : ℝ)+(113/1000 : ℝ))=(10001201754819487/10000000000000000 : ℝ) by norm_num, show 1+(6937326263008059/20000000000000000000 : ℝ)+(14167124826427899/100000000000000000000 : ℝ)=(50024426878070734097/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6937326263008059/20000000000000000000 : ℝ) ≤ ((1392026746302541971/1392500000000000000 : ℝ)+2*(4037647783/2228000000000 : ℝ)*(2817/20000 : ℝ))^(2081/512 : ℝ) := by
    rw [show (1392026746302541971/1392500000000000000 : ℝ)+2*(4037647783/2228000000000 : ℝ)*(2817/20000 : ℝ)=(5000853230396181/5000000000000000 : ℝ) by norm_num, show 1+2*(6937326263008059/20000000000000000000 : ℝ)=(10006937326263008059/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1392026746302541971/1392500000000000000 : ℝ)*(X 1 0+X 2 0)+(4037647783/2228000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (113/1000 : ℝ)) (hi := (2817/20000 : ℝ)) (c := (1392026746302541971/1392500000000000000 : ℝ)) (alpha := (4037647783/2228000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1392026746302541971/1392500000000000000 : ℝ)*(X 0 1+X 2 1)+(4037647783/2228000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (113/1000 : ℝ)) (hi := (2817/20000 : ℝ)) (c := (1392026746302541971/1392500000000000000 : ℝ)) (alpha := (4037647783/2228000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1392026746302541971/1392500000000000000 : ℝ)*(X 0 2+X 1 2)+(4037647783/2228000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (113/1000 : ℝ)) (hi := (2817/20000 : ℝ)) (c := (1392026746302541971/1392500000000000000 : ℝ)) (alpha := (4037647783/2228000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-217164551/1000000000 : ℝ)*X 0 0+(5393585409/10000000000 : ℝ)*X 0 1+(1316306519/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167027721/312500000 : ℝ)*X 1 0+(-1118379681/5000000000 : ℝ)*X 1 1+(5265226073/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068977413/2000000000 : ℝ)*X 2 0+(5265226083/10000000000 : ℝ)*X 2 1+(-2236759359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2183032703/5000000000 : ℝ)*X 0 0+(1060121731/2500000000 : ℝ)*X 0 1+(140479803/312500000 : ℝ)*X 0 2+(2183032703/5000000000 : ℝ)*X 1 0+(1060121731/2500000000 : ℝ)*X 1 1+(140479803/312500000 : ℝ)*X 1 2+(2183032703/5000000000 : ℝ)*X 2 0+(1060121731/2500000000 : ℝ)*X 2 1+(140479803/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2171650563/10000000000 : ℝ)*X 0 0+(5265550197/10000000000 : ℝ)*X 0 1+(5393260063/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312390903/10000000000 : ℝ)*X 1 0+(-105436269/500000000 : ℝ)*X 1 1+(5393260059/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531239099/1000000000 : ℝ)*X 2 0+(5393259879/10000000000 : ℝ)*X 2 1+(-2108725507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2183037653/5000000000 : ℝ)*X 0 0+(4494710013/10000000000 : ℝ)*X 0 1+(1060283239/2500000000 : ℝ)*X 0 2+(2183037653/5000000000 : ℝ)*X 1 0+(4494710013/10000000000 : ℝ)*X 1 1+(1060283239/2500000000 : ℝ)*X 1 2+(2183037653/5000000000 : ℝ)*X 2 0+(4494710013/10000000000 : ℝ)*X 2 1+(1060283239/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14371273668301070679/1392500000000000000000000 : ℝ) := by norm_num
    linear_combination (65602857/3125000000000 : ℝ)*(base19) + (967490089/50000000000000 : ℝ)*(base23) + (41184493/50000000000000 : ℝ)*(lower2) + (264169529/100000000000000 : ℝ)*(upper3) + (76730943/50000000000000 : ℝ)*(upper5) + (585721179202309/10000000000000 : ℝ)*(major0) + (585721179202309/10000000000000 : ℝ)*(major1) + (585721179202309/10000000000000 : ℝ)*(major2) + (3895344576129233/50000000000000 : ℝ)*(sp0) + (1947685967678731/25000000000000 : ℝ)*(sp1) + (7790744035026171/100000000000000 : ℝ)*(sp2) + (980911586511981/25000000000000 : ℝ)*(sp3) + (56817747883/100000000000000 : ℝ)*(sp4) + (3092397577/10000000000000 : ℝ)*(sp7) + (784735454004739/20000000000000 : ℝ)*(f.failure) + (1947686492501587/25000000000000 : ℝ)*(f.sum) + (108529200491/22280000000000000000000000 : ℝ)*base65 + (237059286794688961/13925000000000000000000000000000 : ℝ)*base68 + (101389723706338961/13925000000000000000000000000000 : ℝ)*base70 + (50553113826613961/13925000000000000000000000000000 : ℝ)*base72 + (1218436624341/139250000000000000000000000 : ℝ)*base73 + (281083274401186039/13925000000000000000000000000000 : ℝ)*base75 + (66008666624411039/13925000000000000000000000000000 : ℝ)*base77 + (26185699581911039/13925000000000000000000000000000 : ℝ)*base79 + (423630491251/111400000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (13441787/2000000000000000000000 : ℝ)*base89 + (13441787/2000000000000000000000 : ℝ)*base91 + (13441787/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (48605494225635250957401951/17406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (143814467/20000000000000 : ℝ)*(base19) + (168681807/20000000000000 : ℝ)*(base23) + (1228839/5000000000000 : ℝ)*(upper2) + (50835419/100000000000000 : ℝ)*(upper3) + (27149679/25000000000000 : ℝ)*(upper5) + (2943456240796623/50000000000000 : ℝ)*(major0) + (2943456240796623/50000000000000 : ℝ)*(major1) + (2943456240796623/50000000000000 : ℝ)*(major2) + (4331512493/20000000000000 : ℝ)*(sp1) + (3364355207/25000000000000 : ℝ)*(sp2) + (978781432195569/12500000000000 : ℝ)*(sp4) + (978778635116219/12500000000000 : ℝ)*(sp5) + (244694911147959/3125000000000 : ℝ)*(sp6) + (985893353135349/25000000000000 : ℝ)*(sp7) + (985893353135349/25000000000000 : ℝ)*(f.failure) + (978781432195569/12500000000000 : ℝ)*(f.sum) + (42106887729/55700000000000000000000000 : ℝ)*base65 + (246520667582688933/69625000000000000000000000000000 : ℝ)*base67 + (222888657305188933/69625000000000000000000000000000 : ℝ)*base69 + (157007229240188933/69625000000000000000000000000000 : ℝ)*base71 + (33498986587/17406250000000000000000000 : ℝ)*base73 + (164094624166563933/69625000000000000000000000000000 : ℝ)*base75 + (806423805611688933/69625000000000000000000000000000 : ℝ)*base77 + (241357215132811067/69625000000000000000000000000000 : ℝ)*base80 + (204043687567/278500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (12697917/2500000000000000000000 : ℝ)*base89 + (12697917/2500000000000000000000 : ℝ)*base91 + (12697917/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1132_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (113/1000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2833/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1132_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1132_s7_0 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2171676519/10000000000 : ℝ)*x 0 + (674155637/1250000000 : ℝ)*x 1 + (5265545839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171676519/10000000000 : ℝ)^8325 ≤ (13195047117407/100000000000000 : ℝ)^6277 := by
    have hnat : (2171676519 : ℕ)^8325*100000000000000^6277 ≤ 13195047117407^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171676519 10000000000 13195047117407 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674155637/1250000000 : ℝ)^8325 ≤ (44092098701421/100000000000000 : ℝ)^6277 := by
    have hnat : (674155637 : ℕ)^8325*100000000000000^6277 ≤ 44092098701421^6277*1250000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674155637 1250000000 44092098701421 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265545839/10000000000 : ℝ)^8325 ≤ (1334776692441/3125000000000 : ℝ)^6277 := by
    have hnat : (5265545839 : ℕ)^8325*3125000000000^6277 ≤ 1334776692441^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265545839 10000000000 1334776692441 3125000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2171676519/10000000000 : ℝ), (674155637/1250000000 : ℝ), (5265545839/10000000000 : ℝ)] ![(13195047117407/100000000000000 : ℝ), (44092098701421/100000000000000 : ℝ), (1334776692441/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2171676519/10000000000 : ℝ)|^8325 ≤ (13195047117407/100000000000000 : ℝ)^6277
        have hw : |(-2171676519/10000000000 : ℝ)|=(2171676519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674155637/1250000000 : ℝ)|^8325 ≤ (44092098701421/100000000000000 : ℝ)^6277
        have hw : |(674155637/1250000000 : ℝ)|=(674155637/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265545839/10000000000 : ℝ)|^8325 ≤ (1334776692441/3125000000000 : ℝ)^6277
        have hw : |(5265545839/10000000000 : ℝ)|=(5265545839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s7_1 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344801107/10000000000 : ℝ)*x 0 + (-1118225387/5000000000 : ℝ)*x 1 + (5265545837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344801107/10000000000 : ℝ)^8325 ≤ (43567599925461/100000000000000 : ℝ)^6277 := by
    have hnat : (5344801107 : ℕ)^8325*100000000000000^6277 ≤ 43567599925461^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344801107 10000000000 43567599925461 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118225387/5000000000 : ℝ)^8325 ≤ (13719545925939/100000000000000 : ℝ)^6277 := by
    have hnat : (1118225387 : ℕ)^8325*100000000000000^6277 ≤ 13719545925939^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118225387 5000000000 13719545925939 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265545837/10000000000 : ℝ)^8325 ≤ (8542570827319/20000000000000 : ℝ)^6277 := by
    have hnat : (5265545837 : ℕ)^8325*20000000000000^6277 ≤ 8542570827319^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265545837 10000000000 8542570827319 20000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344801107/10000000000 : ℝ), (-1118225387/5000000000 : ℝ), (5265545837/10000000000 : ℝ)] ![(43567599925461/100000000000000 : ℝ), (13719545925939/100000000000000 : ℝ), (8542570827319/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344801107/10000000000 : ℝ)|^8325 ≤ (43567599925461/100000000000000 : ℝ)^6277
        have hw : |(5344801107/10000000000 : ℝ)|=(5344801107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1118225387/5000000000 : ℝ)|^8325 ≤ (13719545925939/100000000000000 : ℝ)^6277
        have hw : |(-1118225387/5000000000 : ℝ)|=(1118225387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265545837/10000000000 : ℝ)|^8325 ≤ (8542570827319/20000000000000 : ℝ)^6277
        have hw : |(5265545837/10000000000 : ℝ)|=(5265545837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s7_2 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672400553/5000000000 : ℝ)*x 0 + (1316386459/2500000000 : ℝ)*x 1 + (-279556347/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672400553/5000000000 : ℝ)^8325 ≤ (871351998293/2000000000000 : ℝ)^6277 := by
    have hnat : (2672400553 : ℕ)^8325*2000000000000^6277 ≤ 871351998293^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672400553 5000000000 871351998293 2000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316386459/2500000000 : ℝ)^8325 ≤ (10678213531459/25000000000000 : ℝ)^6277 := by
    have hnat : (1316386459 : ℕ)^8325*25000000000000^6277 ≤ 10678213531459^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316386459 2500000000 10678213531459 25000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279556347/1250000000 : ℝ)^8325 ≤ (13719545942211/100000000000000 : ℝ)^6277 := by
    have hnat : (279556347 : ℕ)^8325*100000000000000^6277 ≤ 13719545942211^6277*1250000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279556347 1250000000 13719545942211 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672400553/5000000000 : ℝ), (1316386459/2500000000 : ℝ), (-279556347/1250000000 : ℝ)] ![(871351998293/2000000000000 : ℝ), (10678213531459/25000000000000 : ℝ), (13719545942211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672400553/5000000000 : ℝ)|^8325 ≤ (871351998293/2000000000000 : ℝ)^6277
        have hw : |(2672400553/5000000000 : ℝ)|=(2672400553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316386459/2500000000 : ℝ)|^8325 ≤ (10678213531459/25000000000000 : ℝ)^6277
        have hw : |(1316386459/2500000000 : ℝ)|=(1316386459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-279556347/1250000000 : ℝ)|^8325 ≤ (13719545942211/100000000000000 : ℝ)^6277
        have hw : |(-279556347/1250000000 : ℝ)|=(279556347/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s7_3 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4366082221/10000000000 : ℝ)*x 0 + (4241140041/10000000000 : ℝ)*x 1 + (1123674053/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366082221/10000000000 : ℝ)^8325 ≤ (16658447241609/50000000000000 : ℝ)^6277 := by
    have hnat : (4366082221 : ℕ)^8325*50000000000000^6277 ≤ 16658447241609^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366082221 10000000000 16658447241609 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4241140041/10000000000 : ℝ)^8325 ≤ (4007293828761/12500000000000 : ℝ)^6277 := by
    have hnat : (4241140041 : ℕ)^8325*12500000000000^6277 ≤ 4007293828761^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241140041 10000000000 4007293828761 12500000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123674053/2500000000 : ℝ)^8325 ≤ (17312377438197/50000000000000 : ℝ)^6277 := by
    have hnat : (1123674053 : ℕ)^8325*50000000000000^6277 ≤ 17312377438197^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123674053 2500000000 17312377438197 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366082221/10000000000 : ℝ), (4241140041/10000000000 : ℝ), (1123674053/2500000000 : ℝ)] ![(16658447241609/50000000000000 : ℝ), (4007293828761/12500000000000 : ℝ), (17312377438197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366082221/10000000000 : ℝ)|^8325 ≤ (16658447241609/50000000000000 : ℝ)^6277
        have hw : |(4366082221/10000000000 : ℝ)|=(4366082221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4241140041/10000000000 : ℝ)|^8325 ≤ (4007293828761/12500000000000 : ℝ)^6277
        have hw : |(4241140041/10000000000 : ℝ)|=(4241140041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1123674053/2500000000 : ℝ)|^8325 ≤ (17312377438197/50000000000000 : ℝ)^6277
        have hw : |(1123674053/2500000000 : ℝ)|=(1123674053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s7_4 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-542920357/2500000000 : ℝ)*x 0 + (526586671/1000000000 : ℝ)*x 1 + (539292307/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542920357/2500000000 : ℝ)^8325 ≤ (527803467041/4000000000000 : ℝ)^6277 := by
    have hnat : (542920357 : ℕ)^8325*4000000000000^6277 ≤ 527803467041^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542920357 2500000000 527803467041 4000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526586671/1000000000 : ℝ)^8325 ≤ (42716306247983/100000000000000 : ℝ)^6277 := by
    have hnat : (526586671 : ℕ)^8325*100000000000000^6277 ≤ 42716306247983^6277*1000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526586671 1000000000 42716306247983 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539292307/1000000000 : ℝ)^8325 ≤ (11022151765407/25000000000000 : ℝ)^6277 := by
    have hnat : (539292307 : ℕ)^8325*25000000000000^6277 ≤ 11022151765407^6277*1000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539292307 1000000000 11022151765407 25000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-542920357/2500000000 : ℝ), (526586671/1000000000 : ℝ), (539292307/1000000000 : ℝ)] ![(527803467041/4000000000000 : ℝ), (42716306247983/100000000000000 : ℝ), (11022151765407/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-542920357/2500000000 : ℝ)|^8325 ≤ (527803467041/4000000000000 : ℝ)^6277
        have hw : |(-542920357/2500000000 : ℝ)|=(542920357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526586671/1000000000 : ℝ)|^8325 ≤ (42716306247983/100000000000000 : ℝ)^6277
        have hw : |(526586671/1000000000 : ℝ)|=(526586671/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539292307/1000000000 : ℝ)|^8325 ≤ (11022151765407/25000000000000 : ℝ)^6277
        have hw : |(539292307/1000000000 : ℝ)|=(539292307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s7_5 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312471997/10000000000 : ℝ)*x 0 + (-421814711/2000000000 : ℝ)*x 1 + (2696461531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312471997/10000000000 : ℝ)^8325 ≤ (21609218304053/50000000000000 : ℝ)^6277 := by
    have hnat : (5312471997 : ℕ)^8325*50000000000000^6277 ≤ 21609218304053^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312471997 10000000000 21609218304053 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (421814711/2000000000 : ℝ)^8325 ≤ (12692956395533/100000000000000 : ℝ)^6277 := by
    have hnat : (421814711 : ℕ)^8325*100000000000000^6277 ≤ 12692956395533^6277*2000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421814711 2000000000 12692956395533 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696461531/5000000000 : ℝ)^8325 ≤ (44088606974887/100000000000000 : ℝ)^6277 := by
    have hnat : (2696461531 : ℕ)^8325*100000000000000^6277 ≤ 44088606974887^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696461531 5000000000 44088606974887 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312471997/10000000000 : ℝ), (-421814711/2000000000 : ℝ), (2696461531/5000000000 : ℝ)] ![(21609218304053/50000000000000 : ℝ), (12692956395533/100000000000000 : ℝ), (44088606974887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312471997/10000000000 : ℝ)|^8325 ≤ (21609218304053/50000000000000 : ℝ)^6277
        have hw : |(5312471997/10000000000 : ℝ)|=(5312471997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-421814711/2000000000 : ℝ)|^8325 ≤ (12692956395533/100000000000000 : ℝ)^6277
        have hw : |(-421814711/2000000000 : ℝ)|=(421814711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696461531/5000000000 : ℝ)|^8325 ≤ (44088606974887/100000000000000 : ℝ)^6277
        have hw : |(2696461531/5000000000 : ℝ)|=(2696461531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s7_6 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062494399/2000000000 : ℝ)*x 0 + (1348230767/2500000000 : ℝ)*x 1 + (-42181471/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062494399/2000000000 : ℝ)^8325 ≤ (21609218293263/50000000000000 : ℝ)^6277 := by
    have hnat : (1062494399 : ℕ)^8325*50000000000000^6277 ≤ 21609218293263^6277*2000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062494399 2000000000 21609218293263 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348230767/2500000000 : ℝ)^8325 ≤ (44088607039943/100000000000000 : ℝ)^6277 := by
    have hnat : (1348230767 : ℕ)^8325*100000000000000^6277 ≤ 44088607039943^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348230767 2500000000 44088607039943 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42181471/200000000 : ℝ)^8325 ≤ (1586619544453/12500000000000 : ℝ)^6277 := by
    have hnat : (42181471 : ℕ)^8325*12500000000000^6277 ≤ 1586619544453^6277*200000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42181471 200000000 1586619544453 12500000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062494399/2000000000 : ℝ), (1348230767/2500000000 : ℝ), (-42181471/200000000 : ℝ)] ![(21609218293263/50000000000000 : ℝ), (44088607039943/100000000000000 : ℝ), (1586619544453/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062494399/2000000000 : ℝ)|^8325 ≤ (21609218293263/50000000000000 : ℝ)^6277
        have hw : |(1062494399/2000000000 : ℝ)|=(1062494399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348230767/2500000000 : ℝ)|^8325 ≤ (44088607039943/100000000000000 : ℝ)^6277
        have hw : |(1348230767/2500000000 : ℝ)|=(1348230767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-42181471/200000000 : ℝ)|^8325 ≤ (1586619544453/12500000000000 : ℝ)^6277
        have hw : |(-42181471/200000000 : ℝ)|=(42181471/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s7_7 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4366091981/10000000000 : ℝ)*x 0 + (2247029541/5000000000 : ℝ)*x 1 + (4241779473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366091981/10000000000 : ℝ)^8325 ≤ (33316993259959/100000000000000 : ℝ)^6277 := by
    have hnat : (4366091981 : ℕ)^8325*100000000000000^6277 ≤ 33316993259959^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366091981 10000000000 33316993259959 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247029541/5000000000 : ℝ)^8325 ≤ (34618245543407/100000000000000 : ℝ)^6277 := by
    have hnat : (2247029541 : ℕ)^8325*100000000000000^6277 ≤ 34618245543407^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247029541 5000000000 34618245543407 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4241779473/10000000000 : ℝ)^8325 ≤ (32064761186451/100000000000000 : ℝ)^6277 := by
    have hnat : (4241779473 : ℕ)^8325*100000000000000^6277 ≤ 32064761186451^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241779473 10000000000 32064761186451 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366091981/10000000000 : ℝ), (2247029541/5000000000 : ℝ), (4241779473/10000000000 : ℝ)] ![(33316993259959/100000000000000 : ℝ), (34618245543407/100000000000000 : ℝ), (32064761186451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366091981/10000000000 : ℝ)|^8325 ≤ (33316993259959/100000000000000 : ℝ)^6277
        have hw : |(4366091981/10000000000 : ℝ)|=(4366091981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2247029541/5000000000 : ℝ)|^8325 ≤ (34618245543407/100000000000000 : ℝ)^6277
        have hw : |(2247029541/5000000000 : ℝ)|=(2247029541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4241779473/10000000000 : ℝ)|^8325 ≤ (32064761186451/100000000000000 : ℝ)^6277
        have hw : |(4241779473/10000000000 : ℝ)|=(4241779473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1132_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2833/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11339/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3511/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2833/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2833/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2833/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2833/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2833/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2833/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2833/25000 : ℝ) ^ (2081/512 : ℝ) ≤ (7165448362187079/50000000000000000000 : ℝ) := by
    have hpowers : (2833/25000 : ℝ)^2081 ≤ (7165448362187079/50000000000000000000 : ℝ)^512 := by
      have hnat : (2833 : ℕ)^2081*50000000000000000000^512 ≤ 7165448362187079^512*25000^2081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2833 25000 7165448362187079 50000000000000000000 2081 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2833/25000 : ℝ)) (X := (7165448362187079/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14051/100000 : ℝ) ^ (2081/512 : ℝ) ≤ (34347568863568401/100000000000000000000 : ℝ) := by
    have hpowers : (14051/100000 : ℝ)^2081 ≤ (34347568863568401/100000000000000000000 : ℝ)^512 := by
      have hnat : (14051 : ℕ)^2081*100000000000000000000^512 ≤ 34347568863568401^512*100000^2081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14051 100000 34347568863568401 100000000000000000000 2081 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14051/100000 : ℝ)) (X := (34347568863568401/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007165448362187079/25000000000000000000 : ℝ) ≤ (10000705105857623/10000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (25007165448362187079/25000000000000000000 : ℝ)^512 ≤ (10000705105857623/10000000000000000 : ℝ)^2081 := by
      have hnat : (25007165448362187079 : ℕ)^512*10000000000000000^2081 ≤ 10000705105857623^2081*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007165448362187079 25000000000000000000 10000705105857623 10000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000705105857623/10000000000000000 : ℝ)) (X := (25007165448362187079/25000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048678465587942559/100000000000000000000 : ℝ) ≤ (5000598721816789/5000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (100048678465587942559/100000000000000000000 : ℝ)^512 ≤ (5000598721816789/5000000000000000 : ℝ)^2081 := by
      have hnat : (100048678465587942559 : ℕ)^512*5000000000000000^2081 ≤ 5000598721816789^2081*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048678465587942559 100000000000000000000 5000598721816789 5000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000598721816789/5000000000000000 : ℝ)) (X := (100048678465587942559/100000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034347568863568401/50000000000000000000 : ℝ) ≤ (10001689781409533/10000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (50034347568863568401/50000000000000000000 : ℝ)^512 ≤ (10001689781409533/10000000000000000 : ℝ)^2081 := by
      have hnat : (50034347568863568401 : ℕ)^512*10000000000000000^2081 ≤ 10001689781409533^2081*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034347568863568401 50000000000000000000 10001689781409533 10000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001689781409533/10000000000000000 : ℝ)) (X := (50034347568863568401/50000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7165448362187079/50000000000000000000 : ℝ) ≤ ((27180758839472632817/27190000000000000000 : ℝ)+2*(98467555191/54380000000000 : ℝ)*(2833/25000 : ℝ))^(2081/512 : ℝ) := by
    rw [show (27180758839472632817/27190000000000000000 : ℝ)+2*(98467555191/54380000000000 : ℝ)*(2833/25000 : ℝ)=(10000705105857623/10000000000000000 : ℝ) by norm_num, show 1+2*(7165448362187079/50000000000000000000 : ℝ)=(25007165448362187079/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34347568863568401/100000000000000000000 : ℝ)+(7165448362187079/50000000000000000000 : ℝ) ≤ ((27180758839472632817/27190000000000000000 : ℝ)+(98467555191/54380000000000 : ℝ)*((14051/100000 : ℝ)+(2833/25000 : ℝ)))^(2081/512 : ℝ) := by
    rw [show (27180758839472632817/27190000000000000000 : ℝ)+(98467555191/54380000000000 : ℝ)*((14051/100000 : ℝ)+(2833/25000 : ℝ))=(5000598721816789/5000000000000000 : ℝ) by norm_num, show 1+(34347568863568401/100000000000000000000 : ℝ)+(7165448362187079/50000000000000000000 : ℝ)=(100048678465587942559/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34347568863568401/100000000000000000000 : ℝ) ≤ ((27180758839472632817/27190000000000000000 : ℝ)+2*(98467555191/54380000000000 : ℝ)*(14051/100000 : ℝ))^(2081/512 : ℝ) := by
    rw [show (27180758839472632817/27190000000000000000 : ℝ)+2*(98467555191/54380000000000 : ℝ)*(14051/100000 : ℝ)=(10001689781409533/10000000000000000 : ℝ) by norm_num, show 1+2*(34347568863568401/100000000000000000000 : ℝ)=(50034347568863568401/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27180758839472632817/27190000000000000000 : ℝ)*(X 1 0+X 2 0)+(98467555191/54380000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (2833/25000 : ℝ)) (hi := (14051/100000 : ℝ)) (c := (27180758839472632817/27190000000000000000 : ℝ)) (alpha := (98467555191/54380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27180758839472632817/27190000000000000000 : ℝ)*(X 0 1+X 2 1)+(98467555191/54380000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (2833/25000 : ℝ)) (hi := (14051/100000 : ℝ)) (c := (27180758839472632817/27190000000000000000 : ℝ)) (alpha := (98467555191/54380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27180758839472632817/27190000000000000000 : ℝ)*(X 0 2+X 1 2)+(98467555191/54380000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (2833/25000 : ℝ)) (hi := (14051/100000 : ℝ)) (c := (27180758839472632817/27190000000000000000 : ℝ)) (alpha := (98467555191/54380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2171676519/10000000000 : ℝ)*X 0 0+(674155637/1250000000 : ℝ)*X 0 1+(5265545839/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344801107/10000000000 : ℝ)*X 1 0+(-1118225387/5000000000 : ℝ)*X 1 1+(5265545837/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672400553/5000000000 : ℝ)*X 2 0+(1316386459/2500000000 : ℝ)*X 2 1+(-279556347/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4366082221/10000000000 : ℝ)*X 0 0+(4241140041/10000000000 : ℝ)*X 0 1+(1123674053/2500000000 : ℝ)*X 0 2+(4366082221/10000000000 : ℝ)*X 1 0+(4241140041/10000000000 : ℝ)*X 1 1+(1123674053/2500000000 : ℝ)*X 1 2+(4366082221/10000000000 : ℝ)*X 2 0+(4241140041/10000000000 : ℝ)*X 2 1+(1123674053/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-542920357/2500000000 : ℝ)*X 0 0+(526586671/1000000000 : ℝ)*X 0 1+(539292307/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312471997/10000000000 : ℝ)*X 1 0+(-421814711/2000000000 : ℝ)*X 1 1+(2696461531/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062494399/2000000000 : ℝ)*X 2 0+(1348230767/2500000000 : ℝ)*X 2 1+(-42181471/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4366091981/10000000000 : ℝ)*X 0 0+(2247029541/5000000000 : ℝ)*X 0 1+(4241779473/10000000000 : ℝ)*X 0 2+(4366091981/10000000000 : ℝ)*X 1 0+(2247029541/5000000000 : ℝ)*X 1 1+(4241779473/10000000000 : ℝ)*X 1 2+(4366091981/10000000000 : ℝ)*X 2 0+(2247029541/5000000000 : ℝ)*X 2 1+(4241779473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2370088365196131164570011143/271900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1724607053/100000000000000 : ℝ)*(base19) + (1599947231/100000000000000 : ℝ)*(base23) + (32922547/50000000000000 : ℝ)*(lower2) + (223173619/100000000000000 : ℝ)*(upper3) + (25603227/20000000000000 : ℝ)*(upper5) + (1177494263784707/20000000000000 : ℝ)*(major0) + (1177494263784707/20000000000000 : ℝ)*(major1) + (1177494263784707/20000000000000 : ℝ)*(major2) + (97886851479049/1250000000000 : ℝ)*(sp0) + (3915496425793441/50000000000000 : ℝ)*(sp1) + (489437061015419/6250000000000 : ℝ)*(sp2) + (3943922164799771/100000000000000 : ℝ)*(sp3) + (9291574003/20000000000000 : ℝ)*(sp4) + (1024251781/4000000000000 : ℝ)*(sp7) + (492993471386787/12500000000000 : ℝ)*(f.failure) + (1566198915238787/20000000000000 : ℝ)*(f.sum) + (12492640496181/2719000000000000000000000000 : ℝ)*base65 + (252778027631629619/543800000000000000000000000000000 : ℝ)*base67 + (2836962353102829619/543800000000000000000000000000000 : ℝ)*base69 + (10412593341167429619/543800000000000000000000000000000 : ℝ)*base71 + (2982635924609/1359500000000000000000000000 : ℝ)*base73 + (9014612293212370381/543800000000000000000000000000000 : ℝ)*base76 + (1359467383582570381/543800000000000000000000000000000 : ℝ)*base78 + (45738372890429619/543800000000000000000000000000000 : ℝ)*base79 + (18128145022049/1359500000000000000000000000 : ℝ)*base81 + (9877829/1250000000000000000000 : ℝ)*base90 + (9877829/1250000000000000000000 : ℝ)*base92 + (9877829/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6363540959951642054863808391/1359500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (817920609/100000000000000 : ℝ)*(base19) + (453142281/50000000000000 : ℝ)*(base23) + (43049351/50000000000000 : ℝ)*(upper3) + (8344787/20000000000000 : ℝ)*(lower4) + (12179567/12500000000000 : ℝ)*(upper5) + (5917188884444353/100000000000000 : ℝ)*(major0) + (5917188884444353/100000000000000 : ℝ)*(major1) + (5917188884444353/100000000000000 : ℝ)*(major2) + (22329517609/100000000000000 : ℝ)*(sp1) + (4886160663/20000000000000 : ℝ)*(sp2) + (7870522394249389/100000000000000 : ℝ)*(sp4) + (7870499246811171/100000000000000 : ℝ)*(sp5) + (983812132145189/12500000000000 : ℝ)*(sp6) + (1981927609306401/50000000000000 : ℝ)*(sp7) + (1981927609306401/50000000000000 : ℝ)*(f.failure) + (7870522394249389/100000000000000 : ℝ)*(f.sum) + (17677638585293/2719000000000000000000000000 : ℝ)*base65 + (21100344755323632401/2719000000000000000000000000000000 : ℝ)*base67 + (27418730793105632401/2719000000000000000000000000000000 : ℝ)*base69 + (35953413934021632401/2719000000000000000000000000000000 : ℝ)*base71 + (969194262739/679750000000000000000000000 : ℝ)*base73 + (62597791472610632401/2719000000000000000000000000000000 : ℝ)*base75 + (29621267575601632401/2719000000000000000000000000000000 : ℝ)*base77 + (7160398912769632401/2719000000000000000000000000000000 : ℝ)*base79 + (14355591477409/2719000000000000000000000000 : ℝ)*base81 + (30570167/5000000000000000000000 : ℝ)*base90 + (30570167/5000000000000000000000 : ℝ)*base92 + (30570167/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1132_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2833/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11339/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1132_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1132_s8_0 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-434336339/2000000000 : ℝ)*x 0 + (5393174453/10000000000 : ℝ)*x 1 + (5265613159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434336339/2000000000 : ℝ)^8325 ≤ (2639017765523/20000000000000 : ℝ)^6277 := by
    have hnat : (434336339 : ℕ)^8325*20000000000000^6277 ≤ 2639017765523^6277*2000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434336339 2000000000 2639017765523 20000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393174453/10000000000 : ℝ)^8325 ≤ (551141659161/1250000000000 : ℝ)^6277 := by
    have hnat : (5393174453 : ℕ)^8325*1250000000000^6277 ≤ 551141659161^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393174453 10000000000 551141659161 1250000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265613159/10000000000 : ℝ)^8325 ≤ (21356789207239/50000000000000 : ℝ)^6277 := by
    have hnat : (5265613159 : ℕ)^8325*50000000000000^6277 ≤ 21356789207239^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265613159 10000000000 21356789207239 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-434336339/2000000000 : ℝ), (5393174453/10000000000 : ℝ), (5265613159/10000000000 : ℝ)] ![(2639017765523/20000000000000 : ℝ), (551141659161/1250000000000 : ℝ), (21356789207239/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-434336339/2000000000 : ℝ)|^8325 ≤ (2639017765523/20000000000000 : ℝ)^6277
        have hw : |(-434336339/2000000000 : ℝ)|=(434336339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393174453/10000000000 : ℝ)|^8325 ≤ (551141659161/1250000000000 : ℝ)^6277
        have hw : |(5393174453/10000000000 : ℝ)|=(5393174453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265613159/10000000000 : ℝ)|^8325 ≤ (21356789207239/50000000000000 : ℝ)^6277
        have hw : |(5265613159/10000000000 : ℝ)|=(5265613159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s8_1 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344783653/10000000000 : ℝ)*x 0 + (-1118192411/5000000000 : ℝ)*x 1 + (1316403313/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344783653/10000000000 : ℝ)^8325 ≤ (10891852807773/25000000000000 : ℝ)^6277 := by
    have hnat : (5344783653 : ℕ)^8325*25000000000000^6277 ≤ 10891852807773^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344783653 10000000000 10891852807773 25000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118192411/5000000000 : ℝ)^8325 ≤ (13719009341111/100000000000000 : ℝ)^6277 := by
    have hnat : (1118192411 : ℕ)^8325*100000000000000^6277 ≤ 13719009341111^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118192411 5000000000 13719009341111 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316403313/2500000000 : ℝ)^8325 ≤ (42713579415013/100000000000000 : ℝ)^6277 := by
    have hnat : (1316403313 : ℕ)^8325*100000000000000^6277 ≤ 42713579415013^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316403313 2500000000 42713579415013 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344783653/10000000000 : ℝ), (-1118192411/5000000000 : ℝ), (1316403313/2500000000 : ℝ)] ![(10891852807773/25000000000000 : ℝ), (13719009341111/100000000000000 : ℝ), (42713579415013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344783653/10000000000 : ℝ)|^8325 ≤ (10891852807773/25000000000000 : ℝ)^6277
        have hw : |(5344783653/10000000000 : ℝ)|=(5344783653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1118192411/5000000000 : ℝ)|^8325 ≤ (13719009341111/100000000000000 : ℝ)^6277
        have hw : |(-1118192411/5000000000 : ℝ)|=(1118192411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316403313/2500000000 : ℝ)|^8325 ≤ (42713579415013/100000000000000 : ℝ)^6277
        have hw : |(1316403313/2500000000 : ℝ)|=(1316403313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s8_2 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534478361/1000000000 : ℝ)*x 0 + (5265613239/10000000000 : ℝ)*x 1 + (-17471757/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534478361/1000000000 : ℝ)^8325 ≤ (43567410766221/100000000000000 : ℝ)^6277 := by
    have hnat : (534478361 : ℕ)^8325*100000000000000^6277 ≤ 43567410766221^6277*1000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534478361 1000000000 43567410766221 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265613239/10000000000 : ℝ)^8325 ≤ (42713579275153/100000000000000 : ℝ)^6277 := by
    have hnat : (5265613239 : ℕ)^8325*100000000000000^6277 ≤ 42713579275153^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265613239 10000000000 42713579275153 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17471757/78125000 : ℝ)^8325 ≤ (13719009943171/100000000000000 : ℝ)^6277 := by
    have hnat : (17471757 : ℕ)^8325*100000000000000^6277 ≤ 13719009943171^6277*78125000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17471757 78125000 13719009943171 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534478361/1000000000 : ℝ), (5265613239/10000000000 : ℝ), (-17471757/78125000 : ℝ)] ![(43567410766221/100000000000000 : ℝ), (42713579275153/100000000000000 : ℝ), (13719009943171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534478361/1000000000 : ℝ)|^8325 ≤ (43567410766221/100000000000000 : ℝ)^6277
        have hw : |(534478361/1000000000 : ℝ)|=(534478361/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265613239/10000000000 : ℝ)|^8325 ≤ (42713579275153/100000000000000 : ℝ)^6277
        have hw : |(5265613239/10000000000 : ℝ)|=(5265613239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17471757/78125000 : ℝ)|^8325 ≤ (13719009943171/100000000000000 : ℝ)^6277
        have hw : |(-17471757/78125000 : ℝ)|=(17471757/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s8_3 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4366085641/10000000000 : ℝ)*x 0 + (1060319177/2500000000 : ℝ)*x 1 + (1755687/3906250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366085641/10000000000 : ℝ)^8325 ≤ (260288508559/781250000000 : ℝ)^6277 := by
    have hnat : (4366085641 : ℕ)^8325*781250000000^6277 ≤ 260288508559^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366085641 10000000000 260288508559 781250000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060319177/2500000000 : ℝ)^8325 ≤ (16029860371911/50000000000000 : ℝ)^6277 := by
    have hnat : (1060319177 : ℕ)^8325*50000000000000^6277 ≤ 16029860371911^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060319177 2500000000 16029860371911 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1755687/3906250 : ℝ)^8325 ≤ (17311675071771/50000000000000 : ℝ)^6277 := by
    have hnat : (1755687 : ℕ)^8325*50000000000000^6277 ≤ 17311675071771^6277*3906250^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1755687 3906250 17311675071771 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366085641/10000000000 : ℝ), (1060319177/2500000000 : ℝ), (1755687/3906250 : ℝ)] ![(260288508559/781250000000 : ℝ), (16029860371911/50000000000000 : ℝ), (17311675071771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366085641/10000000000 : ℝ)|^8325 ≤ (260288508559/781250000000 : ℝ)^6277
        have hw : |(4366085641/10000000000 : ℝ)|=(4366085641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060319177/2500000000 : ℝ)|^8325 ≤ (16029860371911/50000000000000 : ℝ)^6277
        have hw : |(1060319177/2500000000 : ℝ)|=(1060319177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1755687/3906250 : ℝ)|^8325 ≤ (17311675071771/50000000000000 : ℝ)^6277
        have hw : |(1755687/3906250 : ℝ)|=(1755687/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s8_4 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2171686273/10000000000 : ℝ)*x 0 + (5265933647/10000000000 : ℝ)*x 1 + (107857061/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171686273/10000000000 : ℝ)^8325 ≤ (1649390714867/12500000000000 : ℝ)^6277 := by
    have hnat : (2171686273 : ℕ)^8325*12500000000000^6277 ≤ 1649390714867^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171686273 10000000000 1649390714867 12500000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265933647/10000000000 : ℝ)^8325 ≤ (21358513199093/50000000000000 : ℝ)^6277 := by
    have hnat : (5265933647 : ℕ)^8325*50000000000000^6277 ≤ 21358513199093^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265933647 10000000000 21358513199093 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107857061/200000000 : ℝ)^8325 ≤ (44087847862933/100000000000000 : ℝ)^6277 := by
    have hnat : (107857061 : ℕ)^8325*100000000000000^6277 ≤ 44087847862933^6277*200000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107857061 200000000 44087847862933 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2171686273/10000000000 : ℝ), (5265933647/10000000000 : ℝ), (107857061/200000000 : ℝ)] ![(1649390714867/12500000000000 : ℝ), (21358513199093/50000000000000 : ℝ), (44087847862933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2171686273/10000000000 : ℝ)|^8325 ≤ (1649390714867/12500000000000 : ℝ)^6277
        have hw : |(-2171686273/10000000000 : ℝ)|=(2171686273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265933647/10000000000 : ℝ)|^8325 ≤ (21358513199093/50000000000000 : ℝ)^6277
        have hw : |(5265933647/10000000000 : ℝ)|=(5265933647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107857061/200000000 : ℝ)|^8325 ≤ (44087847862933/100000000000000 : ℝ)^6277
        have hw : |(107857061/200000000 : ℝ)|=(107857061/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s8_5 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312489561/10000000000 : ℝ)*x 0 + (-2109144789/10000000000 : ℝ)*x 1 + (1078570629/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312489561/10000000000 : ℝ)^8325 ≤ (43218626116379/100000000000000 : ℝ)^6277 := by
    have hnat : (5312489561 : ℕ)^8325*100000000000000^6277 ≤ 43218626116379^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312489561 10000000000 43218626116379 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2109144789/10000000000 : ℝ)^8325 ≤ (12693524977263/100000000000000 : ℝ)^6277 := by
    have hnat : (2109144789 : ℕ)^8325*100000000000000^6277 ≤ 12693524977263^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109144789 10000000000 12693524977263 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078570629/2000000000 : ℝ)^8325 ≤ (22043924446489/50000000000000 : ℝ)^6277 := by
    have hnat : (1078570629 : ℕ)^8325*50000000000000^6277 ≤ 22043924446489^6277*2000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078570629 2000000000 22043924446489 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312489561/10000000000 : ℝ), (-2109144789/10000000000 : ℝ), (1078570629/2000000000 : ℝ)] ![(43218626116379/100000000000000 : ℝ), (12693524977263/100000000000000 : ℝ), (22043924446489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312489561/10000000000 : ℝ)|^8325 ≤ (43218626116379/100000000000000 : ℝ)^6277
        have hw : |(5312489561/10000000000 : ℝ)|=(5312489561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2109144789/10000000000 : ℝ)|^8325 ≤ (12693524977263/100000000000000 : ℝ)^6277
        have hw : |(-2109144789/10000000000 : ℝ)|=(2109144789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078570629/2000000000 : ℝ)|^8325 ≤ (22043924446489/50000000000000 : ℝ)^6277
        have hw : |(1078570629/2000000000 : ℝ)|=(1078570629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s8_6 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656244757/5000000000 : ℝ)*x 0 + (1348213279/2500000000 : ℝ)*x 1 + (-527286223/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656244757/5000000000 : ℝ)^8325 ≤ (10804656402317/25000000000000 : ℝ)^6277 := by
    have hnat : (2656244757 : ℕ)^8325*25000000000000^6277 ≤ 10804656402317^6277*5000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656244757 5000000000 10804656402317 25000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348213279/2500000000 : ℝ)^8325 ≤ (44087848578543/100000000000000 : ℝ)^6277 := by
    have hnat : (1348213279 : ℕ)^8325*100000000000000^6277 ≤ 44087848578543^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348213279 2500000000 44087848578543 100000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527286223/2500000000 : ℝ)^8325 ≤ (6346762899701/50000000000000 : ℝ)^6277 := by
    have hnat : (527286223 : ℕ)^8325*50000000000000^6277 ≤ 6346762899701^6277*2500000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527286223 2500000000 6346762899701 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656244757/5000000000 : ℝ), (1348213279/2500000000 : ℝ), (-527286223/2500000000 : ℝ)] ![(10804656402317/25000000000000 : ℝ), (44087848578543/100000000000000 : ℝ), (6346762899701/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656244757/5000000000 : ℝ)|^8325 ≤ (10804656402317/25000000000000 : ℝ)^6277
        have hw : |(2656244757/5000000000 : ℝ)|=(2656244757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348213279/2500000000 : ℝ)|^8325 ≤ (44087848578543/100000000000000 : ℝ)^6277
        have hw : |(1348213279/2500000000 : ℝ)|=(1348213279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-527286223/2500000000 : ℝ)|^8325 ≤ (6346762899701/50000000000000 : ℝ)^6277
        have hw : |(-527286223/2500000000 : ℝ)|=(527286223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1132_s8_7 (p : ℝ) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4366095317/10000000000 : ℝ)*x 0 + (4493922831/10000000000 : ℝ)*x 1 + (4241914947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366095317/10000000000 : ℝ)^8325 ≤ (3331702702219/10000000000000 : ℝ)^6277 := by
    have hnat : (4366095317 : ℕ)^8325*10000000000000^6277 ≤ 3331702702219^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366095317 10000000000 3331702702219 10000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4493922831/10000000000 : ℝ)^8325 ≤ (2163553347123/6250000000000 : ℝ)^6277 := by
    have hnat : (4493922831 : ℕ)^8325*6250000000000^6277 ≤ 2163553347123^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493922831 10000000000 2163553347123 6250000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4241914947/10000000000 : ℝ)^8325 ≤ (16033059703433/50000000000000 : ℝ)^6277 := by
    have hnat : (4241914947 : ℕ)^8325*50000000000000^6277 ≤ 16033059703433^6277*10000000000^8325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241914947 10000000000 16033059703433 50000000000000 8325 6277 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8325/2048 : ℝ)) 8325 6277 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366095317/10000000000 : ℝ), (4493922831/10000000000 : ℝ), (4241914947/10000000000 : ℝ)] ![(3331702702219/10000000000000 : ℝ), (2163553347123/6250000000000 : ℝ), (16033059703433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366095317/10000000000 : ℝ)|^8325 ≤ (3331702702219/10000000000000 : ℝ)^6277
        have hw : |(4366095317/10000000000 : ℝ)|=(4366095317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4493922831/10000000000 : ℝ)|^8325 ≤ (2163553347123/6250000000000 : ℝ)^6277
        have hw : |(4493922831/10000000000 : ℝ)|=(4493922831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4241914947/10000000000 : ℝ)|^8325 ≤ (16033059703433/50000000000000 : ℝ)^6277
        have hw : |(4241914947/10000000000 : ℝ)|=(4241914947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1132_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11341/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14043/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3511/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11339/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3511/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11339/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3511/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11339/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3511/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11339/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3511/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11339/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3511/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11339/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11339/100000 : ℝ) ^ (2081/512 : ℝ) ≤ (14366911274465627/100000000000000000000 : ℝ) := by
    have hpowers : (11339/100000 : ℝ)^2081 ≤ (14366911274465627/100000000000000000000 : ℝ)^512 := by
      have hnat : (11339 : ℕ)^2081*100000000000000000000^512 ≤ 14366911274465627^512*100000^2081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11339 100000 14366911274465627 100000000000000000000 2081 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11339/100000 : ℝ)) (X := (14366911274465627/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3511/25000 : ℝ) ^ (2081/512 : ℝ) ≤ (34278073248272951/100000000000000000000 : ℝ) := by
    have hpowers : (3511/25000 : ℝ)^2081 ≤ (34278073248272951/100000000000000000000 : ℝ)^512 := by
      have hnat : (3511 : ℕ)^2081*100000000000000000000^512 ≤ 34278073248272951^512*25000^2081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3511 25000 34278073248272951 100000000000000000000 2081 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3511/25000 : ℝ)) (X := (34278073248272951/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014366911274465627/50000000000000000000 : ℝ) ≤ (10000706877646271/10000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (50014366911274465627/50000000000000000000 : ℝ)^512 ≤ (10000706877646271/10000000000000000 : ℝ)^2081 := by
      have hnat : (50014366911274465627 : ℕ)^512*10000000000000000^2081 ≤ 10000706877646271^2081*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014366911274465627 50000000000000000000 10000706877646271 10000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000706877646271/10000000000000000 : ℝ)) (X := (50014366911274465627/50000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024322492261369289/50000000000000000000 : ℝ) ≤ (625074788761401/625000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (50024322492261369289/50000000000000000000 : ℝ)^512 ≤ (625074788761401/625000000000000 : ℝ)^2081 := by
      have hnat : (50024322492261369289 : ℕ)^512*625000000000000^2081 ≤ 625074788761401^2081*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024322492261369289 50000000000000000000 625074788761401 625000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625074788761401/625000000000000 : ℝ)) (X := (50024322492261369289/50000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034278073248272951/50000000000000000000 : ℝ) ≤ (10001686362718561/10000000000000000 : ℝ) ^ (2081/512 : ℝ) := by
    have hpowers : (50034278073248272951/50000000000000000000 : ℝ)^512 ≤ (10001686362718561/10000000000000000 : ℝ)^2081 := by
      have hnat : (50034278073248272951 : ℕ)^512*10000000000000000^2081 ≤ 10001686362718561^2081*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034278073248272951 50000000000000000000 10001686362718561 10000000000000000 512 2081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001686362718561/10000000000000000 : ℝ)) (X := (50034278073248272951/50000000000000000000 : ℝ)) (by norm_num) 2081 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14366911274465627/100000000000000000000 : ℝ) ≤ ((5408161144559693349/5410000000000000000 : ℝ)+2*(97948507229/54100000000000 : ℝ)*(11339/100000 : ℝ))^(2081/512 : ℝ) := by
    rw [show (5408161144559693349/5410000000000000000 : ℝ)+2*(97948507229/54100000000000 : ℝ)*(11339/100000 : ℝ)=(10000706877646271/10000000000000000 : ℝ) by norm_num, show 1+2*(14366911274465627/100000000000000000000 : ℝ)=(50014366911274465627/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34278073248272951/100000000000000000000 : ℝ)+(14366911274465627/100000000000000000000 : ℝ) ≤ ((5408161144559693349/5410000000000000000 : ℝ)+(97948507229/54100000000000 : ℝ)*((3511/25000 : ℝ)+(11339/100000 : ℝ)))^(2081/512 : ℝ) := by
    rw [show (5408161144559693349/5410000000000000000 : ℝ)+(97948507229/54100000000000 : ℝ)*((3511/25000 : ℝ)+(11339/100000 : ℝ))=(625074788761401/625000000000000 : ℝ) by norm_num, show 1+(34278073248272951/100000000000000000000 : ℝ)+(14366911274465627/100000000000000000000 : ℝ)=(50024322492261369289/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34278073248272951/100000000000000000000 : ℝ) ≤ ((5408161144559693349/5410000000000000000 : ℝ)+2*(97948507229/54100000000000 : ℝ)*(3511/25000 : ℝ))^(2081/512 : ℝ) := by
    rw [show (5408161144559693349/5410000000000000000 : ℝ)+2*(97948507229/54100000000000 : ℝ)*(3511/25000 : ℝ)=(10001686362718561/10000000000000000 : ℝ) by norm_num, show 1+2*(34278073248272951/100000000000000000000 : ℝ)=(50034278073248272951/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5408161144559693349/5410000000000000000 : ℝ)*(X 1 0+X 2 0)+(97948507229/54100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (11339/100000 : ℝ)) (hi := (3511/25000 : ℝ)) (c := (5408161144559693349/5410000000000000000 : ℝ)) (alpha := (97948507229/54100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5408161144559693349/5410000000000000000 : ℝ)*(X 0 1+X 2 1)+(97948507229/54100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (11339/100000 : ℝ)) (hi := (3511/25000 : ℝ)) (c := (5408161144559693349/5410000000000000000 : ℝ)) (alpha := (97948507229/54100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5408161144559693349/5410000000000000000 : ℝ)*(X 0 2+X 1 2)+(97948507229/54100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2081/512 : ℝ)) (lo := (11339/100000 : ℝ)) (hi := (3511/25000 : ℝ)) (c := (5408161144559693349/5410000000000000000 : ℝ)) (alpha := (97948507229/54100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-434336339/2000000000 : ℝ)*X 0 0+(5393174453/10000000000 : ℝ)*X 0 1+(5265613159/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344783653/10000000000 : ℝ)*X 1 0+(-1118192411/5000000000 : ℝ)*X 1 1+(1316403313/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534478361/1000000000 : ℝ)*X 2 0+(5265613239/10000000000 : ℝ)*X 2 1+(-17471757/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4366085641/10000000000 : ℝ)*X 0 0+(1060319177/2500000000 : ℝ)*X 0 1+(1755687/3906250 : ℝ)*X 0 2+(4366085641/10000000000 : ℝ)*X 1 0+(1060319177/2500000000 : ℝ)*X 1 1+(1755687/3906250 : ℝ)*X 1 2+(4366085641/10000000000 : ℝ)*X 2 0+(1060319177/2500000000 : ℝ)*X 2 1+(1755687/3906250 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2171686273/10000000000 : ℝ)*X 0 0+(5265933647/10000000000 : ℝ)*X 0 1+(107857061/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312489561/10000000000 : ℝ)*X 1 0+(-2109144789/10000000000 : ℝ)*X 1 1+(1078570629/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656244757/5000000000 : ℝ)*X 2 0+(1348213279/2500000000 : ℝ)*X 2 1+(-527286223/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4366095317/10000000000 : ℝ)*X 0 0+(4493922831/10000000000 : ℝ)*X 0 1+(4241914947/10000000000 : ℝ)*X 0 2+(4366095317/10000000000 : ℝ)*X 1 0+(4493922831/10000000000 : ℝ)*X 1 1+(4241914947/10000000000 : ℝ)*X 1 2+(4366095317/10000000000 : ℝ)*X 2 0+(4493922831/10000000000 : ℝ)*X 2 1+(4241914947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1132_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (460815203416868760136898733/135250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (355099631/50000000000000 : ℝ)*(base19) + (617438653/100000000000000 : ℝ)*(base23) + (1252101/6250000000000 : ℝ)*(upper2) + (2374681/1562500000000 : ℝ)*(upper3) + (17951333/50000000000000 : ℝ)*(upper4) + (5893802980647261/100000000000000 : ℝ)*(major0) + (5893802980647261/100000000000000 : ℝ)*(major1) + (5893802980647261/100000000000000 : ℝ)*(major2) + (1567879272013921/20000000000000 : ℝ)*(sp0) + (7839415860732319/100000000000000 : ℝ)*(sp1) + (7839415953492929/100000000000000 : ℝ)*(sp2) + (123380540361449/3125000000000 : ℝ)*(sp3) + (2526357747/12500000000000 : ℝ)*(sp4) + (2996306337/25000000000000 : ℝ)*(sp7) + (987047319197929/25000000000000 : ℝ)*(f.failure) + (7839416570931581/100000000000000 : ℝ)*(f.sum) + (357735601917/338125000000000000000000000 : ℝ)*base66 + (2878212697144667089/541000000000000000000000000000000 : ℝ)*base67 + (1568462386222667089/541000000000000000000000000000000 : ℝ)*base69 + (7571379992222667089/541000000000000000000000000000000 : ℝ)*base71 + (3790702289399/2705000000000000000000000000 : ℝ)*base73 + (1186228361609667089/541000000000000000000000000000000 : ℝ)*base75 + (4341549193019667089/541000000000000000000000000000000 : ℝ)*base77 + (1426080409109332911/541000000000000000000000000000000 : ℝ)*base80 + (3076607667709/2705000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (27448943/2500000000000000000000 : ℝ)*base90 + (27448943/2500000000000000000000 : ℝ)*base92 + (27448943/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41239026703232365922027427/4226562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1408854349/100000000000000 : ℝ)*(base19) + (359724281/20000000000000 : ℝ)*(base23) + (127126619/20000000000000 : ℝ)*(lower1) + (44148439/50000000000000 : ℝ)*(upper3) + (222172071/100000000000000 : ℝ)*(lower4) + (20784653/50000000000000 : ℝ)*(upper5) + (185110313012543/3125000000000 : ℝ)*(major0) + (185110313012543/3125000000000 : ℝ)*(major1) + (185110313012543/3125000000000 : ℝ)*(major2) + (6788347421/100000000000000 : ℝ)*(sp2) + (7878956639257707/100000000000000 : ℝ)*(sp4) + (3939477615201679/50000000000000 : ℝ)*(sp5) + (7878948052288881/100000000000000 : ℝ)*(sp6) + (992025767077023/25000000000000 : ℝ)*(sp7) + (992025767077023/25000000000000 : ℝ)*(f.failure) + (7878956639257707/100000000000000 : ℝ)*(f.sum) + (19372503588239/2705000000000000000000000000 : ℝ)*base65 + (1439298263067220257/16906250000000000000000000000000 : ℝ)*base67 + (116649770823064007/16906250000000000000000000000000 : ℝ)*base69 + (675609961947185993/16906250000000000000000000000000 : ℝ)*base72 + (4419619719577/1352500000000000000000000000 : ℝ)*base73 + (456098553144435993/16906250000000000000000000000000 : ℝ)*base76 + (8019315145126507/16906250000000000000000000000000 : ℝ)*base77 + (367666149603907757/16906250000000000000000000000000 : ℝ)*base79 + (3209968029453/338125000000000000000000000 : ℝ)*base81 + (850441/2500000000000000000000 : ℝ)*base90 + (850441/2500000000000000000000 : ℝ)*base92 + (850441/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1132_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1132_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1132_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (113/1000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1132_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1132_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1132_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2081/512 : ℝ) ≤ p) (hpb : p ≤ (8325/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149278633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (113/1000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14043/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1132_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
