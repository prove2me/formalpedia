-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1315_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:41:40.832357+00:00
-- url     : https://prove2.me/submissions/aac409d7-3faf-428b-a670-d03895d9e4b8

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
theorem support_rectangle_w1315_s6_0 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-413504303/2000000000 : ℝ)*x 0 + (5414124709/10000000000 : ℝ)*x 1 + (5243719631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (413504303/2000000000 : ℝ)^4275 ≤ (1258434124049/10000000000000 : ℝ)^3251 := by
    have hnat : (413504303 : ℕ)^4275*10000000000000^3251 ≤ 1258434124049^3251*2000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413504303 2000000000 1258434124049 10000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414124709/10000000000 : ℝ)^4275 ≤ (4462672156721/10000000000000 : ℝ)^3251 := by
    have hnat : (5414124709 : ℕ)^4275*10000000000000^3251 ≤ 4462672156721^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414124709 10000000000 4462672156721 10000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243719631/10000000000 : ℝ)^4275 ≤ (21394468588019/50000000000000 : ℝ)^3251 := by
    have hnat : (5243719631 : ℕ)^4275*50000000000000^3251 ≤ 21394468588019^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243719631 10000000000 21394468588019 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-413504303/2000000000 : ℝ), (5414124709/10000000000 : ℝ), (5243719631/10000000000 : ℝ)] ![(1258434124049/10000000000000 : ℝ), (4462672156721/10000000000000 : ℝ), (21394468588019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-413504303/2000000000 : ℝ)|^4275 ≤ (1258434124049/10000000000000 : ℝ)^3251
        have hw : |(-413504303/2000000000 : ℝ)|=(413504303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414124709/10000000000 : ℝ)|^4275 ≤ (4462672156721/10000000000000 : ℝ)^3251
        have hw : |(5414124709/10000000000 : ℝ)|=(5414124709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243719631/10000000000 : ℝ)|^4275 ≤ (21394468588019/50000000000000 : ℝ)^3251
        have hw : |(5243719631/10000000000 : ℝ)|=(5243719631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s6_1 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337363331/2500000000 : ℝ)*x 0 + (-430873387/2000000000 : ℝ)*x 1 + (5243718863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337363331/2500000000 : ℝ)^4275 ≤ (43927076095073/100000000000000 : ℝ)^3251 := by
    have hnat : (1337363331 : ℕ)^4275*100000000000000^3251 ≤ 43927076095073^3251*2500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337363331 2500000000 43927076095073 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430873387/2000000000 : ℝ)^4275 ≤ (6641997478599/50000000000000 : ℝ)^3251 := by
    have hnat : (430873387 : ℕ)^4275*50000000000000^3251 ≤ 6641997478599^3251*2000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430873387 2000000000 6641997478599 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243718863/10000000000 : ℝ)^4275 ≤ (42788928935181/100000000000000 : ℝ)^3251 := by
    have hnat : (5243718863 : ℕ)^4275*100000000000000^3251 ≤ 42788928935181^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243718863 10000000000 42788928935181 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337363331/2500000000 : ℝ), (-430873387/2000000000 : ℝ), (5243718863/10000000000 : ℝ)] ![(43927076095073/100000000000000 : ℝ), (6641997478599/50000000000000 : ℝ), (42788928935181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337363331/2500000000 : ℝ)|^4275 ≤ (43927076095073/100000000000000 : ℝ)^3251
        have hw : |(1337363331/2500000000 : ℝ)|=(1337363331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-430873387/2000000000 : ℝ)|^4275 ≤ (6641997478599/50000000000000 : ℝ)^3251
        have hw : |(-430873387/2000000000 : ℝ)|=(430873387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243718863/10000000000 : ℝ)|^4275 ≤ (42788928935181/100000000000000 : ℝ)^3251
        have hw : |(5243718863/10000000000 : ℝ)|=(5243718863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s6_2 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674726177/5000000000 : ℝ)*x 0 + (2621859731/5000000000 : ℝ)*x 1 + (-1077183717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674726177/5000000000 : ℝ)^4275 ≤ (10981766405261/25000000000000 : ℝ)^3251 := by
    have hnat : (2674726177 : ℕ)^4275*25000000000000^3251 ≤ 10981766405261^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674726177 5000000000 10981766405261 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621859731/5000000000 : ℝ)^4275 ≤ (2139446768131/5000000000000 : ℝ)^3251 := by
    have hnat : (2621859731 : ℕ)^4275*5000000000000^3251 ≤ 2139446768131^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621859731 5000000000 2139446768131 5000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077183717/5000000000 : ℝ)^4275 ≤ (531359960129/4000000000000 : ℝ)^3251 := by
    have hnat : (1077183717 : ℕ)^4275*4000000000000^3251 ≤ 531359960129^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077183717 5000000000 531359960129 4000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674726177/5000000000 : ℝ), (2621859731/5000000000 : ℝ), (-1077183717/5000000000 : ℝ)] ![(10981766405261/25000000000000 : ℝ), (2139446768131/5000000000000 : ℝ), (531359960129/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674726177/5000000000 : ℝ)|^4275 ≤ (10981766405261/25000000000000 : ℝ)^3251
        have hw : |(2674726177/5000000000 : ℝ)|=(2674726177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621859731/5000000000 : ℝ)|^4275 ≤ (2139446768131/5000000000000 : ℝ)^3251
        have hw : |(2621859731/5000000000 : ℝ)|=(2621859731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1077183717/5000000000 : ℝ)|^4275 ≤ (531359960129/4000000000000 : ℝ)^3251
        have hw : |(-1077183717/5000000000 : ℝ)|=(1077183717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s6_3 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2166862943/5000000000 : ℝ)*x 0 + (2080239861/5000000000 : ℝ)*x 1 + (14105577/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166862943/5000000000 : ℝ)^4275 ≤ (16651373255779/50000000000000 : ℝ)^3251 := by
    have hnat : (2166862943 : ℕ)^4275*50000000000000^3251 ≤ 16651373255779^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166862943 5000000000 16651373255779 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080239861/5000000000 : ℝ)^4275 ≤ (31563212442557/100000000000000 : ℝ)^3251 := by
    have hnat : (2080239861 : ℕ)^4275*100000000000000^3251 ≤ 31563212442557^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080239861 5000000000 31563212442557 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14105577/31250000 : ℝ)^4275 ≤ (35134041036479/100000000000000 : ℝ)^3251 := by
    have hnat : (14105577 : ℕ)^4275*100000000000000^3251 ≤ 35134041036479^3251*31250000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14105577 31250000 35134041036479 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2166862943/5000000000 : ℝ), (2080239861/5000000000 : ℝ), (14105577/31250000 : ℝ)] ![(16651373255779/50000000000000 : ℝ), (31563212442557/100000000000000 : ℝ), (35134041036479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2166862943/5000000000 : ℝ)|^4275 ≤ (16651373255779/50000000000000 : ℝ)^3251
        have hw : |(2166862943/5000000000 : ℝ)|=(2166862943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2080239861/5000000000 : ℝ)|^4275 ≤ (31563212442557/100000000000000 : ℝ)^3251
        have hw : |(2080239861/5000000000 : ℝ)|=(2080239861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(14105577/31250000 : ℝ)|^4275 ≤ (35134041036479/100000000000000 : ℝ)^3251
        have hw : |(14105577/31250000 : ℝ)|=(14105577/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s6_4 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-103376729/500000000 : ℝ)*x 0 + (5244328111/10000000000 : ℝ)*x 1 + (2706756329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103376729/500000000 : ℝ)^4275 ≤ (12584445811053/100000000000000 : ℝ)^3251 := by
    have hnat : (103376729 : ℕ)^4275*100000000000000^3251 ≤ 12584445811053^3251*500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103376729 500000000 12584445811053 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244328111/10000000000 : ℝ)^4275 ≤ (21397733229051/50000000000000 : ℝ)^3251 := by
    have hnat : (5244328111 : ℕ)^4275*50000000000000^3251 ≤ 21397733229051^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244328111 10000000000 21397733229051 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706756329/5000000000 : ℝ)^4275 ≤ (44620087715531/100000000000000 : ℝ)^3251 := by
    have hnat : (2706756329 : ℕ)^4275*100000000000000^3251 ≤ 44620087715531^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706756329 5000000000 44620087715531 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-103376729/500000000 : ℝ), (5244328111/10000000000 : ℝ), (2706756329/5000000000 : ℝ)] ![(12584445811053/100000000000000 : ℝ), (21397733229051/50000000000000 : ℝ), (44620087715531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-103376729/500000000 : ℝ)|^4275 ≤ (12584445811053/100000000000000 : ℝ)^3251
        have hw : |(-103376729/500000000 : ℝ)|=(103376729/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244328111/10000000000 : ℝ)|^4275 ≤ (21397733229051/50000000000000 : ℝ)^3251
        have hw : |(5244328111/10000000000 : ℝ)|=(5244328111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706756329/5000000000 : ℝ)|^4275 ≤ (44620087715531/100000000000000 : ℝ)^3251
        have hw : |(2706756329/5000000000 : ℝ)|=(2706756329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s6_5 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652849839/5000000000 : ℝ)*x 0 + (-198457399/1000000000 : ℝ)*x 1 + (5413512877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652849839/5000000000 : ℝ)^4275 ≤ (43455235333183/100000000000000 : ℝ)^3251 := by
    have hnat : (2652849839 : ℕ)^4275*100000000000000^3251 ≤ 43455235333183^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652849839 5000000000 43455235333183 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (198457399/1000000000 : ℝ)^4275 ≤ (1490584320187/12500000000000 : ℝ)^3251 := by
    have hnat : (198457399 : ℕ)^4275*12500000000000^3251 ≤ 1490584320187^3251*1000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198457399 1000000000 1490584320187 12500000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413512877/10000000000 : ℝ)^4275 ≤ (44620090089169/100000000000000 : ℝ)^3251 := by
    have hnat : (5413512877 : ℕ)^4275*100000000000000^3251 ≤ 44620090089169^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413512877 10000000000 44620090089169 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652849839/5000000000 : ℝ), (-198457399/1000000000 : ℝ), (5413512877/10000000000 : ℝ)] ![(43455235333183/100000000000000 : ℝ), (1490584320187/12500000000000 : ℝ), (44620090089169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652849839/5000000000 : ℝ)|^4275 ≤ (43455235333183/100000000000000 : ℝ)^3251
        have hw : |(2652849839/5000000000 : ℝ)|=(2652849839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-198457399/1000000000 : ℝ)|^4275 ≤ (1490584320187/12500000000000 : ℝ)^3251
        have hw : |(-198457399/1000000000 : ℝ)|=(198457399/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413512877/10000000000 : ℝ)|^4275 ≤ (44620090089169/100000000000000 : ℝ)^3251
        have hw : |(5413512877/10000000000 : ℝ)|=(5413512877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s6_6 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165803119/312500000 : ℝ)*x 0 + (2706756309/5000000000 : ℝ)*x 1 + (-1984574169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165803119/312500000 : ℝ)^4275 ≤ (10863809183323/25000000000000 : ℝ)^3251 := by
    have hnat : (165803119 : ℕ)^4275*25000000000000^3251 ≤ 10863809183323^3251*312500000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165803119 312500000 10863809183323 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706756309/5000000000 : ℝ)^4275 ≤ (4462008728199/10000000000000 : ℝ)^3251 := by
    have hnat : (2706756309 : ℕ)^4275*10000000000000^3251 ≤ 4462008728199^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706756309 5000000000 4462008728199 10000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1984574169/10000000000 : ℝ)^4275 ≤ (11924675975829/100000000000000 : ℝ)^3251 := by
    have hnat : (1984574169 : ℕ)^4275*100000000000000^3251 ≤ 11924675975829^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984574169 10000000000 11924675975829 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165803119/312500000 : ℝ), (2706756309/5000000000 : ℝ), (-1984574169/10000000000 : ℝ)] ![(10863809183323/25000000000000 : ℝ), (4462008728199/10000000000000 : ℝ), (11924675975829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165803119/312500000 : ℝ)|^4275 ≤ (10863809183323/25000000000000 : ℝ)^3251
        have hw : |(165803119/312500000 : ℝ)|=(165803119/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706756309/5000000000 : ℝ)|^4275 ≤ (4462008728199/10000000000000 : ℝ)^3251
        have hw : |(2706756309/5000000000 : ℝ)|=(2706756309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1984574169/10000000000 : ℝ)|^4275 ≤ (11924675975829/100000000000000 : ℝ)^3251
        have hw : |(-1984574169/10000000000 : ℝ)|=(1984574169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s6_7 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083438069/2500000000 : ℝ)*x 0 + (70508147/156250000 : ℝ)*x 1 + (2080874477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083438069/2500000000 : ℝ)^4275 ≤ (33303013183651/100000000000000 : ℝ)^3251 := by
    have hnat : (1083438069 : ℕ)^4275*100000000000000^3251 ≤ 33303013183651^3251*2500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083438069 2500000000 33303013183651 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70508147/156250000 : ℝ)^4275 ≤ (17560555936977/50000000000000 : ℝ)^3251 := by
    have hnat : (70508147 : ℕ)^4275*50000000000000^3251 ≤ 17560555936977^3251*156250000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70508147 156250000 17560555936977 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2080874477/5000000000 : ℝ)^4275 ≤ (15787937461903/50000000000000 : ℝ)^3251 := by
    have hnat : (2080874477 : ℕ)^4275*50000000000000^3251 ≤ 15787937461903^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080874477 5000000000 15787937461903 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083438069/2500000000 : ℝ), (70508147/156250000 : ℝ), (2080874477/5000000000 : ℝ)] ![(33303013183651/100000000000000 : ℝ), (17560555936977/50000000000000 : ℝ), (15787937461903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083438069/2500000000 : ℝ)|^4275 ≤ (33303013183651/100000000000000 : ℝ)^3251
        have hw : |(1083438069/2500000000 : ℝ)|=(1083438069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(70508147/156250000 : ℝ)|^4275 ≤ (17560555936977/50000000000000 : ℝ)^3251
        have hw : |(70508147/156250000 : ℝ)|=(70508147/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2080874477/5000000000 : ℝ)|^4275 ≤ (15787937461903/50000000000000 : ℝ)^3251
        have hw : |(2080874477/5000000000 : ℝ)|=(2080874477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1315_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (147/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5537/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11083/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1469/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (147/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5537/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (147/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5537/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (147/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5537/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (147/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5537/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (147/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5537/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (147/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5537/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5537/50000 : ℝ) ^ (2137/512 : ℝ) ≤ (5129338112214587/50000000000000000000 : ℝ) := by
    have hpowers : (5537/50000 : ℝ)^2137 ≤ (5129338112214587/50000000000000000000 : ℝ)^512 := by
      have hnat : (5537 : ℕ)^2137*50000000000000000000^512 ≤ 5129338112214587^512*50000^2137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5537 50000 5129338112214587 50000000000000000000 2137 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5537/50000 : ℝ)) (X := (5129338112214587/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hpowhi : (147/1000 : ℝ) ^ (2137/512 : ℝ) ≤ (6691995931213563/20000000000000000000 : ℝ) := by
    have hpowers : (147/1000 : ℝ)^2137 ≤ (6691995931213563/20000000000000000000 : ℝ)^512 := by
      have hnat : (147 : ℕ)^2137*20000000000000000000^512 ≤ 6691995931213563^512*1000^2137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        147 1000 6691995931213563 20000000000000000000 2137 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (147/1000 : ℝ)) (X := (6691995931213563/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005129338112214587/25000000000000000000 : ℝ) ≤ (2500122883307037/2500000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (25005129338112214587/25000000000000000000 : ℝ)^512 ≤ (2500122883307037/2500000000000000 : ℝ)^2137 := by
      have hnat : (25005129338112214587 : ℕ)^512*2500000000000000^2137 ≤ 2500122883307037^2137*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005129338112214587 25000000000000000000 2500122883307037 2500000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500122883307037/2500000000000000 : ℝ)) (X := (25005129338112214587/25000000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043718655880496989/100000000000000000000 : ℝ) ≤ (1250130909172229/1250000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (100043718655880496989/100000000000000000000 : ℝ)^512 ≤ (1250130909172229/1250000000000000 : ℝ)^2137 := by
      have hnat : (100043718655880496989 : ℕ)^512*1250000000000000^2137 ≤ 1250130909172229^2137*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043718655880496989 100000000000000000000 1250130909172229 1250000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250130909172229/1250000000000000 : ℝ)) (X := (100043718655880496989/100000000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006691995931213563/10000000000000000000 : ℝ) ≤ (2500400753381879/2500000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (10006691995931213563/10000000000000000000 : ℝ)^512 ≤ (2500400753381879/2500000000000000 : ℝ)^2137 := by
      have hnat : (10006691995931213563 : ℕ)^512*2500000000000000^2137 ≤ 2500400753381879^2137*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006691995931213563 10000000000000000000 2500400753381879 2500000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500400753381879/2500000000000000 : ℝ)) (X := (10006691995931213563/10000000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5129338112214587/50000000000000000000 : ℝ) ≤ ((92473147363903223/92500000000000000 : ℝ)+2*(138935037421/90650000000000 : ℝ)*(5537/50000 : ℝ))^(2137/512 : ℝ) := by
    rw [show (92473147363903223/92500000000000000 : ℝ)+2*(138935037421/90650000000000 : ℝ)*(5537/50000 : ℝ)=(2500122883307037/2500000000000000 : ℝ) by norm_num, show 1+2*(5129338112214587/50000000000000000000 : ℝ)=(25005129338112214587/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6691995931213563/20000000000000000000 : ℝ)+(5129338112214587/50000000000000000000 : ℝ) ≤ ((92473147363903223/92500000000000000 : ℝ)+(138935037421/90650000000000 : ℝ)*((147/1000 : ℝ)+(5537/50000 : ℝ)))^(2137/512 : ℝ) := by
    rw [show (92473147363903223/92500000000000000 : ℝ)+(138935037421/90650000000000 : ℝ)*((147/1000 : ℝ)+(5537/50000 : ℝ))=(1250130909172229/1250000000000000 : ℝ) by norm_num, show 1+(6691995931213563/20000000000000000000 : ℝ)+(5129338112214587/50000000000000000000 : ℝ)=(100043718655880496989/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6691995931213563/20000000000000000000 : ℝ) ≤ ((92473147363903223/92500000000000000 : ℝ)+2*(138935037421/90650000000000 : ℝ)*(147/1000 : ℝ))^(2137/512 : ℝ) := by
    rw [show (92473147363903223/92500000000000000 : ℝ)+2*(138935037421/90650000000000 : ℝ)*(147/1000 : ℝ)=(2500400753381879/2500000000000000 : ℝ) by norm_num, show 1+2*(6691995931213563/20000000000000000000 : ℝ)=(10006691995931213563/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (92473147363903223/92500000000000000 : ℝ)*(X 1 0+X 2 0)+(138935037421/90650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (5537/50000 : ℝ)) (hi := (147/1000 : ℝ)) (c := (92473147363903223/92500000000000000 : ℝ)) (alpha := (138935037421/90650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (92473147363903223/92500000000000000 : ℝ)*(X 0 1+X 2 1)+(138935037421/90650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (5537/50000 : ℝ)) (hi := (147/1000 : ℝ)) (c := (92473147363903223/92500000000000000 : ℝ)) (alpha := (138935037421/90650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (92473147363903223/92500000000000000 : ℝ)*(X 0 2+X 1 2)+(138935037421/90650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (5537/50000 : ℝ)) (hi := (147/1000 : ℝ)) (c := (92473147363903223/92500000000000000 : ℝ)) (alpha := (138935037421/90650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-413504303/2000000000 : ℝ)*X 0 0+(5414124709/10000000000 : ℝ)*X 0 1+(5243719631/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337363331/2500000000 : ℝ)*X 1 0+(-430873387/2000000000 : ℝ)*X 1 1+(5243718863/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674726177/5000000000 : ℝ)*X 2 0+(2621859731/5000000000 : ℝ)*X 2 1+(-1077183717/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2166862943/5000000000 : ℝ)*X 0 0+(2080239861/5000000000 : ℝ)*X 0 1+(14105577/31250000 : ℝ)*X 0 2+(2166862943/5000000000 : ℝ)*X 1 0+(2080239861/5000000000 : ℝ)*X 1 1+(14105577/31250000 : ℝ)*X 1 2+(2166862943/5000000000 : ℝ)*X 2 0+(2080239861/5000000000 : ℝ)*X 2 1+(14105577/31250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-103376729/500000000 : ℝ)*X 0 0+(5244328111/10000000000 : ℝ)*X 0 1+(2706756329/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652849839/5000000000 : ℝ)*X 1 0+(-198457399/1000000000 : ℝ)*X 1 1+(5413512877/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165803119/312500000 : ℝ)*X 2 0+(2706756309/5000000000 : ℝ)*X 2 1+(-1984574169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1083438069/2500000000 : ℝ)*X 0 0+(70508147/156250000 : ℝ)*X 0 1+(2080874477/5000000000 : ℝ)*X 0 2+(1083438069/2500000000 : ℝ)*X 1 0+(70508147/156250000 : ℝ)*X 1 1+(2080874477/5000000000 : ℝ)*X 1 2+(1083438069/2500000000 : ℝ)*X 2 0+(70508147/156250000 : ℝ)*X 2 1+(2080874477/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45860107725532098801110817/4625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2155322293/100000000000000 : ℝ)*(base19) + (187680827/12500000000000 : ℝ)*(base23) + (2741693/5000000000000 : ℝ)*(upper3) + (26790599/10000000000000 : ℝ)*(lower4) + (4349457323676493/100000000000000 : ℝ)*(major0) + (4349457323676493/100000000000000 : ℝ)*(major1) + (4349457323676493/100000000000000 : ℝ)*(major2) + (5868416734127897/100000000000000 : ℝ)*(sp0) + (5868445180843227/100000000000000 : ℝ)*(sp1) + (586843476005243/10000000000000 : ℝ)*(sp2) + (707611065319737/25000000000000 : ℝ)*(sp3) + (30602037623/100000000000000 : ℝ)*(sp4) + (5537333237/50000000000000 : ℝ)*(sp6) + (5679846303/25000000000000 : ℝ)*(sp7) + (17690418629151/625000000000 : ℝ)*(f.failure) + (73355591702069/1250000000000 : ℝ)*(f.sum) + (3699145911383/1295000000000000000000000000 : ℝ)*base65 + (944003068862291427/64750000000000000000000000000000 : ℝ)*base68 + (659987996169541427/64750000000000000000000000000000 : ℝ)*base70 + (178911574215208573/64750000000000000000000000000000 : ℝ)*base71 + (2261905576407/1295000000000000000000000000 : ℝ)*base74 + (1423993510329541427/64750000000000000000000000000000 : ℝ)*base76 + (192203411221208573/64750000000000000000000000000000 : ℝ)*base77 + (528277925535791427/64750000000000000000000000000000 : ℝ)*base80 + (274168839423/80937500000000000000000000 : ℝ)*base81 + (26593/12500000000000000000 : ℝ)*base89 + (26593/12500000000000000000 : ℝ)*base91 + (26593/12500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1016279129215359207369873609/226625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (800532471/100000000000000 : ℝ)*(base19) + (238268693/25000000000000 : ℝ)*(base23) + (63440203/50000000000000 : ℝ)*(upper3) + (1029539/3125000000000 : ℝ)*(lower4) + (7963951/4000000000000 : ℝ)*(upper5) + (4380778999053063/100000000000000 : ℝ)*(major0) + (4380778999053063/100000000000000 : ℝ)*(major1) + (4380778999053063/100000000000000 : ℝ)*(major2) + (21775048163/100000000000000 : ℝ)*(sp1) + (15181676789/100000000000000 : ℝ)*(sp2) + (2955353936359983/50000000000000 : ℝ)*(sp4) + (1477671324284833/25000000000000 : ℝ)*(sp5) + (2955345868984203/50000000000000 : ℝ)*(sp6) + (1425424987952929/50000000000000 : ℝ)*(sp7) + (1425424987952929/50000000000000 : ℝ)*(f.failure) + (2955353936359983/50000000000000 : ℝ)*(f.sum) + (34393172482637/4532500000000000000000000000 : ℝ)*base66 + (5391127912803969599/453250000000000000000000000000000 : ℝ)*base68 + (4315624526381469599/453250000000000000000000000000000 : ℝ)*base70 + (1711118382638469599/453250000000000000000000000000000 : ℝ)*base72 + (63500855763589/9065000000000000000000000000 : ℝ)*base74 + (4891907972047719599/453250000000000000000000000000000 : ℝ)*base76 + (6548881553287969599/453250000000000000000000000000000 : ℝ)*base78 + (6349547790953969599/453250000000000000000000000000000 : ℝ)*base80 + (25351605344467/4532500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (14225847/1000000000000000000000 : ℝ)*base89 + (14225847/1000000000000000000000 : ℝ)*base91 + (14225847/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1315_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (147/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5537/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11083/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1469/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1315_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1315_s7_0 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2067532533/10000000000 : ℝ)*x 0 + (1082808267/2000000000 : ℝ)*x 1 + (524379563/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2067532533/10000000000 : ℝ)^4275 ≤ (12584429427117/100000000000000 : ℝ)^3251 := by
    have hnat : (2067532533 : ℕ)^4275*100000000000000^3251 ≤ 12584429427117^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067532533 10000000000 12584429427117 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082808267/2000000000 : ℝ)^4275 ≤ (22312908942781/50000000000000 : ℝ)^3251 := by
    have hnat : (1082808267 : ℕ)^4275*50000000000000^3251 ≤ 22312908942781^3251*2000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082808267 2000000000 22312908942781 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524379563/1000000000 : ℝ)^4275 ≤ (8557950533739/20000000000000 : ℝ)^3251 := by
    have hnat : (524379563 : ℕ)^4275*20000000000000^3251 ≤ 8557950533739^3251*1000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524379563 1000000000 8557950533739 20000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2067532533/10000000000 : ℝ), (1082808267/2000000000 : ℝ), (524379563/1000000000 : ℝ)] ![(12584429427117/100000000000000 : ℝ), (22312908942781/50000000000000 : ℝ), (8557950533739/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2067532533/10000000000 : ℝ)|^4275 ≤ (12584429427117/100000000000000 : ℝ)^3251
        have hw : |(-2067532533/10000000000 : ℝ)|=(2067532533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082808267/2000000000 : ℝ)|^4275 ≤ (22312908942781/50000000000000 : ℝ)^3251
        have hw : |(1082808267/2000000000 : ℝ)|=(1082808267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524379563/1000000000 : ℝ)|^4275 ≤ (8557950533739/20000000000000 : ℝ)^3251
        have hw : |(524379563/1000000000 : ℝ)|=(524379563/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s7_1 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349431751/10000000000 : ℝ)*x 0 + (-2154294147/10000000000 : ℝ)*x 1 + (1310948893/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349431751/10000000000 : ℝ)^4275 ≤ (43926843150653/100000000000000 : ℝ)^3251 := by
    have hnat : (5349431751 : ℕ)^4275*100000000000000^3251 ≤ 43926843150653^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349431751 10000000000 43926843150653 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2154294147/10000000000 : ℝ)^4275 ≤ (207553199619/1562500000000 : ℝ)^3251 := by
    have hnat : (2154294147 : ℕ)^4275*1562500000000^3251 ≤ 207553199619^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154294147 10000000000 207553199619 1562500000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310948893/2500000000 : ℝ)^4275 ≤ (167147468931/390625000000 : ℝ)^3251 := by
    have hnat : (1310948893 : ℕ)^4275*390625000000^3251 ≤ 167147468931^3251*2500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310948893 2500000000 167147468931 390625000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349431751/10000000000 : ℝ), (-2154294147/10000000000 : ℝ), (1310948893/2500000000 : ℝ)] ![(43926843150653/100000000000000 : ℝ), (207553199619/1562500000000 : ℝ), (167147468931/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349431751/10000000000 : ℝ)|^4275 ≤ (43926843150653/100000000000000 : ℝ)^3251
        have hw : |(5349431751/10000000000 : ℝ)|=(5349431751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2154294147/10000000000 : ℝ)|^4275 ≤ (207553199619/1562500000000 : ℝ)^3251
        have hw : |(-2154294147/10000000000 : ℝ)|=(2154294147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310948893/2500000000 : ℝ)|^4275 ≤ (167147468931/390625000000 : ℝ)^3251
        have hw : |(1310948893/2500000000 : ℝ)|=(1310948893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s7_2 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349430811/10000000000 : ℝ)*x 0 + (5243795137/10000000000 : ℝ)*x 1 + (-86171839/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349430811/10000000000 : ℝ)^4275 ≤ (343178382817/781250000000 : ℝ)^3251 := by
    have hnat : (5349430811 : ℕ)^4275*781250000000^3251 ≤ 343178382817^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349430811 10000000000 343178382817 781250000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243795137/10000000000 : ℝ)^4275 ≤ (21394873689321/50000000000000 : ℝ)^3251 := by
    have hnat : (5243795137 : ℕ)^4275*50000000000000^3251 ≤ 21394873689321^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243795137 10000000000 21394873689321 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86171839/400000000 : ℝ)^4275 ≤ (13283419597377/100000000000000 : ℝ)^3251 := by
    have hnat : (86171839 : ℕ)^4275*100000000000000^3251 ≤ 13283419597377^3251*400000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86171839 400000000 13283419597377 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349430811/10000000000 : ℝ), (5243795137/10000000000 : ℝ), (-86171839/400000000 : ℝ)] ![(343178382817/781250000000 : ℝ), (21394873689321/50000000000000 : ℝ), (13283419597377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349430811/10000000000 : ℝ)|^4275 ≤ (343178382817/781250000000 : ℝ)^3251
        have hw : |(5349430811/10000000000 : ℝ)|=(5349430811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243795137/10000000000 : ℝ)|^4275 ≤ (21394873689321/50000000000000 : ℝ)^3251
        have hw : |(5243795137/10000000000 : ℝ)|=(5243795137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-86171839/400000000 : ℝ)|^4275 ≤ (13283419597377/100000000000000 : ℝ)^3251
        have hw : |(-86171839/400000000 : ℝ)|=(86171839/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s7_3 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (433373097/1000000000 : ℝ)*x 0 + (2080322289/5000000000 : ℝ)*x 1 + (225680947/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433373097/1000000000 : ℝ)^4275 ≤ (33302797885559/100000000000000 : ℝ)^3251 := by
    have hnat : (433373097 : ℕ)^4275*100000000000000^3251 ≤ 33302797885559^3251*1000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433373097 1000000000 33302797885559 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080322289/5000000000 : ℝ)^4275 ≤ (31564857058161/100000000000000 : ℝ)^3251 := by
    have hnat : (2080322289 : ℕ)^4275*100000000000000^3251 ≤ 31564857058161^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080322289 5000000000 31564857058161 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225680947/500000000 : ℝ)^4275 ≤ (35132345034257/100000000000000 : ℝ)^3251 := by
    have hnat : (225680947 : ℕ)^4275*100000000000000^3251 ≤ 35132345034257^3251*500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225680947 500000000 35132345034257 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(433373097/1000000000 : ℝ), (2080322289/5000000000 : ℝ), (225680947/500000000 : ℝ)] ![(33302797885559/100000000000000 : ℝ), (31564857058161/100000000000000 : ℝ), (35132345034257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(433373097/1000000000 : ℝ)|^4275 ≤ (33302797885559/100000000000000 : ℝ)^3251
        have hw : |(433373097/1000000000 : ℝ)|=(433373097/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2080322289/5000000000 : ℝ)|^4275 ≤ (31564857058161/100000000000000 : ℝ)^3251
        have hw : |(2080322289/5000000000 : ℝ)|=(2080322289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(225680947/500000000 : ℝ)|^4275 ≤ (35132345034257/100000000000000 : ℝ)^3251
        have hw : |(225680947/500000000 : ℝ)|=(225680947/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s7_4 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1033772603/5000000000 : ℝ)*x 0 + (5244403213/10000000000 : ℝ)*x 1 + (676678807/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033772603/5000000000 : ℝ)^4275 ≤ (1258453086033/10000000000000 : ℝ)^3251 := by
    have hnat : (1033772603 : ℕ)^4275*10000000000000^3251 ≤ 1258453086033^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033772603 5000000000 1258453086033 10000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244403213/10000000000 : ℝ)^4275 ≤ (8559254471021/20000000000000 : ℝ)^3251 := by
    have hnat : (5244403213 : ℕ)^4275*20000000000000^3251 ≤ 8559254471021^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244403213 10000000000 8559254471021 20000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676678807/1250000000 : ℝ)^4275 ≤ (1115479919219/2500000000000 : ℝ)^3251 := by
    have hnat : (676678807 : ℕ)^4275*2500000000000^3251 ≤ 1115479919219^3251*1250000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676678807 1250000000 1115479919219 2500000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1033772603/5000000000 : ℝ), (5244403213/10000000000 : ℝ), (676678807/1250000000 : ℝ)] ![(1258453086033/10000000000000 : ℝ), (8559254471021/20000000000000 : ℝ), (1115479919219/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1033772603/5000000000 : ℝ)|^4275 ≤ (1258453086033/10000000000000 : ℝ)^3251
        have hw : |(-1033772603/5000000000 : ℝ)|=(1033772603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244403213/10000000000 : ℝ)|^4275 ≤ (8559254471021/20000000000000 : ℝ)^3251
        have hw : |(5244403213/10000000000 : ℝ)|=(5244403213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676678807/1250000000 : ℝ)|^4275 ≤ (1115479919219/2500000000000 : ℝ)^3251
        have hw : |(676678807/1250000000 : ℝ)|=(676678807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s7_5 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652859627/5000000000 : ℝ)*x 0 + (-992330183/5000000000 : ℝ)*x 1 + (676678807/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652859627/5000000000 : ℝ)^4275 ≤ (43455446168227/100000000000000 : ℝ)^3251 := by
    have hnat : (2652859627 : ℕ)^4275*100000000000000^3251 ≤ 43455446168227^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652859627 5000000000 43455446168227 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (992330183/5000000000 : ℝ)^4275 ≤ (11925357048609/100000000000000 : ℝ)^3251 := by
    have hnat : (992330183 : ℕ)^4275*100000000000000^3251 ≤ 11925357048609^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992330183 5000000000 11925357048609 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676678807/1250000000 : ℝ)^4275 ≤ (1115479919219/2500000000000 : ℝ)^3251 := by
    have hnat : (676678807 : ℕ)^4275*2500000000000^3251 ≤ 1115479919219^3251*1250000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676678807 1250000000 1115479919219 2500000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652859627/5000000000 : ℝ), (-992330183/5000000000 : ℝ), (676678807/1250000000 : ℝ)] ![(43455446168227/100000000000000 : ℝ), (11925357048609/100000000000000 : ℝ), (1115479919219/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652859627/5000000000 : ℝ)|^4275 ≤ (43455446168227/100000000000000 : ℝ)^3251
        have hw : |(2652859627/5000000000 : ℝ)|=(2652859627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-992330183/5000000000 : ℝ)|^4275 ≤ (11925357048609/100000000000000 : ℝ)^3251
        have hw : |(-992330183/5000000000 : ℝ)|=(992330183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676678807/1250000000 : ℝ)|^4275 ≤ (1115479919219/2500000000000 : ℝ)^3251
        have hw : |(676678807/1250000000 : ℝ)|=(676678807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s7_6 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305719257/10000000000 : ℝ)*x 0 + (1353357613/2500000000 : ℝ)*x 1 + (-1984660367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305719257/10000000000 : ℝ)^4275 ≤ (21727723100269/50000000000000 : ℝ)^3251 := by
    have hnat : (5305719257 : ℕ)^4275*50000000000000^3251 ≤ 21727723100269^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305719257 10000000000 21727723100269 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353357613/2500000000 : ℝ)^4275 ≤ (22309598362703/50000000000000 : ℝ)^3251 := by
    have hnat : (1353357613 : ℕ)^4275*50000000000000^3251 ≤ 22309598362703^3251*2500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353357613 2500000000 22309598362703 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1984660367/10000000000 : ℝ)^4275 ≤ (11925357056511/100000000000000 : ℝ)^3251 := by
    have hnat : (1984660367 : ℕ)^4275*100000000000000^3251 ≤ 11925357056511^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984660367 10000000000 11925357056511 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305719257/10000000000 : ℝ), (1353357613/2500000000 : ℝ), (-1984660367/10000000000 : ℝ)] ![(21727723100269/50000000000000 : ℝ), (22309598362703/50000000000000 : ℝ), (11925357056511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305719257/10000000000 : ℝ)|^4275 ≤ (21727723100269/50000000000000 : ℝ)^3251
        have hw : |(5305719257/10000000000 : ℝ)|=(5305719257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353357613/2500000000 : ℝ)|^4275 ≤ (22309598362703/50000000000000 : ℝ)^3251
        have hw : |(1353357613/2500000000 : ℝ)|=(1353357613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1984660367/10000000000 : ℝ)|^4275 ≤ (11925357056511/100000000000000 : ℝ)^3251
        have hw : |(-1984660367/10000000000 : ℝ)|=(1984660367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s7_7 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4333757617/10000000000 : ℝ)*x 0 + (4512357883/10000000000 : ℝ)*x 1 + (4161911289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4333757617/10000000000 : ℝ)^4275 ≤ (133212268619/400000000000 : ℝ)^3251 := by
    have hnat : (4333757617 : ℕ)^4275*400000000000^3251 ≤ 133212268619^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4333757617 10000000000 133212268619 400000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4512357883/10000000000 : ℝ)^4275 ≤ (35119438281111/100000000000000 : ℝ)^3251 := by
    have hnat : (4512357883 : ℕ)^4275*100000000000000^3251 ≤ 35119438281111^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512357883 10000000000 35119438281111 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4161911289/10000000000 : ℝ)^4275 ≤ (3157749454517/10000000000000 : ℝ)^3251 := by
    have hnat : (4161911289 : ℕ)^4275*10000000000000^3251 ≤ 3157749454517^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4161911289 10000000000 3157749454517 10000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4333757617/10000000000 : ℝ), (4512357883/10000000000 : ℝ), (4161911289/10000000000 : ℝ)] ![(133212268619/400000000000 : ℝ), (35119438281111/100000000000000 : ℝ), (3157749454517/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4333757617/10000000000 : ℝ)|^4275 ≤ (133212268619/400000000000 : ℝ)^3251
        have hw : |(4333757617/10000000000 : ℝ)|=(4333757617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4512357883/10000000000 : ℝ)|^4275 ≤ (35119438281111/100000000000000 : ℝ)^3251
        have hw : |(4512357883/10000000000 : ℝ)|=(4512357883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4161911289/10000000000 : ℝ)|^4275 ≤ (3157749454517/10000000000000 : ℝ)^3251
        have hw : |(4161911289/10000000000 : ℝ)|=(4161911289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1315_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1469/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11083/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2217/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (459/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1469/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11083/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1469/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11083/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1469/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11083/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1469/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11083/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1469/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11083/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1469/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11083/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11083/100000 : ℝ) ^ (2137/512 : ℝ) ≤ (10293519899596983/100000000000000000000 : ℝ) := by
    have hpowers : (11083/100000 : ℝ)^2137 ≤ (10293519899596983/100000000000000000000 : ℝ)^512 := by
      have hnat : (11083 : ℕ)^2137*100000000000000000000^512 ≤ 10293519899596983^512*100000^2137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11083 100000 10293519899596983 100000000000000000000 2137 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11083/100000 : ℝ)) (X := (10293519899596983/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1469/10000 : ℝ) ^ (2137/512 : ℝ) ≤ (33365077945239131/100000000000000000000 : ℝ) := by
    have hpowers : (1469/10000 : ℝ)^2137 ≤ (33365077945239131/100000000000000000000 : ℝ)^512 := by
      have hnat : (1469 : ℕ)^2137*100000000000000000000^512 ≤ 33365077945239131^512*10000^2137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1469 10000 33365077945239131 100000000000000000000 2137 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1469/10000 : ℝ)) (X := (33365077945239131/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010293519899596983/50000000000000000000 : ℝ) ≤ (10000493202594001/10000000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (50010293519899596983/50000000000000000000 : ℝ)^512 ≤ (10000493202594001/10000000000000000 : ℝ)^2137 := by
      have hnat : (50010293519899596983 : ℕ)^512*10000000000000000^2137 ≤ 10000493202594001^2137*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010293519899596983 50000000000000000000 10000493202594001 10000000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000493202594001/10000000000000000 : ℝ)) (X := (50010293519899596983/50000000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021829298922418057/50000000000000000000 : ℝ) ≤ (2500261458733991/2500000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (50021829298922418057/50000000000000000000 : ℝ)^512 ≤ (2500261458733991/2500000000000000 : ℝ)^2137 := by
      have hnat : (50021829298922418057 : ℕ)^512*2500000000000000^2137 ≤ 2500261458733991^2137*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021829298922418057 50000000000000000000 2500261458733991 2500000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500261458733991/2500000000000000 : ℝ)) (X := (50021829298922418057/50000000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033365077945239131/50000000000000000000 : ℝ) ≤ (10001598467277927/10000000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (50033365077945239131/50000000000000000000 : ℝ)^512 ≤ (10001598467277927/10000000000000000 : ℝ)^2137 := by
      have hnat : (50033365077945239131 : ℕ)^512*10000000000000000^2137 ≤ 10001598467277927^2137*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033365077945239131 50000000000000000000 10001598467277927 10000000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001598467277927/10000000000000000 : ℝ)) (X := (50033365077945239131/50000000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10293519899596983/100000000000000000000 : ℝ) ≤ ((36059529333264609749/36070000000000000000 : ℝ)+2*(552632341963/360700000000000 : ℝ)*(11083/100000 : ℝ))^(2137/512 : ℝ) := by
    rw [show (36059529333264609749/36070000000000000000 : ℝ)+2*(552632341963/360700000000000 : ℝ)*(11083/100000 : ℝ)=(10000493202594001/10000000000000000 : ℝ) by norm_num, show 1+2*(10293519899596983/100000000000000000000 : ℝ)=(50010293519899596983/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33365077945239131/100000000000000000000 : ℝ)+(10293519899596983/100000000000000000000 : ℝ) ≤ ((36059529333264609749/36070000000000000000 : ℝ)+(552632341963/360700000000000 : ℝ)*((1469/10000 : ℝ)+(11083/100000 : ℝ)))^(2137/512 : ℝ) := by
    rw [show (36059529333264609749/36070000000000000000 : ℝ)+(552632341963/360700000000000 : ℝ)*((1469/10000 : ℝ)+(11083/100000 : ℝ))=(2500261458733991/2500000000000000 : ℝ) by norm_num, show 1+(33365077945239131/100000000000000000000 : ℝ)+(10293519899596983/100000000000000000000 : ℝ)=(50021829298922418057/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33365077945239131/100000000000000000000 : ℝ) ≤ ((36059529333264609749/36070000000000000000 : ℝ)+2*(552632341963/360700000000000 : ℝ)*(1469/10000 : ℝ))^(2137/512 : ℝ) := by
    rw [show (36059529333264609749/36070000000000000000 : ℝ)+2*(552632341963/360700000000000 : ℝ)*(1469/10000 : ℝ)=(10001598467277927/10000000000000000 : ℝ) by norm_num, show 1+2*(33365077945239131/100000000000000000000 : ℝ)=(50033365077945239131/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36059529333264609749/36070000000000000000 : ℝ)*(X 1 0+X 2 0)+(552632341963/360700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (11083/100000 : ℝ)) (hi := (1469/10000 : ℝ)) (c := (36059529333264609749/36070000000000000000 : ℝ)) (alpha := (552632341963/360700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36059529333264609749/36070000000000000000 : ℝ)*(X 0 1+X 2 1)+(552632341963/360700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (11083/100000 : ℝ)) (hi := (1469/10000 : ℝ)) (c := (36059529333264609749/36070000000000000000 : ℝ)) (alpha := (552632341963/360700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36059529333264609749/36070000000000000000 : ℝ)*(X 0 2+X 1 2)+(552632341963/360700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (11083/100000 : ℝ)) (hi := (1469/10000 : ℝ)) (c := (36059529333264609749/36070000000000000000 : ℝ)) (alpha := (552632341963/360700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2067532533/10000000000 : ℝ)*X 0 0+(1082808267/2000000000 : ℝ)*X 0 1+(524379563/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349431751/10000000000 : ℝ)*X 1 0+(-2154294147/10000000000 : ℝ)*X 1 1+(1310948893/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349430811/10000000000 : ℝ)*X 2 0+(5243795137/10000000000 : ℝ)*X 2 1+(-86171839/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((433373097/1000000000 : ℝ)*X 0 0+(2080322289/5000000000 : ℝ)*X 0 1+(225680947/500000000 : ℝ)*X 0 2+(433373097/1000000000 : ℝ)*X 1 0+(2080322289/5000000000 : ℝ)*X 1 1+(225680947/500000000 : ℝ)*X 1 2+(433373097/1000000000 : ℝ)*X 2 0+(2080322289/5000000000 : ℝ)*X 2 1+(225680947/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1033772603/5000000000 : ℝ)*X 0 0+(5244403213/10000000000 : ℝ)*X 0 1+(676678807/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652859627/5000000000 : ℝ)*X 1 0+(-992330183/5000000000 : ℝ)*X 1 1+(676678807/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305719257/10000000000 : ℝ)*X 2 0+(1353357613/2500000000 : ℝ)*X 2 1+(-1984660367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4333757617/10000000000 : ℝ)*X 0 0+(4512357883/10000000000 : ℝ)*X 0 1+(4161911289/10000000000 : ℝ)*X 0 2+(4333757617/10000000000 : ℝ)*X 1 0+(4512357883/10000000000 : ℝ)*X 1 1+(4161911289/10000000000 : ℝ)*X 1 2+(4333757617/10000000000 : ℝ)*X 2 0+(4512357883/10000000000 : ℝ)*X 2 1+(4161911289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13192953244954886951787/2254375000000000000000000000 : ℝ) := by norm_num
    linear_combination (1933574971/100000000000000 : ℝ)*(base19) + (61120001/12500000000000 : ℝ)*(base23) + (6579777/10000000000000 : ℝ)*(upper2) + (32079749/25000000000000 : ℝ)*(lower5) + (2176780686928763/50000000000000 : ℝ)*(major0) + (2176780686928763/50000000000000 : ℝ)*(major1) + (2176780686928763/50000000000000 : ℝ)*(major2) + (2936966300972091/50000000000000 : ℝ)*(sp0) + (5873982873372949/100000000000000 : ℝ)*(sp1) + (2936959395326983/50000000000000 : ℝ)*(sp2) + (566620856863283/20000000000000 : ℝ)*(sp3) + (26102501869/50000000000000 : ℝ)*(sp4) + (13105466789/20000000000000 : ℝ)*(sp6) + (1673068943/5000000000000 : ℝ)*(sp7) + (113325509827811/4000000000000 : ℝ)*(f.failure) + (5873984806947919/100000000000000 : ℝ)*(f.sum) + (16669791574611/9017500000000000000000000000 : ℝ)*base66 + (8317875199086210487/1803500000000000000000000000000000 : ℝ)*base67 + (8924568455062789513/1803500000000000000000000000000000 : ℝ)*base70 + (17573312294506289513/1803500000000000000000000000000000 : ℝ)*base72 + (119339756206393/18035000000000000000000000000 : ℝ)*base73 + (611956048697210487/1803500000000000000000000000000000 : ℝ)*base75 + (567969385678289513/1803500000000000000000000000000000 : ℝ)*base78 + (2471138635073210487/1803500000000000000000000000000000 : ℝ)*base79 + (30028015404413/18035000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (39973/80000000000000000000 : ℝ)*base89 + (39973/80000000000000000000 : ℝ)*base91 + (39973/80000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (468865449780411154705819959/225437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (369179043/100000000000000 : ℝ)*(base19) + (401789347/100000000000000 : ℝ)*(base23) + (126288869/100000000000000 : ℝ)*(lower1) + (43037661/100000000000000 : ℝ)*(upper3) + (6768191/50000000000000 : ℝ)*(lower4) + (11204297/25000000000000 : ℝ)*(upper5) + (548106038114097/12500000000000 : ℝ)*(major0) + (548106038114097/12500000000000 : ℝ)*(major1) + (548106038114097/12500000000000 : ℝ)*(major2) + (113865739/25000000000000 : ℝ)*(sp2) + (2958099204944611/50000000000000 : ℝ)*(sp4) + (5916198040710179/100000000000000 : ℝ)*(sp5) + (147904938815923/2500000000000 : ℝ)*(sp6) + (22292954145387/781250000000 : ℝ)*(sp7) + (22292954145387/781250000000 : ℝ)*(f.failure) + (2958099204944611/50000000000000 : ℝ)*(f.sum) + (2735720917497/4508750000000000000000000000 : ℝ)*base65 + (20353157256329381653/450875000000000000000000000000000 : ℝ)*base67 + (5392957031812368347/450875000000000000000000000000000 : ℝ)*base70 + (129747524902375881653/450875000000000000000000000000000 : ℝ)*base71 + (22075585024901/9017500000000000000000000000 : ℝ)*base74 + (30149090416305368347/450875000000000000000000000000000 : ℝ)*base76 + (3312279070002868347/450875000000000000000000000000000 : ℝ)*base78 + (12359204810080868347/450875000000000000000000000000000 : ℝ)*base80 + (26284551709613/4508750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (211341/15625000000000000000 : ℝ)*base89 + (211341/15625000000000000000 : ℝ)*base91 + (211341/15625000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1315_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1469/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11083/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2217/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (459/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1315_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1315_box_0 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1898099779/10000000000 : ℝ)*x 0 + (43128503/80000000 : ℝ)*x 1 + (5391062813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1898099779/10000000000 : ℝ)^4275 ≤ (11246152412607/100000000000000 : ℝ)^3251 := by
    have hnat : (1898099779 : ℕ)^4275*100000000000000^3251 ≤ 11246152412607^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1898099779 10000000000 11246152412607 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43128503/80000000 : ℝ)^4275 ≤ (22188462060013/50000000000000 : ℝ)^3251 := by
    have hnat : (43128503 : ℕ)^4275*50000000000000^3251 ≤ 22188462060013^3251*80000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43128503 80000000 22188462060013 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391062813/10000000000 : ℝ)^4275 ≤ (11094230862229/25000000000000 : ℝ)^3251 := by
    have hnat : (5391062813 : ℕ)^4275*25000000000000^3251 ≤ 11094230862229^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391062813 10000000000 11094230862229 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1898099779/10000000000 : ℝ), (43128503/80000000 : ℝ), (5391062813/10000000000 : ℝ)] ![(11246152412607/100000000000000 : ℝ), (22188462060013/50000000000000 : ℝ), (11094230862229/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1898099779/10000000000 : ℝ)|^4275 ≤ (11246152412607/100000000000000 : ℝ)^3251
        have hw : |(-1898099779/10000000000 : ℝ)|=(1898099779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43128503/80000000 : ℝ)|^4275 ≤ (22188462060013/50000000000000 : ℝ)^3251
        have hw : |(43128503/80000000 : ℝ)|=(43128503/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391062813/10000000000 : ℝ)|^4275 ≤ (11094230862229/25000000000000 : ℝ)^3251
        have hw : |(5391062813/10000000000 : ℝ)|=(5391062813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_box_1 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5284761637/10000000000 : ℝ)*x 0 + (-2043596637/10000000000 : ℝ)*x 1 + (336941457/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284761637/10000000000 : ℝ)^4275 ≤ (43229871410693/100000000000000 : ℝ)^3251 := by
    have hnat : (5284761637 : ℕ)^4275*100000000000000^3251 ≤ 43229871410693^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284761637 10000000000 43229871410693 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2043596637/10000000000 : ℝ)^4275 ≤ (12393199723729/100000000000000 : ℝ)^3251 := by
    have hnat : (2043596637 : ℕ)^4275*100000000000000^3251 ≤ 12393199723729^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043596637 10000000000 12393199723729 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336941457/625000000 : ℝ)^4275 ≤ (11094232212567/25000000000000 : ℝ)^3251 := by
    have hnat : (336941457 : ℕ)^4275*25000000000000^3251 ≤ 11094232212567^3251*625000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336941457 625000000 11094232212567 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284761637/10000000000 : ℝ), (-2043596637/10000000000 : ℝ), (336941457/625000000 : ℝ)] ![(43229871410693/100000000000000 : ℝ), (12393199723729/100000000000000 : ℝ), (11094232212567/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284761637/10000000000 : ℝ)|^4275 ≤ (43229871410693/100000000000000 : ℝ)^3251
        have hw : |(5284761637/10000000000 : ℝ)|=(5284761637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2043596637/10000000000 : ℝ)|^4275 ≤ (12393199723729/100000000000000 : ℝ)^3251
        have hw : |(-2043596637/10000000000 : ℝ)|=(2043596637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336941457/625000000 : ℝ)|^4275 ≤ (11094232212567/25000000000000 : ℝ)^3251
        have hw : |(336941457/625000000 : ℝ)|=(336941457/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_box_2 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642381001/5000000000 : ℝ)*x 0 + (336941443/625000000 : ℝ)*x 1 + (-63862389/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642381001/5000000000 : ℝ)^4275 ≤ (10807468834219/25000000000000 : ℝ)^3251 := by
    have hnat : (2642381001 : ℕ)^4275*25000000000000^3251 ≤ 10807468834219^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642381001 5000000000 10807468834219 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336941443/625000000 : ℝ)^4275 ≤ (44376926425613/100000000000000 : ℝ)^3251 := by
    have hnat : (336941443 : ℕ)^4275*100000000000000^3251 ≤ 44376926425613^3251*625000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336941443 625000000 44376926425613 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63862389/312500000 : ℝ)^4275 ≤ (2478639643307/20000000000000 : ℝ)^3251 := by
    have hnat : (63862389 : ℕ)^4275*20000000000000^3251 ≤ 2478639643307^3251*312500000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63862389 312500000 2478639643307 20000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642381001/5000000000 : ℝ), (336941443/625000000 : ℝ), (-63862389/312500000 : ℝ)] ![(10807468834219/25000000000000 : ℝ), (44376926425613/100000000000000 : ℝ), (2478639643307/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642381001/5000000000 : ℝ)|^4275 ≤ (10807468834219/25000000000000 : ℝ)^3251
        have hw : |(2642381001/5000000000 : ℝ)|=(2642381001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336941443/625000000 : ℝ)|^4275 ≤ (44376926425613/100000000000000 : ℝ)^3251
        have hw : |(336941443/625000000 : ℝ)|=(336941443/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-63862389/312500000 : ℝ)|^4275 ≤ (2478639643307/20000000000000 : ℝ)^3251
        have hw : |(-63862389/312500000 : ℝ)|=(63862389/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_box_3 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4482572961/10000000000 : ℝ)*x 0 + (4263262099/10000000000 : ℝ)*x 1 + (266453883/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4482572961/10000000000 : ℝ)^4275 ≤ (34814924290029/100000000000000 : ℝ)^3251 := by
    have hnat : (4482572961 : ℕ)^4275*100000000000000^3251 ≤ 34814924290029^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482572961 10000000000 34814924290029 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4263262099/10000000000 : ℝ)^4275 ≤ (16296268851853/50000000000000 : ℝ)^3251 := by
    have hnat : (4263262099 : ℕ)^4275*50000000000000^3251 ≤ 16296268851853^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4263262099 10000000000 16296268851853 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266453883/625000000 : ℝ)^4275 ≤ (32592537995243/100000000000000 : ℝ)^3251 := by
    have hnat : (266453883 : ℕ)^4275*100000000000000^3251 ≤ 32592537995243^3251*625000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266453883 625000000 32592537995243 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4482572961/10000000000 : ℝ), (4263262099/10000000000 : ℝ), (266453883/625000000 : ℝ)] ![(34814924290029/100000000000000 : ℝ), (16296268851853/50000000000000 : ℝ), (32592537995243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4482572961/10000000000 : ℝ)|^4275 ≤ (34814924290029/100000000000000 : ℝ)^3251
        have hw : |(4482572961/10000000000 : ℝ)|=(4482572961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4263262099/10000000000 : ℝ)|^4275 ≤ (16296268851853/50000000000000 : ℝ)^3251
        have hw : |(4263262099/10000000000 : ℝ)|=(4263262099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(266453883/625000000 : ℝ)|^4275 ≤ (32592537995243/100000000000000 : ℝ)^3251
        have hw : |(266453883/625000000 : ℝ)|=(266453883/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_box_4 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1119861301/5000000000 : ℝ)*x 0 + (26321461/50000000 : ℝ)*x 1 + (5264291491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1119861301/5000000000 : ℝ)^4275 ≤ (6990180857379/50000000000000 : ℝ)^3251 := by
    have hnat : (1119861301 : ℕ)^4275*50000000000000^3251 ≤ 6990180857379^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119861301 5000000000 6990180857379 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26321461/50000000 : ℝ)^4275 ≤ (21504911471217/50000000000000 : ℝ)^3251 := by
    have hnat : (26321461 : ℕ)^4275*50000000000000^3251 ≤ 21504911471217^3251*50000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26321461 50000000 21504911471217 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264291491/10000000000 : ℝ)^4275 ≤ (1720392613011/4000000000000 : ℝ)^3251 := by
    have hnat : (5264291491 : ℕ)^4275*4000000000000^3251 ≤ 1720392613011^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264291491 10000000000 1720392613011 4000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1119861301/5000000000 : ℝ), (26321461/50000000 : ℝ), (5264291491/10000000000 : ℝ)] ![(6990180857379/50000000000000 : ℝ), (21504911471217/50000000000000 : ℝ), (1720392613011/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1119861301/5000000000 : ℝ)|^4275 ≤ (6990180857379/50000000000000 : ℝ)^3251
        have hw : |(-1119861301/5000000000 : ℝ)|=(1119861301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(26321461/50000000 : ℝ)|^4275 ≤ (21504911471217/50000000000000 : ℝ)^3251
        have hw : |(26321461/50000000 : ℝ)|=(26321461/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264291491/10000000000 : ℝ)|^4275 ≤ (1720392613011/4000000000000 : ℝ)^3251
        have hw : |(5264291491/10000000000 : ℝ)|=(5264291491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_box_5 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537390683/1000000000 : ℝ)*x 0 + (-1047135603/5000000000 : ℝ)*x 1 + (16450909/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537390683/1000000000 : ℝ)^4275 ≤ (22095657085293/50000000000000 : ℝ)^3251 := by
    have hnat : (537390683 : ℕ)^4275*50000000000000^3251 ≤ 22095657085293^3251*1000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537390683 1000000000 22095657085293 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047135603/5000000000 : ℝ)^4275 ≤ (6399438525827/50000000000000 : ℝ)^3251 := by
    have hnat : (1047135603 : ℕ)^4275*50000000000000^3251 ≤ 6399438525827^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047135603 5000000000 6399438525827 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16450909/31250000 : ℝ)^4275 ≤ (43009808760981/100000000000000 : ℝ)^3251 := by
    have hnat : (16450909 : ℕ)^4275*100000000000000^3251 ≤ 43009808760981^3251*31250000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16450909 31250000 43009808760981 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537390683/1000000000 : ℝ), (-1047135603/5000000000 : ℝ), (16450909/31250000 : ℝ)] ![(22095657085293/50000000000000 : ℝ), (6399438525827/50000000000000 : ℝ), (43009808760981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537390683/1000000000 : ℝ)|^4275 ≤ (22095657085293/50000000000000 : ℝ)^3251
        have hw : |(537390683/1000000000 : ℝ)|=(537390683/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1047135603/5000000000 : ℝ)|^4275 ≤ (6399438525827/50000000000000 : ℝ)^3251
        have hw : |(-1047135603/5000000000 : ℝ)|=(1047135603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16450909/31250000 : ℝ)|^4275 ≤ (43009808760981/100000000000000 : ℝ)^3251
        have hw : |(16450909/31250000 : ℝ)|=(16450909/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_box_6 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83967277/156250000 : ℝ)*x 0 + (105285839/200000000 : ℝ)*x 1 + (-1047135629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83967277/156250000 : ℝ)^4275 ≤ (44191302254119/100000000000000 : ℝ)^3251 := by
    have hnat : (83967277 : ℕ)^4275*100000000000000^3251 ≤ 44191302254119^3251*156250000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83967277 156250000 44191302254119 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105285839/200000000 : ℝ)^4275 ≤ (43009820256553/100000000000000 : ℝ)^3251 := by
    have hnat : (105285839 : ℕ)^4275*100000000000000^3251 ≤ 43009820256553^3251*200000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105285839 200000000 43009820256553 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047135629/5000000000 : ℝ)^4275 ≤ (12798877469543/100000000000000 : ℝ)^3251 := by
    have hnat : (1047135629 : ℕ)^4275*100000000000000^3251 ≤ 12798877469543^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047135629 5000000000 12798877469543 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83967277/156250000 : ℝ), (105285839/200000000 : ℝ), (-1047135629/5000000000 : ℝ)] ![(44191302254119/100000000000000 : ℝ), (43009820256553/100000000000000 : ℝ), (12798877469543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83967277/156250000 : ℝ)|^4275 ≤ (44191302254119/100000000000000 : ℝ)^3251
        have hw : |(83967277/156250000 : ℝ)|=(83967277/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105285839/200000000 : ℝ)|^4275 ≤ (43009820256553/100000000000000 : ℝ)^3251
        have hw : |(105285839/200000000 : ℝ)|=(105285839/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1047135629/5000000000 : ℝ)|^4275 ≤ (12798877469543/100000000000000 : ℝ)^3251
        have hw : |(-1047135629/5000000000 : ℝ)|=(1047135629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_box_7 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16343771/39062500 : ℝ)*x 0 + (220624589/500000000 : ℝ)*x 1 + (4412490973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16343771/39062500 : ℝ)^4275 ≤ (15899056684237/50000000000000 : ℝ)^3251 := by
    have hnat : (16343771 : ℕ)^4275*50000000000000^3251 ≤ 15899056684237^3251*39062500^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16343771 39062500 15899056684237 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220624589/500000000 : ℝ)^4275 ≤ (34100947408621/100000000000000 : ℝ)^3251 := by
    have hnat : (220624589 : ℕ)^4275*100000000000000^3251 ≤ 34100947408621^3251*500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220624589 500000000 34100947408621 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4412490973/10000000000 : ℝ)^4275 ≤ (34100939207463/100000000000000 : ℝ)^3251 := by
    have hnat : (4412490973 : ℕ)^4275*100000000000000^3251 ≤ 34100939207463^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4412490973 10000000000 34100939207463 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16343771/39062500 : ℝ), (220624589/500000000 : ℝ), (4412490973/10000000000 : ℝ)] ![(15899056684237/50000000000000 : ℝ), (34100947408621/100000000000000 : ℝ), (34100939207463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16343771/39062500 : ℝ)|^4275 ≤ (15899056684237/50000000000000 : ℝ)^3251
        have hw : |(16343771/39062500 : ℝ)|=(16343771/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(220624589/500000000 : ℝ)|^4275 ≤ (34100947408621/100000000000000 : ℝ)^3251
        have hw : |(220624589/500000000 : ℝ)|=(220624589/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4412490973/10000000000 : ℝ)|^4275 ≤ (34100939207463/100000000000000 : ℝ)^3251
        have hw : |(4412490973/10000000000 : ℝ)|=(4412490973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_box_8 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2168055879/10000000000 : ℝ)*x 0 + (517714839/1000000000 : ℝ)*x 1 + (5405093537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168055879/10000000000 : ℝ)^4275 ≤ (13395099515159/100000000000000 : ℝ)^3251 := by
    have hnat : (2168055879 : ℕ)^4275*100000000000000^3251 ≤ 13395099515159^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168055879 10000000000 13395099515159 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517714839/1000000000 : ℝ)^4275 ≤ (210380206483/500000000000 : ℝ)^3251 := by
    have hnat : (517714839 : ℕ)^4275*500000000000^3251 ≤ 210380206483^3251*1000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517714839 1000000000 210380206483 500000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405093537/10000000000 : ℝ)^4275 ≤ (8905771834387/20000000000000 : ℝ)^3251 := by
    have hnat : (5405093537 : ℕ)^4275*20000000000000^3251 ≤ 8905771834387^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405093537 10000000000 8905771834387 20000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2168055879/10000000000 : ℝ), (517714839/1000000000 : ℝ), (5405093537/10000000000 : ℝ)] ![(13395099515159/100000000000000 : ℝ), (210380206483/500000000000 : ℝ), (8905771834387/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2168055879/10000000000 : ℝ)|^4275 ≤ (13395099515159/100000000000000 : ℝ)^3251
        have hw : |(-2168055879/10000000000 : ℝ)|=(2168055879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517714839/1000000000 : ℝ)|^4275 ≤ (210380206483/500000000000 : ℝ)^3251
        have hw : |(517714839/1000000000 : ℝ)|=(517714839/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405093537/10000000000 : ℝ)|^4275 ≤ (8905771834387/20000000000000 : ℝ)^3251
        have hw : |(5405093537/10000000000 : ℝ)|=(5405093537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_box_9 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1054978097/2000000000 : ℝ)*x 0 + (-1018926877/5000000000 : ℝ)*x 1 + (1351273289/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054978097/2000000000 : ℝ)^4275 ≤ (10780930493119/25000000000000 : ℝ)^3251 := by
    have hnat : (1054978097 : ℕ)^4275*25000000000000^3251 ≤ 10780930493119^3251*2000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054978097 2000000000 10780930493119 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1018926877/5000000000 : ℝ)^4275 ≤ (12347422967713/100000000000000 : ℝ)^3251 := by
    have hnat : (1018926877 : ℕ)^4275*100000000000000^3251 ≤ 12347422967713^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018926877 5000000000 12347422967713 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351273289/2500000000 : ℝ)^4275 ≤ (22264427522239/50000000000000 : ℝ)^3251 := by
    have hnat : (1351273289 : ℕ)^4275*50000000000000^3251 ≤ 22264427522239^3251*2500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351273289 2500000000 22264427522239 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054978097/2000000000 : ℝ), (-1018926877/5000000000 : ℝ), (1351273289/2500000000 : ℝ)] ![(10780930493119/25000000000000 : ℝ), (12347422967713/100000000000000 : ℝ), (22264427522239/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054978097/2000000000 : ℝ)|^4275 ≤ (10780930493119/25000000000000 : ℝ)^3251
        have hw : |(1054978097/2000000000 : ℝ)|=(1054978097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1018926877/5000000000 : ℝ)|^4275 ≤ (12347422967713/100000000000000 : ℝ)^3251
        have hw : |(-1018926877/5000000000 : ℝ)|=(1018926877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351273289/2500000000 : ℝ)|^4275 ≤ (22264427522239/50000000000000 : ℝ)^3251
        have hw : |(1351273289/2500000000 : ℝ)|=(1351273289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_box_10 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5274890161/10000000000 : ℝ)*x 0 + (675636677/1250000000 : ℝ)*x 1 + (-1018926919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274890161/10000000000 : ℝ)^4275 ≤ (5390464811171/12500000000000 : ℝ)^3251 := by
    have hnat : (5274890161 : ℕ)^4275*12500000000000^3251 ≤ 5390464811171^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274890161 10000000000 5390464811171 12500000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675636677/1250000000 : ℝ)^4275 ≤ (8905771572223/20000000000000 : ℝ)^3251 := by
    have hnat : (675636677 : ℕ)^4275*20000000000000^3251 ≤ 8905771572223^3251*1250000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675636677 1250000000 8905771572223 20000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1018926919/5000000000 : ℝ)^4275 ≤ (12347423636983/100000000000000 : ℝ)^3251 := by
    have hnat : (1018926919 : ℕ)^4275*100000000000000^3251 ≤ 12347423636983^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018926919 5000000000 12347423636983 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274890161/10000000000 : ℝ), (675636677/1250000000 : ℝ), (-1018926919/5000000000 : ℝ)] ![(5390464811171/12500000000000 : ℝ), (8905771572223/20000000000000 : ℝ), (12347423636983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274890161/10000000000 : ℝ)|^4275 ≤ (5390464811171/12500000000000 : ℝ)^3251
        have hw : |(5274890161/10000000000 : ℝ)|=(5274890161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675636677/1250000000 : ℝ)|^4275 ≤ (8905771572223/20000000000000 : ℝ)^3251
        have hw : |(675636677/1250000000 : ℝ)|=(675636677/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1018926919/5000000000 : ℝ)|^4275 ≤ (12347423636983/100000000000000 : ℝ)^3251
        have hw : |(-1018926919/5000000000 : ℝ)|=(1018926919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_box_11 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4515057363/10000000000 : ℝ)*x 0 + (132710377/312500000 : ℝ)*x 1 + (530841577/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4515057363/10000000000 : ℝ)^4275 ≤ (17573534245951/50000000000000 : ℝ)^3251 := by
    have hnat : (4515057363 : ℕ)^4275*50000000000000^3251 ≤ 17573534245951^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515057363 10000000000 17573534245951 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132710377/312500000 : ℝ)^4275 ≤ (4053307871837/12500000000000 : ℝ)^3251 := by
    have hnat : (132710377 : ℕ)^4275*12500000000000^3251 ≤ 4053307871837^3251*312500000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132710377 312500000 4053307871837 12500000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (530841577/1250000000 : ℝ)^4275 ≤ (32426468517161/100000000000000 : ℝ)^3251 := by
    have hnat : (530841577 : ℕ)^4275*100000000000000^3251 ≤ 32426468517161^3251*1250000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530841577 1250000000 32426468517161 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4515057363/10000000000 : ℝ), (132710377/312500000 : ℝ), (530841577/1250000000 : ℝ)] ![(17573534245951/50000000000000 : ℝ), (4053307871837/12500000000000 : ℝ), (32426468517161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4515057363/10000000000 : ℝ)|^4275 ≤ (17573534245951/50000000000000 : ℝ)^3251
        have hw : |(4515057363/10000000000 : ℝ)|=(4515057363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(132710377/312500000 : ℝ)|^4275 ≤ (4053307871837/12500000000000 : ℝ)^3251
        have hw : |(132710377/312500000 : ℝ)|=(132710377/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(530841577/1250000000 : ℝ)|^4275 ≤ (32426468517161/100000000000000 : ℝ)^3251
        have hw : |(530841577/1250000000 : ℝ)|=(530841577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_box_12 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-246269639/1250000000 : ℝ)*x 0 + (684492323/1250000000 : ℝ)*x 1 + (131331153/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (246269639/1250000000 : ℝ)^4275 ≤ (5905446533627/50000000000000 : ℝ)^3251 := by
    have hnat : (246269639 : ℕ)^4275*50000000000000^3251 ≤ 5905446533627^3251*1250000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246269639 1250000000 5905446533627 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (684492323/1250000000 : ℝ)^4275 ≤ (1132447964807/2500000000000 : ℝ)^3251 := by
    have hnat : (684492323 : ℕ)^4275*2500000000000^3251 ≤ 1132447964807^3251*1250000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684492323 1250000000 1132447964807 2500000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131331153/250000000 : ℝ)^4275 ≤ (2144559416839/5000000000000 : ℝ)^3251 := by
    have hnat : (131331153 : ℕ)^4275*5000000000000^3251 ≤ 2144559416839^3251*250000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131331153 250000000 2144559416839 5000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-246269639/1250000000 : ℝ), (684492323/1250000000 : ℝ), (131331153/250000000 : ℝ)] ![(5905446533627/50000000000000 : ℝ), (1132447964807/2500000000000 : ℝ), (2144559416839/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-246269639/1250000000 : ℝ)|^4275 ≤ (5905446533627/50000000000000 : ℝ)^3251
        have hw : |(-246269639/1250000000 : ℝ)|=(246269639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(684492323/1250000000 : ℝ)|^4275 ≤ (1132447964807/2500000000000 : ℝ)^3251
        have hw : |(684492323/1250000000 : ℝ)|=(684492323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131331153/250000000 : ℝ)|^4275 ≤ (2144559416839/5000000000000 : ℝ)^3251
        have hw : |(131331153/250000000 : ℝ)|=(131331153/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_box_13 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690835147/5000000000 : ℝ)*x 0 + (-2098581441/10000000000 : ℝ)*x 1 + (5253246257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690835147/5000000000 : ℝ)^4275 ≤ (44275283414747/100000000000000 : ℝ)^3251 := by
    have hnat : (2690835147 : ℕ)^4275*100000000000000^3251 ≤ 44275283414747^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690835147 5000000000 44275283414747 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2098581441/10000000000 : ℝ)^4275 ≤ (6416763385599/50000000000000 : ℝ)^3251 := by
    have hnat : (2098581441 : ℕ)^4275*50000000000000^3251 ≤ 6416763385599^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098581441 10000000000 6416763385599 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253246257/10000000000 : ℝ)^4275 ≤ (4289118980767/10000000000000 : ℝ)^3251 := by
    have hnat : (5253246257 : ℕ)^4275*10000000000000^3251 ≤ 4289118980767^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253246257 10000000000 4289118980767 10000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690835147/5000000000 : ℝ), (-2098581441/10000000000 : ℝ), (5253246257/10000000000 : ℝ)] ![(44275283414747/100000000000000 : ℝ), (6416763385599/50000000000000 : ℝ), (4289118980767/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690835147/5000000000 : ℝ)|^4275 ≤ (44275283414747/100000000000000 : ℝ)^3251
        have hw : |(2690835147/5000000000 : ℝ)|=(2690835147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2098581441/10000000000 : ℝ)|^4275 ≤ (6416763385599/50000000000000 : ℝ)^3251
        have hw : |(-2098581441/10000000000 : ℝ)|=(2098581441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253246257/10000000000 : ℝ)|^4275 ≤ (4289118980767/10000000000000 : ℝ)^3251
        have hw : |(5253246257/10000000000 : ℝ)|=(5253246257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_box_14 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5381670449/10000000000 : ℝ)*x 0 + (65665577/125000000 : ℝ)*x 1 + (-2098581361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381670449/10000000000 : ℝ)^4275 ≤ (110688212729/250000000000 : ℝ)^3251 := by
    have hnat : (5381670449 : ℕ)^4275*250000000000^3251 ≤ 110688212729^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381670449 10000000000 110688212729 250000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65665577/125000000 : ℝ)^4275 ≤ (42891188766237/100000000000000 : ℝ)^3251 := by
    have hnat : (65665577 : ℕ)^4275*100000000000000^3251 ≤ 42891188766237^3251*125000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65665577 125000000 42891188766237 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2098581361/10000000000 : ℝ)^4275 ≤ (102668209023/800000000000 : ℝ)^3251 := by
    have hnat : (2098581361 : ℕ)^4275*800000000000^3251 ≤ 102668209023^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098581361 10000000000 102668209023 800000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381670449/10000000000 : ℝ), (65665577/125000000 : ℝ), (-2098581361/10000000000 : ℝ)] ![(110688212729/250000000000 : ℝ), (42891188766237/100000000000000 : ℝ), (102668209023/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381670449/10000000000 : ℝ)|^4275 ≤ (110688212729/250000000000 : ℝ)^3251
        have hw : |(5381670449/10000000000 : ℝ)|=(5381670449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65665577/125000000 : ℝ)|^4275 ≤ (42891188766237/100000000000000 : ℝ)^3251
        have hw : |(65665577/125000000 : ℝ)|=(65665577/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2098581361/10000000000 : ℝ)|^4275 ≤ (102668209023/800000000000 : ℝ)^3251
        have hw : |(-2098581361/10000000000 : ℝ)|=(2098581361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_box_15 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039385949/2500000000 : ℝ)*x 0 + (110637091/250000000 : ℝ)*x 1 + (4425483217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039385949/2500000000 : ℝ)^4275 ≤ (31533926866769/100000000000000 : ℝ)^3251 := by
    have hnat : (1039385949 : ℕ)^4275*100000000000000^3251 ≤ 31533926866769^3251*2500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039385949 2500000000 31533926866769 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110637091/250000000 : ℝ)^4275 ≤ (17116519355039/50000000000000 : ℝ)^3251 := by
    have hnat : (110637091 : ℕ)^4275*50000000000000^3251 ≤ 17116519355039^3251*250000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110637091 250000000 17116519355039 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4425483217/10000000000 : ℝ)^4275 ≤ (34233034407347/100000000000000 : ℝ)^3251 := by
    have hnat : (4425483217 : ℕ)^4275*100000000000000^3251 ≤ 34233034407347^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4425483217 10000000000 34233034407347 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039385949/2500000000 : ℝ), (110637091/250000000 : ℝ), (4425483217/10000000000 : ℝ)] ![(31533926866769/100000000000000 : ℝ), (17116519355039/50000000000000 : ℝ), (34233034407347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039385949/2500000000 : ℝ)|^4275 ≤ (31533926866769/100000000000000 : ℝ)^3251
        have hw : |(1039385949/2500000000 : ℝ)|=(1039385949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(110637091/250000000 : ℝ)|^4275 ≤ (17116519355039/50000000000000 : ℝ)^3251
        have hw : |(110637091/250000000 : ℝ)|=(110637091/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4425483217/10000000000 : ℝ)|^4275 ≤ (34233034407347/100000000000000 : ℝ)^3251
        have hw : |(4425483217/10000000000 : ℝ)|=(4425483217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1315_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (459/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2217/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31423/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58889/100000 : ℝ) ∧ (15959/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42123/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (459/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2217/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (459/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2217/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (459/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2217/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (459/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2217/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (459/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2217/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (459/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2217/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2217/20000 : ℝ) ^ (2137/512 : ℝ) ≤ (5150637572089747/50000000000000000000 : ℝ) := by
    have hpowers : (2217/20000 : ℝ)^2137 ≤ (5150637572089747/50000000000000000000 : ℝ)^512 := by
      have hnat : (2217 : ℕ)^2137*50000000000000000000^512 ≤ 5150637572089747^512*20000^2137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2217 20000 5150637572089747 50000000000000000000 2137 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2217/20000 : ℝ)) (X := (5150637572089747/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hpowhi : (459/3125 : ℝ) ^ (2137/512 : ℝ) ≤ (33346122190843533/100000000000000000000 : ℝ) := by
    have hpowers : (459/3125 : ℝ)^2137 ≤ (33346122190843533/100000000000000000000 : ℝ)^512 := by
      have hnat : (459 : ℕ)^2137*100000000000000000000^512 ≤ 33346122190843533^512*3125^2137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        459 3125 33346122190843533 100000000000000000000 2137 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (459/3125 : ℝ)) (X := (33346122190843533/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005150637572089747/25000000000000000000 : ℝ) ≤ (2000098714829769/2000000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (25005150637572089747/25000000000000000000 : ℝ)^512 ≤ (2000098714829769/2000000000000000 : ℝ)^2137 := by
      have hnat : (25005150637572089747 : ℕ)^512*2000000000000000^2137 ≤ 2000098714829769^2137*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005150637572089747 25000000000000000000 2000098714829769 2000000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000098714829769/2000000000000000 : ℝ)) (X := (25005150637572089747/25000000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043647397335023027/100000000000000000000 : ℝ) ≤ (5000522783337/5000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (100043647397335023027/100000000000000000000 : ℝ)^512 ≤ (5000522783337/5000000000000 : ℝ)^2137 := by
      have hnat : (100043647397335023027 : ℕ)^512*5000000000000^2137 ≤ 5000522783337^2137*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043647397335023027 100000000000000000000 5000522783337 5000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000522783337/5000000000000 : ℝ)) (X := (100043647397335023027/100000000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033346122190843533/50000000000000000000 : ℝ) ≤ (2000319511839831/2000000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (50033346122190843533/50000000000000000000 : ℝ)^512 ≤ (2000319511839831/2000000000000000 : ℝ)^2137 := by
      have hnat : (50033346122190843533 : ℕ)^512*2000000000000000^2137 ≤ 2000319511839831^2137*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033346122190843533 50000000000000000000 2000319511839831 2000000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000319511839831/2000000000000000 : ℝ)) (X := (50033346122190843533/50000000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5150637572089747/50000000000000000000 : ℝ) ≤ ((2401302711558373479/2402000000000000000 : ℝ)+2*(36799501677/24020000000000 : ℝ)*(2217/20000 : ℝ))^(2137/512 : ℝ) := by
    rw [show (2401302711558373479/2402000000000000000 : ℝ)+2*(36799501677/24020000000000 : ℝ)*(2217/20000 : ℝ)=(2000098714829769/2000000000000000 : ℝ) by norm_num, show 1+2*(5150637572089747/50000000000000000000 : ℝ)=(25005150637572089747/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33346122190843533/100000000000000000000 : ℝ)+(5150637572089747/50000000000000000000 : ℝ) ≤ ((2401302711558373479/2402000000000000000 : ℝ)+(36799501677/24020000000000 : ℝ)*((459/3125 : ℝ)+(2217/20000 : ℝ)))^(2137/512 : ℝ) := by
    rw [show (2401302711558373479/2402000000000000000 : ℝ)+(36799501677/24020000000000 : ℝ)*((459/3125 : ℝ)+(2217/20000 : ℝ))=(5000522783337/5000000000000 : ℝ) by norm_num, show 1+(33346122190843533/100000000000000000000 : ℝ)+(5150637572089747/50000000000000000000 : ℝ)=(100043647397335023027/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33346122190843533/100000000000000000000 : ℝ) ≤ ((2401302711558373479/2402000000000000000 : ℝ)+2*(36799501677/24020000000000 : ℝ)*(459/3125 : ℝ))^(2137/512 : ℝ) := by
    rw [show (2401302711558373479/2402000000000000000 : ℝ)+2*(36799501677/24020000000000 : ℝ)*(459/3125 : ℝ)=(2000319511839831/2000000000000000 : ℝ) by norm_num, show 1+2*(33346122190843533/100000000000000000000 : ℝ)=(50033346122190843533/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2401302711558373479/2402000000000000000 : ℝ)*(X 1 0+X 2 0)+(36799501677/24020000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (2217/20000 : ℝ)) (hi := (459/3125 : ℝ)) (c := (2401302711558373479/2402000000000000000 : ℝ)) (alpha := (36799501677/24020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2401302711558373479/2402000000000000000 : ℝ)*(X 0 1+X 2 1)+(36799501677/24020000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (2217/20000 : ℝ)) (hi := (459/3125 : ℝ)) (c := (2401302711558373479/2402000000000000000 : ℝ)) (alpha := (36799501677/24020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2401302711558373479/2402000000000000000 : ℝ)*(X 0 2+X 1 2)+(36799501677/24020000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (2217/20000 : ℝ)) (hi := (459/3125 : ℝ)) (c := (2401302711558373479/2402000000000000000 : ℝ)) (alpha := (36799501677/24020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1898099779/10000000000 : ℝ)*X 0 0+(43128503/80000000 : ℝ)*X 0 1+(5391062813/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5284761637/10000000000 : ℝ)*X 1 0+(-2043596637/10000000000 : ℝ)*X 1 1+(336941457/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642381001/5000000000 : ℝ)*X 2 0+(336941443/625000000 : ℝ)*X 2 1+(-63862389/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4482572961/10000000000 : ℝ)*X 0 0+(4263262099/10000000000 : ℝ)*X 0 1+(266453883/625000000 : ℝ)*X 0 2+(4482572961/10000000000 : ℝ)*X 1 0+(4263262099/10000000000 : ℝ)*X 1 1+(266453883/625000000 : ℝ)*X 1 2+(4482572961/10000000000 : ℝ)*X 2 0+(4263262099/10000000000 : ℝ)*X 2 1+(266453883/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1119861301/5000000000 : ℝ)*X 0 0+(26321461/50000000 : ℝ)*X 0 1+(5264291491/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((537390683/1000000000 : ℝ)*X 1 0+(-1047135603/5000000000 : ℝ)*X 1 1+(16450909/31250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((83967277/156250000 : ℝ)*X 2 0+(105285839/200000000 : ℝ)*X 2 1+(-1047135629/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((16343771/39062500 : ℝ)*X 0 0+(220624589/500000000 : ℝ)*X 0 1+(4412490973/10000000000 : ℝ)*X 0 2+(16343771/39062500 : ℝ)*X 1 0+(220624589/500000000 : ℝ)*X 1 1+(4412490973/10000000000 : ℝ)*X 1 2+(16343771/39062500 : ℝ)*X 2 0+(220624589/500000000 : ℝ)*X 2 1+(4412490973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2168055879/10000000000 : ℝ)*X 0 0+(517714839/1000000000 : ℝ)*X 0 1+(5405093537/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1054978097/2000000000 : ℝ)*X 1 0+(-1018926877/5000000000 : ℝ)*X 1 1+(1351273289/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5274890161/10000000000 : ℝ)*X 2 0+(675636677/1250000000 : ℝ)*X 2 1+(-1018926919/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4515057363/10000000000 : ℝ)*X 0 0+(132710377/312500000 : ℝ)*X 0 1+(530841577/1250000000 : ℝ)*X 0 2+(4515057363/10000000000 : ℝ)*X 1 0+(132710377/312500000 : ℝ)*X 1 1+(530841577/1250000000 : ℝ)*X 1 2+(4515057363/10000000000 : ℝ)*X 2 0+(132710377/312500000 : ℝ)*X 2 1+(530841577/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-246269639/1250000000 : ℝ)*X 0 0+(684492323/1250000000 : ℝ)*X 0 1+(131331153/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2690835147/5000000000 : ℝ)*X 1 0+(-2098581441/10000000000 : ℝ)*X 1 1+(5253246257/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5381670449/10000000000 : ℝ)*X 2 0+(65665577/125000000 : ℝ)*X 2 1+(-2098581361/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1039385949/2500000000 : ℝ)*X 0 0+(110637091/250000000 : ℝ)*X 0 1+(4425483217/10000000000 : ℝ)*X 0 2+(1039385949/2500000000 : ℝ)*X 1 0+(110637091/250000000 : ℝ)*X 1 1+(4425483217/10000000000 : ℝ)*X 1 2+(1039385949/2500000000 : ℝ)*X 2 0+(110637091/250000000 : ℝ)*X 2 1+(4425483217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31423/50000 : ℝ) ≤ (-377373574579927248288763383/600500000000000000000000000 : ℝ) := by norm_num
    linear_combination (84731/4000000000000 : ℝ)*(upper1) + (166867337/100000000000000 : ℝ)*(upper3) + (17691467/25000000000000 : ℝ)*(lower4) + (103763473/50000000000000 : ℝ)*(lower5) + (578046753235251/20000000000000 : ℝ)*(major0) + (578046753235251/20000000000000 : ℝ)*(major1) + (578046753235251/20000000000000 : ℝ)*(major2) + (31891406617/100000000000000 : ℝ)*(sp1) + (2793901103/100000000000000 : ℝ)*(sp3) + (1960278678781961/50000000000000 : ℝ)*(sp4) + (490065683269663/12500000000000 : ℝ)*(sp5) + (3920458212992613/100000000000000 : ℝ)*(sp6) + (1880855123023473/100000000000000 : ℝ)*(sp7) + (24786142827/25000000000000 : ℝ)*(sp14) + (58776809903893/3125000000000 : ℝ)*(f.failure) + (1960278678781961/50000000000000 : ℝ)*(f.sum) + (428801129181/150125000000000000000000000 : ℝ)*base65 + (192515747798471771/48040000000000000000000000000000 : ℝ)*base68 + (329440361714408229/48040000000000000000000000000000 : ℝ)*base69 + (82395571351808229/48040000000000000000000000000000 : ℝ)*base71 + (379497087351/1201000000000000000000000000 : ℝ)*base73 + (41097780845528229/48040000000000000000000000000000 : ℝ)*base75 + (145781275632471771/48040000000000000000000000000000 : ℝ)*base78 + (242310852207671771/48040000000000000000000000000000 : ℝ)*base80 + (1655778666341/300250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (450699/62500000000000000000 : ℝ)*base89 + (450699/62500000000000000000 : ℝ)*base91 + (450699/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58889/100000 : ℝ) ≤ (17682181427093645540115065345247/30025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46900769/100000000000000 : ℝ)*(upper0) + (31462099/100000000000000 : ℝ)*(lower1) + (14896537/10000000000000 : ℝ)*(upper4) + (1479011586185869/50000000000000 : ℝ)*(major0) + (1479011586185869/50000000000000 : ℝ)*(major1) + (1479011586185869/50000000000000 : ℝ)*(major2) + (124107539652451/3125000000000 : ℝ)*(sp0) + (1985715056101023/50000000000000 : ℝ)*(sp1) + (1985714831205881/50000000000000 : ℝ)*(sp2) + (384994055047019/20000000000000 : ℝ)*(sp3) + (6475939139/50000000000000 : ℝ)*(sp5) + (13401668563/100000000000000 : ℝ)*(sp6) + (38998963/1562500000000 : ℝ)*(sp7) + (897600947/50000000000000 : ℝ)*(sp8) + (1924972771168727/100000000000000 : ℝ)*(f.failure) + (158857722563213/4000000000000 : ℝ)*(f.sum) + (1783083053547/1201000000000000000000000000 : ℝ)*base66 + (606854368957031749/120100000000000000000000000000000 : ℝ)*base68 + (683089005006468251/120100000000000000000000000000000 : ℝ)*base69 + (852462962968568251/120100000000000000000000000000000 : ℝ)*base71 + (21282654923831/1201000000000000000000000000 : ℝ)*base73 + (968334587976668251/120100000000000000000000000000000 : ℝ)*base75 + (228885946613968251/120100000000000000000000000000000 : ℝ)*base77 + (2869590706898368251/120100000000000000000000000000000 : ℝ)*base79 + (67185399463/15012500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (4018961/2000000000000000000000 : ℝ)*base89 + (4018961/2000000000000000000000 : ℝ)*base91 + (4018961/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (15959/20000 : ℝ) ≤ (119795798068352787875269239/150125000000000000000000000 : ℝ) := by norm_num
    linear_combination (62881401/100000000000000 : ℝ)*(upper0) + (50466663/50000000000000 : ℝ)*(upper2) + (10641001/100000000000000 : ℝ)*(lower4) + (3271211009340467/100000000000000 : ℝ)*(major0) + (3271211009340467/100000000000000 : ℝ)*(major1) + (3271211009340467/100000000000000 : ℝ)*(major2) + (12665594357/10000000000000 : ℝ)*(sp1) + (157609649249/100000000000000 : ℝ)*(sp2) + (82123054467/100000000000000 : ℝ)*(sp3) + (4898259763/20000000000000 : ℝ)*(sp4) + (2193507249630481/50000000000000 : ℝ)*(sp8) + (274182020913513/6250000000000 : ℝ)*(sp9) + (68545021576727/1562500000000 : ℝ)*(sp10) + (532175445635619/25000000000000 : ℝ)*(sp11) + (2128783905596943/100000000000000 : ℝ)*(f.failure) + (2193519495279889/50000000000000 : ℝ)*(f.sum) + (15568743464647/300250000000000000000000000 : ℝ)*base66 + (185700212714774693/240200000000000000000000000000000 : ℝ)*base67 + (2248317339379974693/240200000000000000000000000000000 : ℝ)*base69 + (11516971493938825307/240200000000000000000000000000000 : ℝ)*base72 + (381883993077/150125000000000000000000000 : ℝ)*base74 + (1673929354314174693/240200000000000000000000000000000 : ℝ)*base75 + (1561341211886025307/240200000000000000000000000000000 : ℝ)*base78 + (1401255640561225307/240200000000000000000000000000000 : ℝ)*base80 + (2654143557017/1201000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (9581849/2000000000000000000000 : ℝ)*base89 + (9581849/2000000000000000000000 : ℝ)*base91 + (9581849/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-42123/50000 : ℝ) ≤ (-1011765791040128484968738079/1201000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48848273/100000000000000 : ℝ)*(lower0) + (73501189/100000000000000 : ℝ)*(lower2) + (2321919/6250000000000 : ℝ)*(upper3) + (3589351/12500000000000 : ℝ)*(upper5) + (826840555595283/25000000000000 : ℝ)*(major0) + (826840555595283/25000000000000 : ℝ)*(major1) + (826840555595283/25000000000000 : ℝ)*(major2) + (2170655851/100000000000000 : ℝ)*(sp0) + (1004320717/20000000000000 : ℝ)*(sp5) + (3261128459/12500000000000 : ℝ)*(sp7) + (1122623422986981/25000000000000 : ℝ)*(sp12) + (1122622710250047/25000000000000 : ℝ)*(sp13) + (2245247931301887/50000000000000 : ℝ)*(sp14) + (215228369743389/10000000000000 : ℝ)*(sp15) + (1076154893230781/50000000000000 : ℝ)*(f.failure) + (2245247931301887/50000000000000 : ℝ)*(f.sum) + (2606135294331/1201000000000000000000000000 : ℝ)*base66 + (55678113366250443/60050000000000000000000000000000 : ℝ)*base68 + (262401783332650443/60050000000000000000000000000000 : ℝ)*base70 + (398024561407099557/60050000000000000000000000000000 : ℝ)*base71 + (1961915318311/600500000000000000000000000 : ℝ)*base73 + (332328770418699557/60050000000000000000000000000000 : ℝ)*base75 + (366992844518100443/60050000000000000000000000000000 : ℝ)*base78 + (3938302836863799557/60050000000000000000000000000000 : ℝ)*base79 + (39919410161/9382812500000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (4474683/1000000000000000000000 : ℝ)*base89 + (4474683/1000000000000000000000 : ℝ)*base91 + (4474683/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1315_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (459/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2217/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31423/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58889/100000 : ℝ) else (15959/20000 : ℝ) ≤ X j i ∧ X j i ≤ (42123/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1315_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1315_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (147/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5537/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31423/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58889/100000 : ℝ) else (15959/20000 : ℝ) ≤ X j i ∧ X j i ≤ (42123/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1315_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1315_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1315_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (147/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5537/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31423/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58889/100000 : ℝ) else (15959/20000 : ℝ) ≤ X j i ∧ X j i ≤ (42123/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1315_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
