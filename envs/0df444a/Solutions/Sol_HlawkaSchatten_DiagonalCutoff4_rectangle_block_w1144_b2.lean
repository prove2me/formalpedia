-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1144_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:33:22.712703+00:00
-- url     : https://prove2.me/submissions/acfa319e-ef56-4591-b1f6-43ed4b2fafbe

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
theorem support_rectangle_w1144_s6_0 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-433179803/2000000000 : ℝ)*x 0 + (337084017/625000000 : ℝ)*x 1 + (5265445741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433179803/2000000000 : ℝ)^8337 ≤ (6580518988507/50000000000000 : ℝ)^6289 := by
    have hnat : (433179803 : ℕ)^8337*50000000000000^6289 ≤ 6580518988507^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433179803 2000000000 6580518988507 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337084017/625000000 : ℝ)^8337 ≤ (44110125727967/100000000000000 : ℝ)^6289 := by
    have hnat : (337084017 : ℕ)^8337*100000000000000^6289 ≤ 44110125727967^6289*625000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337084017 625000000 44110125727967 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265445741/10000000000 : ℝ)^8337 ≤ (42728836279039/100000000000000 : ℝ)^6289 := by
    have hnat : (5265445741 : ℕ)^8337*100000000000000^6289 ≤ 42728836279039^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265445741 10000000000 42728836279039 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-433179803/2000000000 : ℝ), (337084017/625000000 : ℝ), (5265445741/10000000000 : ℝ)] ![(6580518988507/50000000000000 : ℝ), (44110125727967/100000000000000 : ℝ), (42728836279039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-433179803/2000000000 : ℝ)|^8337 ≤ (6580518988507/50000000000000 : ℝ)^6289
        have hw : |(-433179803/2000000000 : ℝ)|=(433179803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337084017/625000000 : ℝ)|^8337 ≤ (44110125727967/100000000000000 : ℝ)^6289
        have hw : |(337084017/625000000 : ℝ)|=(337084017/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265445741/10000000000 : ℝ)|^8337 ≤ (42728836279039/100000000000000 : ℝ)^6289
        have hw : |(5265445741/10000000000 : ℝ)|=(5265445741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s6_1 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672419057/5000000000 : ℝ)*x 0 + (-1115387831/5000000000 : ℝ)*x 1 + (263272287/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672419057/5000000000 : ℝ)^8337 ≤ (43584994916809/100000000000000 : ℝ)^6289 := by
    have hnat : (2672419057 : ℕ)^8337*100000000000000^6289 ≤ 43584994916809^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672419057 5000000000 43584994916809 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115387831/5000000000 : ℝ)^8337 ≤ (13686168795783/100000000000000 : ℝ)^6289 := by
    have hnat : (1115387831 : ℕ)^8337*100000000000000^6289 ≤ 13686168795783^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115387831 5000000000 13686168795783 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263272287/500000000 : ℝ)^8337 ≤ (42728836268281/100000000000000 : ℝ)^6289 := by
    have hnat : (263272287 : ℕ)^8337*100000000000000^6289 ≤ 42728836268281^6289*500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263272287 500000000 42728836268281 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672419057/5000000000 : ℝ), (-1115387831/5000000000 : ℝ), (263272287/500000000 : ℝ)] ![(43584994916809/100000000000000 : ℝ), (13686168795783/100000000000000 : ℝ), (42728836268281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672419057/5000000000 : ℝ)|^8337 ≤ (43584994916809/100000000000000 : ℝ)^6289
        have hw : |(2672419057/5000000000 : ℝ)|=(2672419057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1115387831/5000000000 : ℝ)|^8337 ≤ (13686168795783/100000000000000 : ℝ)^6289
        have hw : |(-1115387831/5000000000 : ℝ)|=(1115387831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263272287/500000000 : ℝ)|^8337 ≤ (42728836268281/100000000000000 : ℝ)^6289
        have hw : |(263272287/500000000 : ℝ)|=(263272287/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s6_2 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336209519/2500000000 : ℝ)*x 0 + (5265445771/10000000000 : ℝ)*x 1 + (-2230775671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336209519/2500000000 : ℝ)^8337 ≤ (1743399780241/4000000000000 : ℝ)^6289 := by
    have hnat : (1336209519 : ℕ)^8337*4000000000000^6289 ≤ 1743399780241^6289*2500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336209519 2500000000 1743399780241 4000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265445771/10000000000 : ℝ)^8337 ≤ (21364418300883/50000000000000 : ℝ)^6289 := by
    have hnat : (5265445771 : ℕ)^8337*50000000000000^6289 ≤ 21364418300883^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265445771 10000000000 21364418300883 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2230775671/10000000000 : ℝ)^8337 ≤ (684308443449/5000000000000 : ℝ)^6289 := by
    have hnat : (2230775671 : ℕ)^8337*5000000000000^6289 ≤ 684308443449^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230775671 10000000000 684308443449 5000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336209519/2500000000 : ℝ), (5265445771/10000000000 : ℝ), (-2230775671/10000000000 : ℝ)] ![(1743399780241/4000000000000 : ℝ), (21364418300883/50000000000000 : ℝ), (684308443449/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336209519/2500000000 : ℝ)|^8337 ≤ (1743399780241/4000000000000 : ℝ)^6289
        have hw : |(1336209519/2500000000 : ℝ)|=(1336209519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265445771/10000000000 : ℝ)|^8337 ≤ (21364418300883/50000000000000 : ℝ)^6289
        have hw : |(5265445771/10000000000 : ℝ)|=(5265445771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2230775671/10000000000 : ℝ)|^8337 ≤ (684308443449/5000000000000 : ℝ)^6289
        have hw : |(-2230775671/10000000000 : ℝ)|=(2230775671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s6_3 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (68193349/156250000 : ℝ)*x 0 + (423894483/1000000000 : ℝ)*x 1 + (898699089/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68193349/156250000 : ℝ)^8337 ≤ (16658401702469/50000000000000 : ℝ)^6289 := by
    have hnat : (68193349 : ℕ)^8337*50000000000000^6289 ≤ 16658401702469^6289*156250000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68193349 156250000 16658401702469 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423894483/1000000000 : ℝ)^8337 ≤ (16026733713331/50000000000000 : ℝ)^6289 := by
    have hnat : (423894483 : ℕ)^8337*50000000000000^6289 ≤ 16026733713331^6289*1000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423894483 1000000000 16026733713331 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898699089/2000000000 : ℝ)^8337 ≤ (1385189166051/4000000000000 : ℝ)^6289 := by
    have hnat : (898699089 : ℕ)^8337*4000000000000^6289 ≤ 1385189166051^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898699089 2000000000 1385189166051 4000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(68193349/156250000 : ℝ), (423894483/1000000000 : ℝ), (898699089/2000000000 : ℝ)] ![(16658401702469/50000000000000 : ℝ), (16026733713331/50000000000000 : ℝ), (1385189166051/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(68193349/156250000 : ℝ)|^8337 ≤ (16658401702469/50000000000000 : ℝ)^6289
        have hw : |(68193349/156250000 : ℝ)|=(68193349/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(423894483/1000000000 : ℝ)|^8337 ≤ (16026733713331/50000000000000 : ℝ)^6289
        have hw : |(423894483/1000000000 : ℝ)|=(423894483/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(898699089/2000000000 : ℝ)|^8337 ≤ (1385189166051/4000000000000 : ℝ)^6289
        have hw : |(898699089/2000000000 : ℝ)|=(898699089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s6_4 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1082952003/5000000000 : ℝ)*x 0 + (82277637/156250000 : ℝ)*x 1 + (1078604009/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082952003/5000000000 : ℝ)^8337 ≤ (6580539090443/50000000000000 : ℝ)^6289 := by
    have hnat : (1082952003 : ℕ)^8337*50000000000000^6289 ≤ 6580539090443^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082952003 5000000000 6580539090443 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82277637/156250000 : ℝ)^8337 ≤ (10683077824727/25000000000000 : ℝ)^6289 := by
    have hnat : (82277637 : ℕ)^8337*25000000000000^6289 ≤ 10683077824727^6289*156250000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82277637 156250000 10683077824727 25000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078604009/2000000000 : ℝ)^8337 ≤ (11026652625423/25000000000000 : ℝ)^6289 := by
    have hnat : (1078604009 : ℕ)^8337*25000000000000^6289 ≤ 11026652625423^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078604009 2000000000 11026652625423 25000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1082952003/5000000000 : ℝ), (82277637/156250000 : ℝ), (1078604009/2000000000 : ℝ)] ![(6580539090443/50000000000000 : ℝ), (10683077824727/25000000000000 : ℝ), (11026652625423/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1082952003/5000000000 : ℝ)|^8337 ≤ (6580539090443/50000000000000 : ℝ)^6289
        have hw : |(-1082952003/5000000000 : ℝ)|=(1082952003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(82277637/156250000 : ℝ)|^8337 ≤ (10683077824727/25000000000000 : ℝ)^6289
        have hw : |(82277637/156250000 : ℝ)|=(82277637/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078604009/2000000000 : ℝ)|^8337 ≤ (11026652625423/25000000000000 : ℝ)^6289
        have hw : |(1078604009/2000000000 : ℝ)|=(1078604009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s6_5 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312429639/10000000000 : ℝ)*x 0 + (-2103201459/10000000000 : ℝ)*x 1 + (2696509999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312429639/10000000000 : ℝ)^8337 ≤ (8647000332217/20000000000000 : ℝ)^6289 := by
    have hnat : (5312429639 : ℕ)^8337*20000000000000^6289 ≤ 8647000332217^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312429639 10000000000 8647000332217 20000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2103201459/10000000000 : ℝ)^8337 ≤ (19778731763/156250000000 : ℝ)^6289 := by
    have hnat : (2103201459 : ℕ)^8337*156250000000^6289 ≤ 19778731763^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103201459 10000000000 19778731763 156250000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696509999/5000000000 : ℝ)^8337 ≤ (44106609992129/100000000000000 : ℝ)^6289 := by
    have hnat : (2696509999 : ℕ)^8337*100000000000000^6289 ≤ 44106609992129^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696509999 5000000000 44106609992129 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312429639/10000000000 : ℝ), (-2103201459/10000000000 : ℝ), (2696509999/5000000000 : ℝ)] ![(8647000332217/20000000000000 : ℝ), (19778731763/156250000000 : ℝ), (44106609992129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312429639/10000000000 : ℝ)|^8337 ≤ (8647000332217/20000000000000 : ℝ)^6289
        have hw : |(5312429639/10000000000 : ℝ)|=(5312429639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2103201459/10000000000 : ℝ)|^8337 ≤ (19778731763/156250000000 : ℝ)^6289
        have hw : |(-2103201459/10000000000 : ℝ)|=(2103201459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696509999/5000000000 : ℝ)|^8337 ≤ (44106609992129/100000000000000 : ℝ)^6289
        have hw : |(2696509999/5000000000 : ℝ)|=(2696509999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s6_6 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212497187/400000000 : ℝ)*x 0 + (1078603987/2000000000 : ℝ)*x 1 + (-262900187/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212497187/400000000 : ℝ)^8337 ≤ (43235002049479/100000000000000 : ℝ)^6289 := by
    have hnat : (212497187 : ℕ)^8337*100000000000000^6289 ≤ 43235002049479^6289*400000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212497187 400000000 43235002049479 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078603987/2000000000 : ℝ)^8337 ≤ (22053304654549/50000000000000 : ℝ)^6289 := by
    have hnat : (1078603987 : ℕ)^8337*50000000000000^6289 ≤ 22053304654549^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078603987 2000000000 22053304654549 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262900187/1250000000 : ℝ)^8337 ≤ (12658388623527/100000000000000 : ℝ)^6289 := by
    have hnat : (262900187 : ℕ)^8337*100000000000000^6289 ≤ 12658388623527^6289*1250000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262900187 1250000000 12658388623527 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212497187/400000000 : ℝ), (1078603987/2000000000 : ℝ), (-262900187/1250000000 : ℝ)] ![(43235002049479/100000000000000 : ℝ), (22053304654549/50000000000000 : ℝ), (12658388623527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212497187/400000000 : ℝ)|^8337 ≤ (43235002049479/100000000000000 : ℝ)^6289
        have hw : |(212497187/400000000 : ℝ)|=(212497187/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078603987/2000000000 : ℝ)|^8337 ≤ (22053304654549/50000000000000 : ℝ)^6289
        have hw : |(1078603987/2000000000 : ℝ)|=(1078603987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-262900187/1250000000 : ℝ)|^8337 ≤ (12658388623527/100000000000000 : ℝ)^6289
        have hw : |(-262900187/1250000000 : ℝ)|=(262900187/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s6_7 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364384119/10000000000 : ℝ)*x 0 + (4492852529/10000000000 : ℝ)*x 1 + (847918033/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364384119/10000000000 : ℝ)^8337 ≤ (33316902406433/100000000000000 : ℝ)^6289 := by
    have hnat : (4364384119 : ℕ)^8337*100000000000000^6289 ≤ 33316902406433^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364384119 10000000000 33316902406433 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4492852529/10000000000 : ℝ)^8337 ≤ (34623161091269/100000000000000 : ℝ)^6289 := by
    have hnat : (4492852529 : ℕ)^8337*100000000000000^6289 ≤ 34623161091269^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492852529 10000000000 34623161091269 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (847918033/2000000000 : ℝ)^8337 ≤ (2003746030663/6250000000000 : ℝ)^6289 := by
    have hnat : (847918033 : ℕ)^8337*6250000000000^6289 ≤ 2003746030663^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847918033 2000000000 2003746030663 6250000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364384119/10000000000 : ℝ), (4492852529/10000000000 : ℝ), (847918033/2000000000 : ℝ)] ![(33316902406433/100000000000000 : ℝ), (34623161091269/100000000000000 : ℝ), (2003746030663/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364384119/10000000000 : ℝ)|^8337 ≤ (33316902406433/100000000000000 : ℝ)^6289
        have hw : |(4364384119/10000000000 : ℝ)|=(4364384119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4492852529/10000000000 : ℝ)|^8337 ≤ (34623161091269/100000000000000 : ℝ)^6289
        have hw : |(4492852529/10000000000 : ℝ)|=(4492852529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(847918033/2000000000 : ℝ)|^8337 ≤ (2003746030663/6250000000000 : ℝ)^6289
        have hw : |(847918033/2000000000 : ℝ)|=(847918033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1144_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37378183/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11349/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7029/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1409/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5659/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1409/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5659/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1409/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5659/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1409/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5659/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1409/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5659/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1409/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5659/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5659/50000 : ℝ) ^ (521/128 : ℝ) ≤ (7039096904924017/50000000000000000000 : ℝ) := by
    have hpowers : (5659/50000 : ℝ)^521 ≤ (7039096904924017/50000000000000000000 : ℝ)^128 := by
      have hnat : (5659 : ℕ)^521*50000000000000000000^128 ≤ 7039096904924017^128*50000^521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5659 50000 7039096904924017 50000000000000000000 521 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5659/50000 : ℝ)) (X := (7039096904924017/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hpowhi : (1409/10000 : ℝ) ^ (521/128 : ℝ) ≤ (34340117484782087/100000000000000000000 : ℝ) := by
    have hpowers : (1409/10000 : ℝ)^521 ≤ (34340117484782087/100000000000000000000 : ℝ)^128 := by
      have hnat : (1409 : ℕ)^521*100000000000000000000^128 ≤ 34340117484782087^128*10000^521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1409 10000 34340117484782087 100000000000000000000 521 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1409/10000 : ℝ)) (X := (34340117484782087/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007039096904924017/25000000000000000000 : ℝ) ≤ (625043229785889/625000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (25007039096904924017/25000000000000000000 : ℝ)^128 ≤ (625043229785889/625000000000000 : ℝ)^521 := by
      have hnat : (25007039096904924017 : ℕ)^128*625000000000000^521 ≤ 625043229785889^521*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007039096904924017 25000000000000000000 625043229785889 625000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625043229785889/625000000000000 : ℝ)) (X := (25007039096904924017/25000000000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048418311294630121/100000000000000000000 : ℝ) ≤ (10001189330596303/10000000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (100048418311294630121/100000000000000000000 : ℝ)^128 ≤ (10001189330596303/10000000000000000 : ℝ)^521 := by
      have hnat : (100048418311294630121 : ℕ)^128*10000000000000000^521 ≤ 10001189330596303^521*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048418311294630121 100000000000000000000 10001189330596303 10000000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001189330596303/10000000000000000 : ℝ)) (X := (100048418311294630121/100000000000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034340117484782087/50000000000000000000 : ℝ) ≤ (5000843492309191/5000000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (50034340117484782087/50000000000000000000 : ℝ)^128 ≤ (5000843492309191/5000000000000000 : ℝ)^521 := by
      have hnat : (50034340117484782087 : ℕ)^128*5000000000000000^521 ≤ 5000843492309191^521*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034340117484782087 50000000000000000000 5000843492309191 5000000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000843492309191/5000000000000000 : ℝ)) (X := (50034340117484782087/50000000000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7039096904924017/50000000000000000000 : ℝ) ≤ ((6927663107754992171/6930000000000000000 : ℝ)+2*(497654022079/277200000000000 : ℝ)*(5659/50000 : ℝ))^(521/128 : ℝ) := by
    rw [show (6927663107754992171/6930000000000000000 : ℝ)+2*(497654022079/277200000000000 : ℝ)*(5659/50000 : ℝ)=(625043229785889/625000000000000 : ℝ) by norm_num, show 1+2*(7039096904924017/50000000000000000000 : ℝ)=(25007039096904924017/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34340117484782087/100000000000000000000 : ℝ)+(7039096904924017/50000000000000000000 : ℝ) ≤ ((6927663107754992171/6930000000000000000 : ℝ)+(497654022079/277200000000000 : ℝ)*((1409/10000 : ℝ)+(5659/50000 : ℝ)))^(521/128 : ℝ) := by
    rw [show (6927663107754992171/6930000000000000000 : ℝ)+(497654022079/277200000000000 : ℝ)*((1409/10000 : ℝ)+(5659/50000 : ℝ))=(10001189330596303/10000000000000000 : ℝ) by norm_num, show 1+(34340117484782087/100000000000000000000 : ℝ)+(7039096904924017/50000000000000000000 : ℝ)=(100048418311294630121/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34340117484782087/100000000000000000000 : ℝ) ≤ ((6927663107754992171/6930000000000000000 : ℝ)+2*(497654022079/277200000000000 : ℝ)*(1409/10000 : ℝ))^(521/128 : ℝ) := by
    rw [show (6927663107754992171/6930000000000000000 : ℝ)+2*(497654022079/277200000000000 : ℝ)*(1409/10000 : ℝ)=(5000843492309191/5000000000000000 : ℝ) by norm_num, show 1+2*(34340117484782087/100000000000000000000 : ℝ)=(50034340117484782087/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6927663107754992171/6930000000000000000 : ℝ)*(X 1 0+X 2 0)+(497654022079/277200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (5659/50000 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (6927663107754992171/6930000000000000000 : ℝ)) (alpha := (497654022079/277200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6927663107754992171/6930000000000000000 : ℝ)*(X 0 1+X 2 1)+(497654022079/277200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (5659/50000 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (6927663107754992171/6930000000000000000 : ℝ)) (alpha := (497654022079/277200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6927663107754992171/6930000000000000000 : ℝ)*(X 0 2+X 1 2)+(497654022079/277200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (5659/50000 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (6927663107754992171/6930000000000000000 : ℝ)) (alpha := (497654022079/277200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-433179803/2000000000 : ℝ)*X 0 0+(337084017/625000000 : ℝ)*X 0 1+(5265445741/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672419057/5000000000 : ℝ)*X 1 0+(-1115387831/5000000000 : ℝ)*X 1 1+(263272287/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336209519/2500000000 : ℝ)*X 2 0+(5265445771/10000000000 : ℝ)*X 2 1+(-2230775671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((68193349/156250000 : ℝ)*X 0 0+(423894483/1000000000 : ℝ)*X 0 1+(898699089/2000000000 : ℝ)*X 0 2+(68193349/156250000 : ℝ)*X 1 0+(423894483/1000000000 : ℝ)*X 1 1+(898699089/2000000000 : ℝ)*X 1 2+(68193349/156250000 : ℝ)*X 2 0+(423894483/1000000000 : ℝ)*X 2 1+(898699089/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1082952003/5000000000 : ℝ)*X 0 0+(82277637/156250000 : ℝ)*X 0 1+(1078604009/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312429639/10000000000 : ℝ)*X 1 0+(-2103201459/10000000000 : ℝ)*X 1 1+(2696509999/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212497187/400000000 : ℝ)*X 2 0+(1078603987/2000000000 : ℝ)*X 2 1+(-262900187/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4364384119/10000000000 : ℝ)*X 0 0+(4492852529/10000000000 : ℝ)*X 0 1+(847918033/2000000000 : ℝ)*X 0 2+(4364384119/10000000000 : ℝ)*X 1 0+(4492852529/10000000000 : ℝ)*X 1 1+(847918033/2000000000 : ℝ)*X 1 2+(4364384119/10000000000 : ℝ)*X 2 0+(4492852529/10000000000 : ℝ)*X 2 1+(847918033/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52669020972454130374903497/19250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18362311/2500000000000 : ℝ)*(base19) + (59154229/10000000000000 : ℝ)*(base23) + (46693329/100000000000000 : ℝ)*(lower2) + (96981871/100000000000000 : ℝ)*(upper3) + (3627989/50000000000000 : ℝ)*(upper5) + (5873626861248079/100000000000000 : ℝ)*(major0) + (5873626861248079/100000000000000 : ℝ)*(major1) + (73420335765601/1250000000000 : ℝ)*(major2) + (1954680301139843/25000000000000 : ℝ)*(sp0) + (781874006536757/10000000000000 : ℝ)*(sp1) + (7818740208317719/100000000000000 : ℝ)*(sp2) + (982125320340057/25000000000000 : ℝ)*(sp3) + (19595300637/100000000000000 : ℝ)*(sp4) + (11550074141/100000000000000 : ℝ)*(sp7) + (30691506495581/781250000000 : ℝ)*(f.failure) + (7818740799860009/100000000000000 : ℝ)*(f.sum) + (6440377880459/1320000000000000000000000000 : ℝ)*base66 + (2608509078194789509/693000000000000000000000000000000 : ℝ)*base67 + (388822645224720167/17325000000000000000000000000000 : ℝ)*base69 + (517837476560789509/693000000000000000000000000000000 : ℝ)*base71 + (4902794614261/1320000000000000000000000000 : ℝ)*base73 + (40306317243254833/17325000000000000000000000000000 : ℝ)*base76 + (152549998426298643/11000000000000000000000000000000 : ℝ)*base77 + (157942790809298643/11000000000000000000000000000000 : ℝ)*base79 + (54184177689119/13860000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (240729/39062500000000000000 : ℝ)*base90 + (240729/39062500000000000000 : ℝ)*base92 + (315677/19531250000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (472347347084818194057365219/57750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1582478329/100000000000000 : ℝ)*(base19) + (167593533/10000000000000 : ℝ)*(base23) + (145189967/100000000000000 : ℝ)*(upper3) + (5351343/20000000000000 : ℝ)*(lower4) + (172661497/100000000000000 : ℝ)*(upper5) + (5903471256190411/100000000000000 : ℝ)*(major0) + (5903471256190411/100000000000000 : ℝ)*(major1) + (5903471256190411/100000000000000 : ℝ)*(major2) + (42870704671/100000000000000 : ℝ)*(sp1) + (8240986373/20000000000000 : ℝ)*(sp2) + (491154268893189/6250000000000 : ℝ)*(sp4) + (982302981138503/12500000000000 : ℝ)*(sp5) + (7858425421423829/100000000000000 : ℝ)*(sp6) + (493559242181329/12500000000000 : ℝ)*(sp7) + (493559242181329/12500000000000 : ℝ)*(f.failure) + (491154268893189/6250000000000 : ℝ)*(f.sum) + (2798670862571/13860000000000000000000000000 : ℝ)*base66 + (44602990475841313/11000000000000000000000000000000 : ℝ)*base68 + (132463749924158687/11000000000000000000000000000000 : ℝ)*base69 + (17662726466158687/11000000000000000000000000000000 : ℝ)*base71 + (75204046080131/13860000000000000000000000000 : ℝ)*base74 + (168172616392158687/11000000000000000000000000000000 : ℝ)*base75 + (7097628131158687/11000000000000000000000000000000 : ℝ)*base77 + (46009667946158687/11000000000000000000000000000000 : ℝ)*base79 + (31090988705809/13860000000000000000000000000 : ℝ)*base81 + (170207/312500000000000000000 : ℝ)*base89 + (170207/312500000000000000000 : ℝ)*base91 + (170207/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1144_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37378183/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1144_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1144_s7_0 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1082962677/5000000000 : ℝ)*x 0 + (5393024009/10000000000 : ℝ)*x 1 + (5265748789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082962677/5000000000 : ℝ)^8337 ≤ (3290312536303/25000000000000 : ℝ)^6289 := by
    have hnat : (1082962677 : ℕ)^8337*25000000000000^6289 ≤ 3290312536303^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082962677 5000000000 3290312536303 25000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393024009/10000000000 : ℝ)^8337 ≤ (44106653478441/100000000000000 : ℝ)^6289 := by
    have hnat : (5393024009 : ℕ)^8337*100000000000000^6289 ≤ 44106653478441^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393024009 10000000000 44106653478441 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265748789/10000000000 : ℝ)^8337 ≤ (42732096369281/100000000000000 : ℝ)^6289 := by
    have hnat : (5265748789 : ℕ)^8337*100000000000000^6289 ≤ 42732096369281^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265748789 10000000000 42732096369281 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1082962677/5000000000 : ℝ), (5393024009/10000000000 : ℝ), (5265748789/10000000000 : ℝ)] ![(3290312536303/25000000000000 : ℝ), (44106653478441/100000000000000 : ℝ), (42732096369281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1082962677/5000000000 : ℝ)|^8337 ≤ (3290312536303/25000000000000 : ℝ)^6289
        have hw : |(-1082962677/5000000000 : ℝ)|=(1082962677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393024009/10000000000 : ℝ)|^8337 ≤ (44106653478441/100000000000000 : ℝ)^6289
        have hw : |(5393024009/10000000000 : ℝ)|=(5393024009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265748789/10000000000 : ℝ)|^8337 ≤ (42732096369281/100000000000000 : ℝ)^6289
        have hw : |(5265748789/10000000000 : ℝ)|=(5265748789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s7_1 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344757927/10000000000 : ℝ)*x 0 + (-1115240697/5000000000 : ℝ)*x 1 + (5265748787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344757927/10000000000 : ℝ)^8337 ≤ (43584128087563/100000000000000 : ℝ)^6289 := by
    have hnat : (5344757927 : ℕ)^8337*100000000000000^6289 ≤ 43584128087563^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344757927 10000000000 43584128087563 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115240697/5000000000 : ℝ)^8337 ≤ (273675510933/2000000000000 : ℝ)^6289 := by
    have hnat : (1115240697 : ℕ)^8337*2000000000000^6289 ≤ 273675510933^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115240697 5000000000 273675510933 2000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265748787/10000000000 : ℝ)^8337 ≤ (8546419269553/20000000000000 : ℝ)^6289 := by
    have hnat : (5265748787 : ℕ)^8337*20000000000000^6289 ≤ 8546419269553^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265748787 10000000000 8546419269553 20000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344757927/10000000000 : ℝ), (-1115240697/5000000000 : ℝ), (5265748787/10000000000 : ℝ)] ![(43584128087563/100000000000000 : ℝ), (273675510933/2000000000000 : ℝ), (8546419269553/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344757927/10000000000 : ℝ)|^8337 ≤ (43584128087563/100000000000000 : ℝ)^6289
        have hw : |(5344757927/10000000000 : ℝ)|=(5344757927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1115240697/5000000000 : ℝ)|^8337 ≤ (273675510933/2000000000000 : ℝ)^6289
        have hw : |(-1115240697/5000000000 : ℝ)|=(1115240697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265748787/10000000000 : ℝ)|^8337 ≤ (8546419269553/20000000000000 : ℝ)^6289
        have hw : |(5265748787/10000000000 : ℝ)|=(5265748787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s7_2 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672378963/5000000000 : ℝ)*x 0 + (5265748787/10000000000 : ℝ)*x 1 + (-446096279/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672378963/5000000000 : ℝ)^8337 ≤ (43584128076753/100000000000000 : ℝ)^6289 := by
    have hnat : (2672378963 : ℕ)^8337*100000000000000^6289 ≤ 43584128076753^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672378963 5000000000 43584128076753 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265748787/10000000000 : ℝ)^8337 ≤ (8546419269553/20000000000000 : ℝ)^6289 := by
    have hnat : (5265748787 : ℕ)^8337*20000000000000^6289 ≤ 8546419269553^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265748787 10000000000 8546419269553 20000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (446096279/2000000000 : ℝ)^8337 ≤ (6841887777391/50000000000000 : ℝ)^6289 := by
    have hnat : (446096279 : ℕ)^8337*50000000000000^6289 ≤ 6841887777391^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446096279 2000000000 6841887777391 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672378963/5000000000 : ℝ), (5265748787/10000000000 : ℝ), (-446096279/2000000000 : ℝ)] ![(43584128076753/100000000000000 : ℝ), (8546419269553/20000000000000 : ℝ), (6841887777391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672378963/5000000000 : ℝ)|^8337 ≤ (43584128076753/100000000000000 : ℝ)^6289
        have hw : |(2672378963/5000000000 : ℝ)|=(2672378963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265748787/10000000000 : ℝ)|^8337 ≤ (8546419269553/20000000000000 : ℝ)^6289
        have hw : |(5265748787/10000000000 : ℝ)|=(5265748787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-446096279/2000000000 : ℝ)|^8337 ≤ (6841887777391/50000000000000 : ℝ)^6289
        have hw : |(-446096279/2000000000 : ℝ)|=(446096279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s7_3 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2182195091/5000000000 : ℝ)*x 0 + (1059890759/2500000000 : ℝ)*x 1 + (4492873143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182195091/5000000000 : ℝ)^8337 ≤ (33316963762501/100000000000000 : ℝ)^6289 := by
    have hnat : (2182195091 : ℕ)^8337*100000000000000^6289 ≤ 33316963762501^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182195091 5000000000 33316963762501 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059890759/2500000000 : ℝ)^8337 ≤ (16029832266779/50000000000000 : ℝ)^6289 := by
    have hnat : (1059890759 : ℕ)^8337*50000000000000^6289 ≤ 16029832266779^6289*2500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059890759 2500000000 16029832266779 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4492873143/10000000000 : ℝ)^8337 ≤ (3462337168011/10000000000000 : ℝ)^6289 := by
    have hnat : (4492873143 : ℕ)^8337*10000000000000^6289 ≤ 3462337168011^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492873143 10000000000 3462337168011 10000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182195091/5000000000 : ℝ), (1059890759/2500000000 : ℝ), (4492873143/10000000000 : ℝ)] ![(33316963762501/100000000000000 : ℝ), (16029832266779/50000000000000 : ℝ), (3462337168011/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182195091/5000000000 : ℝ)|^8337 ≤ (33316963762501/100000000000000 : ℝ)^6289
        have hw : |(2182195091/5000000000 : ℝ)|=(2182195091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1059890759/2500000000 : ℝ)|^8337 ≤ (16029832266779/50000000000000 : ℝ)^6289
        have hw : |(1059890759/2500000000 : ℝ)|=(1059890759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4492873143/10000000000 : ℝ)|^8337 ≤ (3462337168011/10000000000000 : ℝ)^6289
        have hw : |(4492873143/10000000000 : ℝ)|=(4492873143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s7_4 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2165930239/10000000000 : ℝ)*x 0 + (1053213741/2000000000 : ℝ)*x 1 + (674087867/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165930239/10000000000 : ℝ)^8337 ≤ (658064474769/5000000000000 : ℝ)^6289 := by
    have hnat : (2165930239 : ℕ)^8337*5000000000000^6289 ≤ 658064474769^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165930239 10000000000 658064474769 5000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053213741/2000000000 : ℝ)^8337 ≤ (42735537986187/100000000000000 : ℝ)^6289 := by
    have hnat : (1053213741 : ℕ)^8337*100000000000000^6289 ≤ 42735537986187^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053213741 2000000000 42735537986187 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674087867/1250000000 : ℝ)^8337 ≤ (22051586257201/50000000000000 : ℝ)^6289 := by
    have hnat : (674087867 : ℕ)^8337*50000000000000^6289 ≤ 22051586257201^6289*1250000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674087867 1250000000 22051586257201 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2165930239/10000000000 : ℝ), (1053213741/2000000000 : ℝ), (674087867/1250000000 : ℝ)] ![(658064474769/5000000000000 : ℝ), (42735537986187/100000000000000 : ℝ), (22051586257201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2165930239/10000000000 : ℝ)|^8337 ≤ (658064474769/5000000000000 : ℝ)^6289
        have hw : |(-2165930239/10000000000 : ℝ)|=(2165930239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053213741/2000000000 : ℝ)|^8337 ≤ (42735537986187/100000000000000 : ℝ)^6289
        have hw : |(1053213741/2000000000 : ℝ)|=(1053213741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674087867/1250000000 : ℝ)|^8337 ≤ (22051586257201/50000000000000 : ℝ)^6289
        have hw : |(674087867/1250000000 : ℝ)|=(674087867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s7_5 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312507321/10000000000 : ℝ)*x 0 + (-131470453/625000000 : ℝ)*x 1 + (1078540587/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312507321/10000000000 : ℝ)^8337 ≤ (21617919876767/50000000000000 : ℝ)^6289 := by
    have hnat : (5312507321 : ℕ)^8337*50000000000000^6289 ≤ 21617919876767^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312507321 10000000000 21617919876767 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131470453/625000000 : ℝ)^8337 ≤ (12660987728333/100000000000000 : ℝ)^6289 := by
    have hnat : (131470453 : ℕ)^8337*100000000000000^6289 ≤ 12660987728333^6289*625000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131470453 625000000 12660987728333 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078540587/2000000000 : ℝ)^8337 ≤ (1102579312589/2500000000000 : ℝ)^6289 := by
    have hnat : (1078540587 : ℕ)^8337*2500000000000^6289 ≤ 1102579312589^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078540587 2000000000 1102579312589 2500000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312507321/10000000000 : ℝ), (-131470453/625000000 : ℝ), (1078540587/2000000000 : ℝ)] ![(21617919876767/50000000000000 : ℝ), (12660987728333/100000000000000 : ℝ), (1102579312589/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312507321/10000000000 : ℝ)|^8337 ≤ (21617919876767/50000000000000 : ℝ)^6289
        have hw : |(5312507321/10000000000 : ℝ)|=(5312507321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-131470453/625000000 : ℝ)|^8337 ≤ (12660987728333/100000000000000 : ℝ)^6289
        have hw : |(-131470453/625000000 : ℝ)|=(131470453/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078540587/2000000000 : ℝ)|^8337 ≤ (1102579312589/2500000000000 : ℝ)^6289
        have hw : |(1078540587/2000000000 : ℝ)|=(1078540587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s7_6 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312507321/10000000000 : ℝ)*x 0 + (1078540587/2000000000 : ℝ)*x 1 + (-2103527247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312507321/10000000000 : ℝ)^8337 ≤ (21617919876767/50000000000000 : ℝ)^6289 := by
    have hnat : (5312507321 : ℕ)^8337*50000000000000^6289 ≤ 21617919876767^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312507321 10000000000 21617919876767 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078540587/2000000000 : ℝ)^8337 ≤ (1102579312589/2500000000000 : ℝ)^6289 := by
    have hnat : (1078540587 : ℕ)^8337*2500000000000^6289 ≤ 1102579312589^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078540587 2000000000 1102579312589 2500000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2103527247/10000000000 : ℝ)^8337 ≤ (6330493860177/50000000000000 : ℝ)^6289 := by
    have hnat : (2103527247 : ℕ)^8337*50000000000000^6289 ≤ 6330493860177^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103527247 10000000000 6330493860177 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312507321/10000000000 : ℝ), (1078540587/2000000000 : ℝ), (-2103527247/10000000000 : ℝ)] ![(21617919876767/50000000000000 : ℝ), (1102579312589/2500000000000 : ℝ), (6330493860177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312507321/10000000000 : ℝ)|^8337 ≤ (21617919876767/50000000000000 : ℝ)^6289
        have hw : |(5312507321/10000000000 : ℝ)|=(5312507321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078540587/2000000000 : ℝ)|^8337 ≤ (1102579312589/2500000000000 : ℝ)^6289
        have hw : |(1078540587/2000000000 : ℝ)|=(1078540587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2103527247/10000000000 : ℝ)|^8337 ≤ (6330493860177/50000000000000 : ℝ)^6289
        have hw : |(-2103527247/10000000000 : ℝ)|=(2103527247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s7_7 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (136387497/312500000 : ℝ)*x 0 + (4492236423/10000000000 : ℝ)*x 1 + (4240202059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136387497/312500000 : ℝ)^8337 ≤ (33317062146807/100000000000000 : ℝ)^6289 := by
    have hnat : (136387497 : ℕ)^8337*100000000000000^6289 ≤ 33317062146807^6289*312500000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136387497 312500000 33317062146807 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4492236423/10000000000 : ℝ)^8337 ≤ (34616867210661/100000000000000 : ℝ)^6289 := by
    have hnat : (4492236423 : ℕ)^8337*100000000000000^6289 ≤ 34616867210661^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492236423 10000000000 34616867210661 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4240202059/10000000000 : ℝ)^8337 ≤ (32066070626441/100000000000000 : ℝ)^6289 := by
    have hnat : (4240202059 : ℕ)^8337*100000000000000^6289 ≤ 32066070626441^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240202059 10000000000 32066070626441 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136387497/312500000 : ℝ), (4492236423/10000000000 : ℝ), (4240202059/10000000000 : ℝ)] ![(33317062146807/100000000000000 : ℝ), (34616867210661/100000000000000 : ℝ), (32066070626441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136387497/312500000 : ℝ)|^8337 ≤ (33317062146807/100000000000000 : ℝ)^6289
        have hw : |(136387497/312500000 : ℝ)|=(136387497/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4492236423/10000000000 : ℝ)|^8337 ≤ (34616867210661/100000000000000 : ℝ)^6289
        have hw : |(4492236423/10000000000 : ℝ)|=(4492236423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4240202059/10000000000 : ℝ)|^8337 ≤ (32066070626441/100000000000000 : ℝ)^6289
        have hw : |(4240202059/10000000000 : ℝ)|=(4240202059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1144_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37378183/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2271/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14051/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7029/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11349/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7029/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11349/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7029/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11349/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7029/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11349/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7029/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11349/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7029/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11349/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11349/100000 : ℝ) ^ (521/128 : ℝ) ≤ (1423580695199079/10000000000000000000 : ℝ) := by
    have hpowers : (11349/100000 : ℝ)^521 ≤ (1423580695199079/10000000000000000000 : ℝ)^128 := by
      have hnat : (11349 : ℕ)^521*10000000000000000000^128 ≤ 1423580695199079^128*100000^521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11349 100000 1423580695199079 10000000000000000000 521 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11349/100000 : ℝ)) (X := (1423580695199079/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hpowhi : (7029/50000 : ℝ) ^ (521/128 : ℝ) ≤ (34023777510164731/100000000000000000000 : ℝ) := by
    have hpowers : (7029/50000 : ℝ)^521 ≤ (34023777510164731/100000000000000000000 : ℝ)^128 := by
      have hnat : (7029 : ℕ)^521*100000000000000000000^128 ≤ 34023777510164731^128*50000^521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7029 50000 34023777510164731 100000000000000000000 521 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7029/50000 : ℝ)) (X := (34023777510164731/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001423580695199079/5000000000000000000 : ℝ) ≤ (2500174854860873/2500000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (5001423580695199079/5000000000000000000 : ℝ)^128 ≤ (2500174854860873/2500000000000000 : ℝ)^521 := by
      have hnat : (5001423580695199079 : ℕ)^128*2500000000000000^521 ≤ 2500174854860873^521*5000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001423580695199079 5000000000000000000 2500174854860873 2500000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500174854860873/2500000000000000 : ℝ)) (X := (5001423580695199079/5000000000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048259584462155521/100000000000000000000 : ℝ) ≤ (10001185432394863/10000000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (100048259584462155521/100000000000000000000 : ℝ)^128 ≤ (10001185432394863/10000000000000000 : ℝ)^521 := by
      have hnat : (100048259584462155521 : ℕ)^128*10000000000000000^521 ≤ 10001185432394863^521*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048259584462155521 100000000000000000000 10001185432394863 10000000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001185432394863/10000000000000000 : ℝ)) (X := (100048259584462155521/100000000000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034023777510164731/50000000000000000000 : ℝ) ≤ (5000835722673117/5000000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (50034023777510164731/50000000000000000000 : ℝ)^128 ≤ (5000835722673117/5000000000000000 : ℝ)^521 := by
      have hnat : (50034023777510164731 : ℕ)^128*5000000000000000^521 ≤ 5000835722673117^521*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034023777510164731 50000000000000000000 5000835722673117 5000000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000835722673117/5000000000000000 : ℝ)) (X := (50034023777510164731/50000000000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1423580695199079/10000000000000000000 : ℝ) ≤ ((300898480058913343/301000000000000000 : ℝ)+2*(486012951371/270900000000000 : ℝ)*(11349/100000 : ℝ))^(521/128 : ℝ) := by
    rw [show (300898480058913343/301000000000000000 : ℝ)+2*(486012951371/270900000000000 : ℝ)*(11349/100000 : ℝ)=(2500174854860873/2500000000000000 : ℝ) by norm_num, show 1+2*(1423580695199079/10000000000000000000 : ℝ)=(5001423580695199079/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34023777510164731/100000000000000000000 : ℝ)+(1423580695199079/10000000000000000000 : ℝ) ≤ ((300898480058913343/301000000000000000 : ℝ)+(486012951371/270900000000000 : ℝ)*((7029/50000 : ℝ)+(11349/100000 : ℝ)))^(521/128 : ℝ) := by
    rw [show (300898480058913343/301000000000000000 : ℝ)+(486012951371/270900000000000 : ℝ)*((7029/50000 : ℝ)+(11349/100000 : ℝ))=(10001185432394863/10000000000000000 : ℝ) by norm_num, show 1+(34023777510164731/100000000000000000000 : ℝ)+(1423580695199079/10000000000000000000 : ℝ)=(100048259584462155521/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34023777510164731/100000000000000000000 : ℝ) ≤ ((300898480058913343/301000000000000000 : ℝ)+2*(486012951371/270900000000000 : ℝ)*(7029/50000 : ℝ))^(521/128 : ℝ) := by
    rw [show (300898480058913343/301000000000000000 : ℝ)+2*(486012951371/270900000000000 : ℝ)*(7029/50000 : ℝ)=(5000835722673117/5000000000000000 : ℝ) by norm_num, show 1+2*(34023777510164731/100000000000000000000 : ℝ)=(50034023777510164731/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (300898480058913343/301000000000000000 : ℝ)*(X 1 0+X 2 0)+(486012951371/270900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (11349/100000 : ℝ)) (hi := (7029/50000 : ℝ)) (c := (300898480058913343/301000000000000000 : ℝ)) (alpha := (486012951371/270900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (300898480058913343/301000000000000000 : ℝ)*(X 0 1+X 2 1)+(486012951371/270900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (11349/100000 : ℝ)) (hi := (7029/50000 : ℝ)) (c := (300898480058913343/301000000000000000 : ℝ)) (alpha := (486012951371/270900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (300898480058913343/301000000000000000 : ℝ)*(X 0 2+X 1 2)+(486012951371/270900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (11349/100000 : ℝ)) (hi := (7029/50000 : ℝ)) (c := (300898480058913343/301000000000000000 : ℝ)) (alpha := (486012951371/270900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1082962677/5000000000 : ℝ)*X 0 0+(5393024009/10000000000 : ℝ)*X 0 1+(5265748789/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344757927/10000000000 : ℝ)*X 1 0+(-1115240697/5000000000 : ℝ)*X 1 1+(5265748787/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672378963/5000000000 : ℝ)*X 2 0+(5265748787/10000000000 : ℝ)*X 2 1+(-446096279/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2182195091/5000000000 : ℝ)*X 0 0+(1059890759/2500000000 : ℝ)*X 0 1+(4492873143/10000000000 : ℝ)*X 0 2+(2182195091/5000000000 : ℝ)*X 1 0+(1059890759/2500000000 : ℝ)*X 1 1+(4492873143/10000000000 : ℝ)*X 1 2+(2182195091/5000000000 : ℝ)*X 2 0+(1059890759/2500000000 : ℝ)*X 2 1+(4492873143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2165930239/10000000000 : ℝ)*X 0 0+(1053213741/2000000000 : ℝ)*X 0 1+(674087867/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312507321/10000000000 : ℝ)*X 1 0+(-131470453/625000000 : ℝ)*X 1 1+(1078540587/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312507321/10000000000 : ℝ)*X 2 0+(1078540587/2000000000 : ℝ)*X 2 1+(-2103527247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((136387497/312500000 : ℝ)*X 0 0+(4492236423/10000000000 : ℝ)*X 0 1+(4240202059/10000000000 : ℝ)*X 0 2+(136387497/312500000 : ℝ)*X 1 0+(4492236423/10000000000 : ℝ)*X 1 1+(4240202059/10000000000 : ℝ)*X 1 2+(136387497/312500000 : ℝ)*X 2 0+(4492236423/10000000000 : ℝ)*X 2 1+(4240202059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10978765510051582451373/1505000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1441205251/100000000000000 : ℝ)*(base19) + (267883783/20000000000000 : ℝ)*(base23) + (428933/800000000000 : ℝ)*(lower2) + (185212203/100000000000000 : ℝ)*(upper3) + (13611339/12500000000000 : ℝ)*(upper5) + (2951210040585259/50000000000000 : ℝ)*(major0) + (2951210040585259/50000000000000 : ℝ)*(major1) + (5902420081170519/100000000000000 : ℝ)*(major2) + (1571406003521523/20000000000000 : ℝ)*(sp0) + (1571413521550159/20000000000000 : ℝ)*(sp1) + (7857067709537131/100000000000000 : ℝ)*(sp2) + (986937379675539/25000000000000 : ℝ)*(sp3) + (2439459277/6250000000000 : ℝ)*(sp4) + (10675760401/50000000000000 : ℝ)*(sp7) + (1973885435111479/50000000000000 : ℝ)*(f.failure) + (3928534524478023/50000000000000 : ℝ)*(f.sum) + (18263212124579/3870000000000000000000000000 : ℝ)*base66 + (31086718573334163/15050000000000000000000000000000 : ℝ)*base68 + (758899906053904847/270900000000000000000000000000000 : ℝ)*base70 + (83094449736265837/15050000000000000000000000000000 : ℝ)*base71 + (18480083789879/3870000000000000000000000000 : ℝ)*base74 + (2513379462915895153/270900000000000000000000000000000 : ℝ)*base75 + (404110079918912467/135450000000000000000000000000000 : ℝ)*base78 + (564018625362237533/135450000000000000000000000000000 : ℝ)*base79 + (76599177742033/13545000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (12462657/1250000000000000000000 : ℝ)*base89 + (12462657/1250000000000000000000 : ℝ)*base91 + (37343/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4253299246255193893678403/752500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1028862177/100000000000000 : ℝ)*(base19) + (280091389/25000000000000 : ℝ)*(base23) + (112483869/100000000000000 : ℝ)*(upper3) + (41604099/100000000000000 : ℝ)*(lower4) + (23033709/20000000000000 : ℝ)*(upper5) + (296611768195269/5000000000000 : ℝ)*(major0) + (296611768195269/5000000000000 : ℝ)*(major1) + (296611768195269/5000000000000 : ℝ)*(major2) + (28416072289/100000000000000 : ℝ)*(sp1) + (15294394247/50000000000000 : ℝ)*(sp2) + (7896758034554247/100000000000000 : ℝ)*(sp4) + (7896728589619781/100000000000000 : ℝ)*(sp5) + (1974181581350049/25000000000000 : ℝ)*(sp6) + (1983856252424503/50000000000000 : ℝ)*(sp7) + (1983856252424503/50000000000000 : ℝ)*(f.failure) + (7896758034554247/100000000000000 : ℝ)*(f.sum) + (3608050838659/903000000000000000000000000 : ℝ)*base65 + (68435819813542199/4515000000000000000000000000000 : ℝ)*base68 + (53932226045137199/4515000000000000000000000000000 : ℝ)*base70 + (62781736581367199/4515000000000000000000000000000 : ℝ)*base72 + (160210935991/45150000000000000000000000 : ℝ)*base74 + (24091017504427199/4515000000000000000000000000000 : ℝ)*base76 + (51684935534707199/4515000000000000000000000000000 : ℝ)*base78 + (29368842755587199/4515000000000000000000000000000 : ℝ)*base80 + (457172329937/112875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (16818049/1250000000000000000000 : ℝ)*base89 + (16818049/1250000000000000000000 : ℝ)*base91 + (16818049/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1144_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37378183/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1144_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1144_s8_0 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2165933293/10000000000 : ℝ)*x 0 + (1078591491/2000000000 : ℝ)*x 1 + (2632904959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165933293/10000000000 : ℝ)^8337 ≤ (6580657048149/50000000000000 : ℝ)^6289 := by
    have hnat : (2165933293 : ℕ)^8337*50000000000000^6289 ≤ 6580657048149^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165933293 10000000000 6580657048149 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078591491/2000000000 : ℝ)^8337 ≤ (44105931917111/100000000000000 : ℝ)^6289 := by
    have hnat : (1078591491 : ℕ)^8337*100000000000000^6289 ≤ 44105931917111^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078591491 2000000000 44105931917111 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632904959/5000000000 : ℝ)^8337 ≤ (10683188495567/25000000000000 : ℝ)^6289 := by
    have hnat : (2632904959 : ℕ)^8337*25000000000000^6289 ≤ 10683188495567^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632904959 5000000000 10683188495567 25000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2165933293/10000000000 : ℝ), (1078591491/2000000000 : ℝ), (2632904959/5000000000 : ℝ)] ![(6580657048149/50000000000000 : ℝ), (44105931917111/100000000000000 : ℝ), (10683188495567/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2165933293/10000000000 : ℝ)|^8337 ≤ (6580657048149/50000000000000 : ℝ)^6289
        have hw : |(-2165933293/10000000000 : ℝ)|=(2165933293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078591491/2000000000 : ℝ)|^8337 ≤ (44105931917111/100000000000000 : ℝ)^6289
        have hw : |(1078591491/2000000000 : ℝ)|=(1078591491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632904959/5000000000 : ℝ)|^8337 ≤ (10683188495567/25000000000000 : ℝ)^6289
        have hw : |(2632904959/5000000000 : ℝ)|=(2632904959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s8_1 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672370269/5000000000 : ℝ)*x 0 + (-2230423623/10000000000 : ℝ)*x 1 + (1053161987/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672370269/5000000000 : ℝ)^8337 ≤ (21791970055673/50000000000000 : ℝ)^6289 := by
    have hnat : (2672370269 : ℕ)^8337*50000000000000^6289 ≤ 21791970055673^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672370269 5000000000 21791970055673 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2230423623/10000000000 : ℝ)^8337 ≤ (13683305713563/100000000000000 : ℝ)^6289 := by
    have hnat : (2230423623 : ℕ)^8337*100000000000000^6289 ≤ 13683305713563^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230423623 10000000000 13683305713563 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053161987/2000000000 : ℝ)^8337 ≤ (42732754165151/100000000000000 : ℝ)^6289 := by
    have hnat : (1053161987 : ℕ)^8337*100000000000000^6289 ≤ 42732754165151^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053161987 2000000000 42732754165151 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672370269/5000000000 : ℝ), (-2230423623/10000000000 : ℝ), (1053161987/2000000000 : ℝ)] ![(21791970055673/50000000000000 : ℝ), (13683305713563/100000000000000 : ℝ), (42732754165151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672370269/5000000000 : ℝ)|^8337 ≤ (21791970055673/50000000000000 : ℝ)^6289
        have hw : |(2672370269/5000000000 : ℝ)|=(2672370269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2230423623/10000000000 : ℝ)|^8337 ≤ (13683305713563/100000000000000 : ℝ)^6289
        have hw : |(-2230423623/10000000000 : ℝ)|=(2230423623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053161987/2000000000 : ℝ)|^8337 ≤ (42732754165151/100000000000000 : ℝ)^6289
        have hw : |(1053161987/2000000000 : ℝ)|=(1053161987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s8_2 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344740477/10000000000 : ℝ)*x 0 + (658226253/1250000000 : ℝ)*x 1 + (-446084717/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344740477/10000000000 : ℝ)^8337 ≤ (10895984862983/25000000000000 : ℝ)^6289 := by
    have hnat : (5344740477 : ℕ)^8337*25000000000000^6289 ≤ 10895984862983^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344740477 10000000000 10895984862983 25000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658226253/1250000000 : ℝ)^8337 ≤ (10683188780649/25000000000000 : ℝ)^6289 := by
    have hnat : (658226253 : ℕ)^8337*25000000000000^6289 ≤ 10683188780649^6289*1250000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658226253 1250000000 10683188780649 25000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (446084717/2000000000 : ℝ)^8337 ≤ (6841652702261/50000000000000 : ℝ)^6289 := by
    have hnat : (446084717 : ℕ)^8337*50000000000000^6289 ≤ 6841652702261^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446084717 2000000000 6841652702261 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344740477/10000000000 : ℝ), (658226253/1250000000 : ℝ), (-446084717/2000000000 : ℝ)] ![(10895984862983/25000000000000 : ℝ), (10683188780649/25000000000000 : ℝ), (6841652702261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344740477/10000000000 : ℝ)|^8337 ≤ (10895984862983/25000000000000 : ℝ)^6289
        have hw : |(5344740477/10000000000 : ℝ)|=(5344740477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658226253/1250000000 : ℝ)|^8337 ≤ (10683188780649/25000000000000 : ℝ)^6289
        have hw : |(658226253/1250000000 : ℝ)|=(658226253/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-446084717/2000000000 : ℝ)|^8337 ≤ (6841652702261/50000000000000 : ℝ)^6289
        have hw : |(-446084717/2000000000 : ℝ)|=(446084717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s8_3 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (87287869/200000000 : ℝ)*x 0 + (847937929/2000000000 : ℝ)*x 1 + (4492745667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87287869/200000000 : ℝ)^8337 ≤ (33316996833869/100000000000000 : ℝ)^6289 := by
    have hnat : (87287869 : ℕ)^8337*100000000000000^6289 ≤ 33316996833869^6289*200000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87287869 200000000 33316996833869 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (847937929/2000000000 : ℝ)^8337 ≤ (32060933741479/100000000000000 : ℝ)^6289 := by
    have hnat : (847937929 : ℕ)^8337*100000000000000^6289 ≤ 32060933741479^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847937929 2000000000 32060933741479 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4492745667/10000000000 : ℝ)^8337 ≤ (1081939669179/3125000000000 : ℝ)^6289 := by
    have hnat : (4492745667 : ℕ)^8337*3125000000000^6289 ≤ 1081939669179^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492745667 10000000000 1081939669179 3125000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(87287869/200000000 : ℝ), (847937929/2000000000 : ℝ), (4492745667/10000000000 : ℝ)] ![(33316996833869/100000000000000 : ℝ), (32060933741479/100000000000000 : ℝ), (1081939669179/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(87287869/200000000 : ℝ)|^8337 ≤ (33316996833869/100000000000000 : ℝ)^6289
        have hw : |(87287869/200000000 : ℝ)|=(87287869/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(847937929/2000000000 : ℝ)|^8337 ≤ (32060933741479/100000000000000 : ℝ)^6289
        have hw : |(847937929/2000000000 : ℝ)|=(847937929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4492745667/10000000000 : ℝ)|^8337 ≤ (1081939669179/3125000000000 : ℝ)^6289
        have hw : |(4492745667/10000000000 : ℝ)|=(4492745667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s8_4 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-27074227/125000000 : ℝ)*x 0 + (1316532303/2500000000 : ℝ)*x 1 + (5392637009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27074227/125000000 : ℝ)^8337 ≤ (6580676650759/50000000000000 : ℝ)^6289 := by
    have hnat : (27074227 : ℕ)^8337*50000000000000^6289 ≤ 6580676650759^6289*125000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27074227 125000000 6580676650759 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316532303/2500000000 : ℝ)^8337 ≤ (21368094460347/50000000000000 : ℝ)^6289 := by
    have hnat : (1316532303 : ℕ)^8337*50000000000000^6289 ≤ 21368094460347^6289*2500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316532303 2500000000 21368094460347 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392637009/10000000000 : ℝ)^8337 ≤ (44102457764689/100000000000000 : ℝ)^6289 := by
    have hnat : (5392637009 : ℕ)^8337*100000000000000^6289 ≤ 44102457764689^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392637009 10000000000 44102457764689 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-27074227/125000000 : ℝ), (1316532303/2500000000 : ℝ), (5392637009/10000000000 : ℝ)] ![(6580676650759/50000000000000 : ℝ), (21368094460347/50000000000000 : ℝ), (44102457764689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-27074227/125000000 : ℝ)|^8337 ≤ (6580676650759/50000000000000 : ℝ)^6289
        have hw : |(-27074227/125000000 : ℝ)|=(27074227/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316532303/2500000000 : ℝ)|^8337 ≤ (21368094460347/50000000000000 : ℝ)^6289
        have hw : |(1316532303/2500000000 : ℝ)|=(1316532303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392637009/10000000000 : ℝ)|^8337 ≤ (44102457764689/100000000000000 : ℝ)^6289
        have hw : |(5392637009/10000000000 : ℝ)|=(5392637009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s8_5 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312522311/10000000000 : ℝ)*x 0 + (-525899139/2500000000 : ℝ)*x 1 + (5392637009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312522311/10000000000 : ℝ)^8337 ≤ (8647200295501/20000000000000 : ℝ)^6289 := by
    have hnat : (5312522311 : ℕ)^8337*20000000000000^6289 ≤ 8647200295501^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312522311 10000000000 8647200295501 20000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525899139/2500000000 : ℝ)^8337 ≤ (12661540738797/100000000000000 : ℝ)^6289 := by
    have hnat : (525899139 : ℕ)^8337*100000000000000^6289 ≤ 12661540738797^6289*2500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525899139 2500000000 12661540738797 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392637009/10000000000 : ℝ)^8337 ≤ (44102457764689/100000000000000 : ℝ)^6289 := by
    have hnat : (5392637009 : ℕ)^8337*100000000000000^6289 ≤ 44102457764689^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392637009 10000000000 44102457764689 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312522311/10000000000 : ℝ), (-525899139/2500000000 : ℝ), (5392637009/10000000000 : ℝ)] ![(8647200295501/20000000000000 : ℝ), (12661540738797/100000000000000 : ℝ), (44102457764689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312522311/10000000000 : ℝ)|^8337 ≤ (8647200295501/20000000000000 : ℝ)^6289
        have hw : |(5312522311/10000000000 : ℝ)|=(5312522311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-525899139/2500000000 : ℝ)|^8337 ≤ (12661540738797/100000000000000 : ℝ)^6289
        have hw : |(-525899139/2500000000 : ℝ)|=(525899139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392637009/10000000000 : ℝ)|^8337 ≤ (44102457764689/100000000000000 : ℝ)^6289
        have hw : |(5392637009/10000000000 : ℝ)|=(5392637009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s8_6 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312522311/10000000000 : ℝ)*x 0 + (5392637009/10000000000 : ℝ)*x 1 + (-525899139/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312522311/10000000000 : ℝ)^8337 ≤ (8647200295501/20000000000000 : ℝ)^6289 := by
    have hnat : (5312522311 : ℕ)^8337*20000000000000^6289 ≤ 8647200295501^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312522311 10000000000 8647200295501 20000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392637009/10000000000 : ℝ)^8337 ≤ (44102457764689/100000000000000 : ℝ)^6289 := by
    have hnat : (5392637009 : ℕ)^8337*100000000000000^6289 ≤ 44102457764689^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392637009 10000000000 44102457764689 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525899139/2500000000 : ℝ)^8337 ≤ (12661540738797/100000000000000 : ℝ)^6289 := by
    have hnat : (525899139 : ℕ)^8337*100000000000000^6289 ≤ 12661540738797^6289*2500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525899139 2500000000 12661540738797 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312522311/10000000000 : ℝ), (5392637009/10000000000 : ℝ), (-525899139/2500000000 : ℝ)] ![(8647200295501/20000000000000 : ℝ), (44102457764689/100000000000000 : ℝ), (12661540738797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312522311/10000000000 : ℝ)|^8337 ≤ (8647200295501/20000000000000 : ℝ)^6289
        have hw : |(5312522311/10000000000 : ℝ)|=(5312522311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392637009/10000000000 : ℝ)|^8337 ≤ (44102457764689/100000000000000 : ℝ)^6289
        have hw : |(5392637009/10000000000 : ℝ)|=(5392637009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-525899139/2500000000 : ℝ)|^8337 ≤ (12661540738797/100000000000000 : ℝ)^6289
        have hw : |(-525899139/2500000000 : ℝ)|=(525899139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s8_7 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2182201559/5000000000 : ℝ)*x 0 + (2246055091/5000000000 : ℝ)*x 1 + (4240327451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182201559/5000000000 : ℝ)^8337 ≤ (8329273667933/25000000000000 : ℝ)^6289 := by
    have hnat : (2182201559 : ℕ)^8337*25000000000000^6289 ≤ 8329273667933^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182201559 5000000000 8329273667933 25000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246055091/5000000000 : ℝ)^8337 ≤ (34615577620227/100000000000000 : ℝ)^6289 := by
    have hnat : (2246055091 : ℕ)^8337*100000000000000^6289 ≤ 34615577620227^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246055091 5000000000 34615577620227 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4240327451/10000000000 : ℝ)^8337 ≤ (8016831924007/25000000000000 : ℝ)^6289 := by
    have hnat : (4240327451 : ℕ)^8337*25000000000000^6289 ≤ 8016831924007^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240327451 10000000000 8016831924007 25000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182201559/5000000000 : ℝ), (2246055091/5000000000 : ℝ), (4240327451/10000000000 : ℝ)] ![(8329273667933/25000000000000 : ℝ), (34615577620227/100000000000000 : ℝ), (8016831924007/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182201559/5000000000 : ℝ)|^8337 ≤ (8329273667933/25000000000000 : ℝ)^6289
        have hw : |(2182201559/5000000000 : ℝ)|=(2182201559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246055091/5000000000 : ℝ)|^8337 ≤ (34615577620227/100000000000000 : ℝ)^6289
        have hw : |(2246055091/5000000000 : ℝ)|=(2246055091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4240327451/10000000000 : ℝ)|^8337 ≤ (8016831924007/25000000000000 : ℝ)^6289
        have hw : |(4240327451/10000000000 : ℝ)|=(4240327451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1144_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37378183/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2839/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (281/2000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (2271/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2271/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2271/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2271/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2271/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2271/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2271/20000 : ℝ) ^ (521/128 : ℝ) ≤ (14266465809034637/100000000000000000000 : ℝ) := by
    have hpowers : (2271/20000 : ℝ)^521 ≤ (14266465809034637/100000000000000000000 : ℝ)^128 := by
      have hnat : (2271 : ℕ)^521*100000000000000000000^128 ≤ 14266465809034637^128*20000^521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2271 20000 14266465809034637 100000000000000000000 521 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2271/20000 : ℝ)) (X := (14266465809034637/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14051/100000 : ℝ) ^ (521/128 : ℝ) ≤ (16977436092060149/50000000000000000000 : ℝ) := by
    have hpowers : (14051/100000 : ℝ)^521 ≤ (16977436092060149/50000000000000000000 : ℝ)^128 := by
      have hnat : (14051 : ℕ)^521*50000000000000000000^128 ≤ 16977436092060149^128*100000^521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14051 100000 16977436092060149 50000000000000000000 521 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14051/100000 : ℝ)) (X := (16977436092060149/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014266465809034637/50000000000000000000 : ℝ) ≤ (31252190392443/31250000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (50014266465809034637/50000000000000000000 : ℝ)^128 ≤ (31252190392443/31250000000000 : ℝ)^521 := by
      have hnat : (50014266465809034637 : ℕ)^128*31250000000000^521 ≤ 31252190392443^521*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014266465809034637 50000000000000000000 31252190392443 31250000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31252190392443/31250000000000 : ℝ)) (X := (50014266465809034637/50000000000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009644267598630987/20000000000000000000 : ℝ) ≤ (5000592246546053/5000000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (20009644267598630987/20000000000000000000 : ℝ)^128 ≤ (5000592246546053/5000000000000000 : ℝ)^521 := by
      have hnat : (20009644267598630987 : ℕ)^128*5000000000000000^521 ≤ 5000592246546053^521*20000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009644267598630987 20000000000000000000 5000592246546053 5000000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000592246546053/5000000000000000 : ℝ)) (X := (20009644267598630987/20000000000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016977436092060149/25000000000000000000 : ℝ) ≤ (2500417015150613/2500000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (25016977436092060149/25000000000000000000 : ℝ)^128 ≤ (2500417015150613/2500000000000000 : ℝ)^521 := by
      have hnat : (25016977436092060149 : ℕ)^128*2500000000000000^521 ≤ 2500417015150613^521*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016977436092060149 25000000000000000000 2500417015150613 2500000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500417015150613/2500000000000000 : ℝ)) (X := (25016977436092060149/25000000000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14266465809034637/100000000000000000000 : ℝ) ≤ ((269509078772084673/269600000000000000 : ℝ)+2*(241783755173/134800000000000 : ℝ)*(2271/20000 : ℝ))^(521/128 : ℝ) := by
    rw [show (269509078772084673/269600000000000000 : ℝ)+2*(241783755173/134800000000000 : ℝ)*(2271/20000 : ℝ)=(31252190392443/31250000000000 : ℝ) by norm_num, show 1+2*(14266465809034637/100000000000000000000 : ℝ)=(50014266465809034637/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16977436092060149/50000000000000000000 : ℝ)+(14266465809034637/100000000000000000000 : ℝ) ≤ ((269509078772084673/269600000000000000 : ℝ)+(241783755173/134800000000000 : ℝ)*((14051/100000 : ℝ)+(2271/20000 : ℝ)))^(521/128 : ℝ) := by
    rw [show (269509078772084673/269600000000000000 : ℝ)+(241783755173/134800000000000 : ℝ)*((14051/100000 : ℝ)+(2271/20000 : ℝ))=(5000592246546053/5000000000000000 : ℝ) by norm_num, show 1+(16977436092060149/50000000000000000000 : ℝ)+(14266465809034637/100000000000000000000 : ℝ)=(20009644267598630987/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16977436092060149/50000000000000000000 : ℝ) ≤ ((269509078772084673/269600000000000000 : ℝ)+2*(241783755173/134800000000000 : ℝ)*(14051/100000 : ℝ))^(521/128 : ℝ) := by
    rw [show (269509078772084673/269600000000000000 : ℝ)+2*(241783755173/134800000000000 : ℝ)*(14051/100000 : ℝ)=(2500417015150613/2500000000000000 : ℝ) by norm_num, show 1+2*(16977436092060149/50000000000000000000 : ℝ)=(25016977436092060149/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (269509078772084673/269600000000000000 : ℝ)*(X 1 0+X 2 0)+(241783755173/134800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (2271/20000 : ℝ)) (hi := (14051/100000 : ℝ)) (c := (269509078772084673/269600000000000000 : ℝ)) (alpha := (241783755173/134800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (269509078772084673/269600000000000000 : ℝ)*(X 0 1+X 2 1)+(241783755173/134800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (2271/20000 : ℝ)) (hi := (14051/100000 : ℝ)) (c := (269509078772084673/269600000000000000 : ℝ)) (alpha := (241783755173/134800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (269509078772084673/269600000000000000 : ℝ)*(X 0 2+X 1 2)+(241783755173/134800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (2271/20000 : ℝ)) (hi := (14051/100000 : ℝ)) (c := (269509078772084673/269600000000000000 : ℝ)) (alpha := (241783755173/134800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2165933293/10000000000 : ℝ)*X 0 0+(1078591491/2000000000 : ℝ)*X 0 1+(2632904959/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672370269/5000000000 : ℝ)*X 1 0+(-2230423623/10000000000 : ℝ)*X 1 1+(1053161987/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344740477/10000000000 : ℝ)*X 2 0+(658226253/1250000000 : ℝ)*X 2 1+(-446084717/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((87287869/200000000 : ℝ)*X 0 0+(847937929/2000000000 : ℝ)*X 0 1+(4492745667/10000000000 : ℝ)*X 0 2+(87287869/200000000 : ℝ)*X 1 0+(847937929/2000000000 : ℝ)*X 1 1+(4492745667/10000000000 : ℝ)*X 1 2+(87287869/200000000 : ℝ)*X 2 0+(847937929/2000000000 : ℝ)*X 2 1+(4492745667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-27074227/125000000 : ℝ)*X 0 0+(1316532303/2500000000 : ℝ)*X 0 1+(5392637009/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312522311/10000000000 : ℝ)*X 1 0+(-525899139/2500000000 : ℝ)*X 1 1+(5392637009/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312522311/10000000000 : ℝ)*X 2 0+(5392637009/10000000000 : ℝ)*X 2 1+(-525899139/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2182201559/5000000000 : ℝ)*X 0 0+(2246055091/5000000000 : ℝ)*X 0 1+(4240327451/10000000000 : ℝ)*X 0 2+(2182201559/5000000000 : ℝ)*X 1 0+(2246055091/5000000000 : ℝ)*X 1 1+(4240327451/10000000000 : ℝ)*X 1 2+(2182201559/5000000000 : ℝ)*X 2 0+(2246055091/5000000000 : ℝ)*X 2 1+(4240327451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (68907617506655095871841/6740000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2036958443/100000000000000 : ℝ)*(base19) + (897123521/50000000000000 : ℝ)*(base23) + (40873241/50000000000000 : ℝ)*(lower2) + (247458043/100000000000000 : ℝ)*(upper3) + (44449713/25000000000000 : ℝ)*(upper5) + (5908374968834013/100000000000000 : ℝ)*(major0) + (5908374968834013/100000000000000 : ℝ)*(major1) + (5908374968834013/100000000000000 : ℝ)*(major2) + (7864938285222397/100000000000000 : ℝ)*(sp0) + (1966248456610701/25000000000000 : ℝ)*(sp1) + (3932497034577103/50000000000000 : ℝ)*(sp2) + (49396537044917/1250000000000 : ℝ)*(sp3) + (57578178851/100000000000000 : ℝ)*(sp4) + (30769884009/100000000000000 : ℝ)*(sp7) + (3951753733477369/100000000000000 : ℝ)*(f.failure) + (245781120731289/3125000000000 : ℝ)*(f.sum) + (13159951176691/6740000000000000000000000000 : ℝ)*base66 + (11127232502719251/26960000000000000000000000000000 : ℝ)*base68 + (54458887940240749/26960000000000000000000000000000 : ℝ)*base69 + (107645890563440749/26960000000000000000000000000000 : ℝ)*base71 + (27331902256791/6740000000000000000000000000 : ℝ)*base74 + (342110558900640749/26960000000000000000000000000000 : ℝ)*base75 + (191227485298159251/26960000000000000000000000000000 : ℝ)*base78 + (116560941885839251/26960000000000000000000000000000 : ℝ)*base80 + (15224002629811/6740000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (159473/2500000000000000000000 : ℝ)*base90 + (159473/2500000000000000000000 : ℝ)*base92 + (159473/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (63211373369575020229011/6740000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1712249899/100000000000000 : ℝ)*(base19) + (1862465331/100000000000000 : ℝ)*(base23) + (15020583/2500000000000 : ℝ)*(lower1) + (188072367/100000000000000 : ℝ)*(upper3) + (34154019/50000000000000 : ℝ)*(lower4) + (191048747/100000000000000 : ℝ)*(upper5) + (5938128013916537/100000000000000 : ℝ)*(major0) + (5938128013916537/100000000000000 : ℝ)*(major1) + (5938128013916537/100000000000000 : ℝ)*(major2) + (1783815961/50000000000000 : ℝ)*(sp2) + (1976150493525783/25000000000000 : ℝ)*(sp4) + (7904600261853233/100000000000000 : ℝ)*(sp5) + (7904596544005879/100000000000000 : ℝ)*(sp6) + (992913435277963/25000000000000 : ℝ)*(sp7) + (992913435277963/25000000000000 : ℝ)*(f.failure) + (1976150493525783/25000000000000 : ℝ)*(f.sum) + (48783323812061/6740000000000000000000000000 : ℝ)*base65 + (520320790623340599/26960000000000000000000000000000 : ℝ)*base68 + (380616561511660599/26960000000000000000000000000000 : ℝ)*base70 + (2887119452377699401/26960000000000000000000000000000 : ℝ)*base71 + (1788174378061/6740000000000000000000000000 : ℝ)*base73 + (1075328908461699401/26960000000000000000000000000000 : ℝ)*base75 + (95859212145699401/26960000000000000000000000000000 : ℝ)*base77 + (684589959306140599/26960000000000000000000000000000 : ℝ)*base80 + (7804267090981/6740000000000000000000000000 : ℝ)*base81 + (631229/625000000000000000000 : ℝ)*base89 + (631229/625000000000000000000 : ℝ)*base91 + (631229/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1144_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37378183/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2839/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (281/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1144_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1144_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37378183/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2839/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (281/2000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1144_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1144_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1144_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37378183/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2839/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (281/2000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1144_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
