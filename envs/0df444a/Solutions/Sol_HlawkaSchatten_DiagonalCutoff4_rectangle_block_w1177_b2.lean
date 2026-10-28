-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1177_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:48:21.868987+00:00
-- url     : https://prove2.me/submissions/dfbf44de-4cff-4c04-b444-e59c340f1752

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
theorem support_rectangle_w1177_s6_0 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-537558593/2500000000 : ℝ)*x 0 + (5392679101/10000000000 : ℝ)*x 1 + (5266023283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537558593/2500000000 : ℝ)^4185 ≤ (3267276129841/25000000000000 : ℝ)^3161 := by
    have hnat : (537558593 : ℕ)^4185*25000000000000^3161 ≤ 3267276129841^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537558593 2500000000 3267276129841 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392679101/10000000000 : ℝ)^4185 ≤ (22074617136031/50000000000000 : ℝ)^3161 := by
    have hnat : (5392679101 : ℕ)^4185*50000000000000^3161 ≤ 22074617136031^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392679101 10000000000 22074617136031 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266023283/10000000000 : ℝ)^4185 ≤ (42781661205191/100000000000000 : ℝ)^3161 := by
    have hnat : (5266023283 : ℕ)^4185*100000000000000^3161 ≤ 42781661205191^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266023283 10000000000 42781661205191 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-537558593/2500000000 : ℝ), (5392679101/10000000000 : ℝ), (5266023283/10000000000 : ℝ)] ![(3267276129841/25000000000000 : ℝ), (22074617136031/50000000000000 : ℝ), (42781661205191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-537558593/2500000000 : ℝ)|^4185 ≤ (3267276129841/25000000000000 : ℝ)^3161
        have hw : |(-537558593/2500000000 : ℝ)|=(537558593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392679101/10000000000 : ℝ)|^4185 ≤ (22074617136031/50000000000000 : ℝ)^3161
        have hw : |(5392679101/10000000000 : ℝ)|=(5392679101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266023283/10000000000 : ℝ)|^4185 ≤ (42781661205191/100000000000000 : ℝ)^3161
        have hw : |(5266023283/10000000000 : ℝ)|=(5266023283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s6_1 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668086291/1250000000 : ℝ)*x 0 + (-553617929/2500000000 : ℝ)*x 1 + (2633011663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668086291/1250000000 : ℝ)^4185 ≤ (43629834792241/100000000000000 : ℝ)^3161 := by
    have hnat : (668086291 : ℕ)^4185*100000000000000^3161 ≤ 43629834792241^3161*1250000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668086291 1250000000 43629834792241 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553617929/2500000000 : ℝ)^4185 ≤ (169856293999/1250000000000 : ℝ)^3161 := by
    have hnat : (553617929 : ℕ)^4185*1250000000000^3161 ≤ 169856293999^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553617929 2500000000 169856293999 1250000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633011663/5000000000 : ℝ)^4185 ≤ (21390830833847/50000000000000 : ℝ)^3161 := by
    have hnat : (2633011663 : ℕ)^4185*50000000000000^3161 ≤ 21390830833847^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633011663 5000000000 21390830833847 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668086291/1250000000 : ℝ), (-553617929/2500000000 : ℝ), (2633011663/5000000000 : ℝ)] ![(43629834792241/100000000000000 : ℝ), (169856293999/1250000000000 : ℝ), (21390830833847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668086291/1250000000 : ℝ)|^4185 ≤ (43629834792241/100000000000000 : ℝ)^3161
        have hw : |(668086291/1250000000 : ℝ)|=(668086291/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-553617929/2500000000 : ℝ)|^4185 ≤ (169856293999/1250000000000 : ℝ)^3161
        have hw : |(-553617929/2500000000 : ℝ)|=(553617929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633011663/5000000000 : ℝ)|^4185 ≤ (21390830833847/50000000000000 : ℝ)^3161
        have hw : |(2633011663/5000000000 : ℝ)|=(2633011663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s6_2 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344690427/10000000000 : ℝ)*x 0 + (2633011583/5000000000 : ℝ)*x 1 + (-2214471797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344690427/10000000000 : ℝ)^4185 ≤ (218149179311/500000000000 : ℝ)^3161 := by
    have hnat : (5344690427 : ℕ)^4185*500000000000^3161 ≤ 218149179311^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344690427 10000000000 218149179311 500000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633011583/5000000000 : ℝ)^4185 ≤ (21390829973377/50000000000000 : ℝ)^3161 := by
    have hnat : (2633011583 : ℕ)^4185*50000000000000^3161 ≤ 21390829973377^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633011583 5000000000 21390829973377 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2214471797/10000000000 : ℝ)^4185 ≤ (13588504177967/100000000000000 : ℝ)^3161 := by
    have hnat : (2214471797 : ℕ)^4185*100000000000000^3161 ≤ 13588504177967^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214471797 10000000000 13588504177967 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344690427/10000000000 : ℝ), (2633011583/5000000000 : ℝ), (-2214471797/10000000000 : ℝ)] ![(218149179311/500000000000 : ℝ), (21390829973377/50000000000000 : ℝ), (13588504177967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344690427/10000000000 : ℝ)|^4185 ≤ (218149179311/500000000000 : ℝ)^3161
        have hw : |(5344690427/10000000000 : ℝ)|=(5344690427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633011583/5000000000 : ℝ)|^4185 ≤ (21390829973377/50000000000000 : ℝ)^3161
        have hw : |(2633011583/5000000000 : ℝ)|=(2633011583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2214471797/10000000000 : ℝ)|^4185 ≤ (13588504177967/100000000000000 : ℝ)^3161
        have hw : |(-2214471797/10000000000 : ℝ)|=(2214471797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s6_3 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (174390077/400000000 : ℝ)*x 0 + (2117359107/5000000000 : ℝ)*x 1 + (561053523/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174390077/400000000 : ℝ)^4185 ≤ (8329254045581/25000000000000 : ℝ)^3161 := by
    have hnat : (174390077 : ℕ)^4185*25000000000000^3161 ≤ 8329254045581^3161*400000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174390077 400000000 8329254045581 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117359107/5000000000 : ℝ)^4185 ≤ (32057896434113/100000000000000 : ℝ)^3161 := by
    have hnat : (2117359107 : ℕ)^4185*100000000000000^3161 ≤ 32057896434113^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117359107 5000000000 32057896434113 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561053523/1250000000 : ℝ)^4185 ≤ (17312543682393/50000000000000 : ℝ)^3161 := by
    have hnat : (561053523 : ℕ)^4185*50000000000000^3161 ≤ 17312543682393^3161*1250000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561053523 1250000000 17312543682393 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174390077/400000000 : ℝ), (2117359107/5000000000 : ℝ), (561053523/1250000000 : ℝ)] ![(8329254045581/25000000000000 : ℝ), (32057896434113/100000000000000 : ℝ), (17312543682393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174390077/400000000 : ℝ)|^4185 ≤ (8329254045581/25000000000000 : ℝ)^3161
        have hw : |(174390077/400000000 : ℝ)|=(174390077/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2117359107/5000000000 : ℝ)|^4185 ≤ (32057896434113/100000000000000 : ℝ)^3161
        have hw : |(2117359107/5000000000 : ℝ)|=(2117359107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(561053523/1250000000 : ℝ)|^4185 ≤ (17312543682393/50000000000000 : ℝ)^3161
        have hw : |(561053523/1250000000 : ℝ)|=(561053523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s6_4 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-268779909/1250000000 : ℝ)*x 0 + (5266343241/10000000000 : ℝ)*x 1 + (84255593/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268779909/1250000000 : ℝ)^4185 ≤ (6534571974703/50000000000000 : ℝ)^3161 := by
    have hnat : (268779909 : ℕ)^4185*50000000000000^3161 ≤ 6534571974703^3161*1250000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268779909 1250000000 6534571974703 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266343241/10000000000 : ℝ)^4185 ≤ (2139255133401/5000000000000 : ℝ)^3161 := by
    have hnat : (5266343241 : ℕ)^4185*5000000000000^3161 ≤ 2139255133401^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266343241 10000000000 2139255133401 5000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84255593/156250000 : ℝ)^4185 ≤ (44145753368839/100000000000000 : ℝ)^3161 := by
    have hnat : (84255593 : ℕ)^4185*100000000000000^3161 ≤ 44145753368839^3161*156250000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84255593 156250000 44145753368839 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-268779909/1250000000 : ℝ), (5266343241/10000000000 : ℝ), (84255593/156250000 : ℝ)] ![(6534571974703/50000000000000 : ℝ), (2139255133401/5000000000000 : ℝ), (44145753368839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-268779909/1250000000 : ℝ)|^4185 ≤ (6534571974703/50000000000000 : ℝ)^3161
        have hw : |(-268779909/1250000000 : ℝ)|=(268779909/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266343241/10000000000 : ℝ)|^4185 ≤ (2139255133401/5000000000000 : ℝ)^3161
        have hw : |(5266343241/10000000000 : ℝ)|=(5266343241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84255593/156250000 : ℝ)|^4185 ≤ (44145753368839/100000000000000 : ℝ)^3161
        have hw : |(84255593/156250000 : ℝ)|=(84255593/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s6_5 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (664064939/1250000000 : ℝ)*x 0 + (-1044068491/5000000000 : ℝ)*x 1 + (5392358023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664064939/1250000000 : ℝ)^4185 ≤ (676288792881/1562500000000 : ℝ)^3161 := by
    have hnat : (664064939 : ℕ)^4185*1562500000000^3161 ≤ 676288792881^3161*1250000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664064939 1250000000 676288792881 1562500000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044068491/5000000000 : ℝ)^4185 ≤ (12571763099947/100000000000000 : ℝ)^3161 := by
    have hnat : (1044068491 : ℕ)^4185*100000000000000^3161 ≤ 12571763099947^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044068491 5000000000 12571763099947 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392358023/10000000000 : ℝ)^4185 ≤ (22072877069197/50000000000000 : ℝ)^3161 := by
    have hnat : (5392358023 : ℕ)^4185*50000000000000^3161 ≤ 22072877069197^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392358023 10000000000 22072877069197 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664064939/1250000000 : ℝ), (-1044068491/5000000000 : ℝ), (5392358023/10000000000 : ℝ)] ![(676288792881/1562500000000 : ℝ), (12571763099947/100000000000000 : ℝ), (22072877069197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664064939/1250000000 : ℝ)|^4185 ≤ (676288792881/1562500000000 : ℝ)^3161
        have hw : |(664064939/1250000000 : ℝ)|=(664064939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1044068491/5000000000 : ℝ)|^4185 ≤ (12571763099947/100000000000000 : ℝ)^3161
        have hw : |(-1044068491/5000000000 : ℝ)|=(1044068491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392358023/10000000000 : ℝ)|^4185 ≤ (22072877069197/50000000000000 : ℝ)^3161
        have hw : |(5392358023/10000000000 : ℝ)|=(5392358023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s6_6 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328129873/2500000000 : ℝ)*x 0 + (5392358077/10000000000 : ℝ)*x 1 + (-261017117/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328129873/2500000000 : ℝ)^4185 ≤ (43282482528653/100000000000000 : ℝ)^3161 := by
    have hnat : (1328129873 : ℕ)^4185*100000000000000^3161 ≤ 43282482528653^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328129873 2500000000 43282482528653 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392358077/10000000000 : ℝ)^4185 ≤ (44145754723689/100000000000000 : ℝ)^3161 := by
    have hnat : (5392358077 : ℕ)^4185*100000000000000^3161 ≤ 44145754723689^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392358077 10000000000 44145754723689 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261017117/1250000000 : ℝ)^4185 ≤ (2514352546657/20000000000000 : ℝ)^3161 := by
    have hnat : (261017117 : ℕ)^4185*20000000000000^3161 ≤ 2514352546657^3161*1250000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261017117 1250000000 2514352546657 20000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328129873/2500000000 : ℝ), (5392358077/10000000000 : ℝ), (-261017117/1250000000 : ℝ)] ![(43282482528653/100000000000000 : ℝ), (44145754723689/100000000000000 : ℝ), (2514352546657/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328129873/2500000000 : ℝ)|^4185 ≤ (43282482528653/100000000000000 : ℝ)^3161
        have hw : |(1328129873/2500000000 : ℝ)|=(1328129873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392358077/10000000000 : ℝ)|^4185 ≤ (44145754723689/100000000000000 : ℝ)^3161
        have hw : |(5392358077/10000000000 : ℝ)|=(5392358077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-261017117/1250000000 : ℝ)|^4185 ≤ (2514352546657/20000000000000 : ℝ)^3161
        have hw : |(-261017117/1250000000 : ℝ)|=(261017117/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s6_7 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (34060637/78125000 : ℝ)*x 0 + (4487787157/10000000000 : ℝ)*x 1 + (847072341/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34060637/78125000 : ℝ)^4185 ≤ (8329278355529/25000000000000 : ℝ)^3161 := by
    have hnat : (34060637 : ℕ)^4185*25000000000000^3161 ≤ 8329278355529^3161*78125000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34060637 78125000 8329278355529 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4487787157/10000000000 : ℝ)^4185 ≤ (692370809859/2000000000000 : ℝ)^3161 := by
    have hnat : (4487787157 : ℕ)^4185*2000000000000^3161 ≤ 692370809859^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487787157 10000000000 692370809859 2000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (847072341/2000000000 : ℝ)^4185 ≤ (400804325771/1250000000000 : ℝ)^3161 := by
    have hnat : (847072341 : ℕ)^4185*1250000000000^3161 ≤ 400804325771^3161*2000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847072341 2000000000 400804325771 1250000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34060637/78125000 : ℝ), (4487787157/10000000000 : ℝ), (847072341/2000000000 : ℝ)] ![(8329278355529/25000000000000 : ℝ), (692370809859/2000000000000 : ℝ), (400804325771/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34060637/78125000 : ℝ)|^4185 ≤ (8329278355529/25000000000000 : ℝ)^3161
        have hw : |(34060637/78125000 : ℝ)|=(34060637/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4487787157/10000000000 : ℝ)|^4185 ≤ (692370809859/2000000000000 : ℝ)^3161
        have hw : |(4487787157/10000000000 : ℝ)|=(4487787157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(847072341/2000000000 : ℝ)|^4185 ≤ (400804325771/1250000000000 : ℝ)^3161
        have hw : |(847072341/2000000000 : ℝ)|=(847072341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1177_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5683/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (356/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (563/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14103/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5683/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14103/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5683/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14103/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5683/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14103/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5683/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14103/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5683/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14103/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5683/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5683/50000 : ℝ) ^ (8369/2048 : ℝ) ≤ (553185453786217/4000000000000000000 : ℝ) := by
    have hpowers : (5683/50000 : ℝ)^8369 ≤ (553185453786217/4000000000000000000 : ℝ)^2048 := by
      have hnat : (5683 : ℕ)^8369*4000000000000000000^2048 ≤ 553185453786217^2048*50000^8369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5683 50000 553185453786217 4000000000000000000 8369 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5683/50000 : ℝ)) (X := (553185453786217/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14103/100000 : ℝ) ^ (8369/2048 : ℝ) ≤ (16699159400914039/50000000000000000000 : ℝ) := by
    have hpowers : (14103/100000 : ℝ)^8369 ≤ (16699159400914039/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14103 : ℕ)^8369*50000000000000000000^2048 ≤ 16699159400914039^2048*100000^8369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14103 100000 16699159400914039 50000000000000000000 8369 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14103/100000 : ℝ)) (X := (16699159400914039/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000553185453786217/2000000000000000000 : ℝ) ≤ (5000338393323769/5000000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (2000553185453786217/2000000000000000000 : ℝ)^2048 ≤ (5000338393323769/5000000000000000 : ℝ)^8369 := by
      have hnat : (2000553185453786217 : ℕ)^2048*5000000000000000^8369 ≤ 5000338393323769^8369*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000553185453786217 2000000000000000000 5000338393323769 5000000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000338393323769/5000000000000000 : ℝ)) (X := (2000553185453786217/2000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047227955146483503/100000000000000000000 : ℝ) ≤ (5000577760820031/5000000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (100047227955146483503/100000000000000000000 : ℝ)^2048 ≤ (5000577760820031/5000000000000000 : ℝ)^8369 := by
      have hnat : (100047227955146483503 : ℕ)^2048*5000000000000000^8369 ≤ 5000577760820031^8369*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047227955146483503 100000000000000000000 5000577760820031 5000000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000577760820031/5000000000000000 : ℝ)) (X := (100047227955146483503/100000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016699159400914039/25000000000000000000 : ℝ) ≤ (5000817128316293/5000000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (25016699159400914039/25000000000000000000 : ℝ)^2048 ≤ (5000817128316293/5000000000000000 : ℝ)^8369 := by
      have hnat : (25016699159400914039 : ℕ)^2048*5000000000000000^8369 ≤ 5000817128316293^8369*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016699159400914039 25000000000000000000 5000817128316293 5000000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000817128316293/5000000000000000 : ℝ)) (X := (25016699159400914039/25000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(553185453786217/4000000000000000000 : ℝ) ≤ ((13680484880602127969/13685000000000000000 : ℝ)+2*(119683748131/68425000000000 : ℝ)*(5683/50000 : ℝ))^(8369/2048 : ℝ) := by
    rw [show (13680484880602127969/13685000000000000000 : ℝ)+2*(119683748131/68425000000000 : ℝ)*(5683/50000 : ℝ)=(5000338393323769/5000000000000000 : ℝ) by norm_num, show 1+2*(553185453786217/4000000000000000000 : ℝ)=(2000553185453786217/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16699159400914039/50000000000000000000 : ℝ)+(553185453786217/4000000000000000000 : ℝ) ≤ ((13680484880602127969/13685000000000000000 : ℝ)+(119683748131/68425000000000 : ℝ)*((14103/100000 : ℝ)+(5683/50000 : ℝ)))^(8369/2048 : ℝ) := by
    rw [show (13680484880602127969/13685000000000000000 : ℝ)+(119683748131/68425000000000 : ℝ)*((14103/100000 : ℝ)+(5683/50000 : ℝ))=(5000577760820031/5000000000000000 : ℝ) by norm_num, show 1+(16699159400914039/50000000000000000000 : ℝ)+(553185453786217/4000000000000000000 : ℝ)=(100047227955146483503/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16699159400914039/50000000000000000000 : ℝ) ≤ ((13680484880602127969/13685000000000000000 : ℝ)+2*(119683748131/68425000000000 : ℝ)*(14103/100000 : ℝ))^(8369/2048 : ℝ) := by
    rw [show (13680484880602127969/13685000000000000000 : ℝ)+2*(119683748131/68425000000000 : ℝ)*(14103/100000 : ℝ)=(5000817128316293/5000000000000000 : ℝ) by norm_num, show 1+2*(16699159400914039/50000000000000000000 : ℝ)=(25016699159400914039/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13680484880602127969/13685000000000000000 : ℝ)*(X 1 0+X 2 0)+(119683748131/68425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (5683/50000 : ℝ)) (hi := (14103/100000 : ℝ)) (c := (13680484880602127969/13685000000000000000 : ℝ)) (alpha := (119683748131/68425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13680484880602127969/13685000000000000000 : ℝ)*(X 0 1+X 2 1)+(119683748131/68425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (5683/50000 : ℝ)) (hi := (14103/100000 : ℝ)) (c := (13680484880602127969/13685000000000000000 : ℝ)) (alpha := (119683748131/68425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13680484880602127969/13685000000000000000 : ℝ)*(X 0 2+X 1 2)+(119683748131/68425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (5683/50000 : ℝ)) (hi := (14103/100000 : ℝ)) (c := (13680484880602127969/13685000000000000000 : ℝ)) (alpha := (119683748131/68425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-537558593/2500000000 : ℝ)*X 0 0+(5392679101/10000000000 : ℝ)*X 0 1+(5266023283/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668086291/1250000000 : ℝ)*X 1 0+(-553617929/2500000000 : ℝ)*X 1 1+(2633011663/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344690427/10000000000 : ℝ)*X 2 0+(2633011583/5000000000 : ℝ)*X 2 1+(-2214471797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((174390077/400000000 : ℝ)*X 0 0+(2117359107/5000000000 : ℝ)*X 0 1+(561053523/1250000000 : ℝ)*X 0 2+(174390077/400000000 : ℝ)*X 1 0+(2117359107/5000000000 : ℝ)*X 1 1+(561053523/1250000000 : ℝ)*X 1 2+(174390077/400000000 : ℝ)*X 2 0+(2117359107/5000000000 : ℝ)*X 2 1+(561053523/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-268779909/1250000000 : ℝ)*X 0 0+(5266343241/10000000000 : ℝ)*X 0 1+(84255593/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664064939/1250000000 : ℝ)*X 1 0+(-1044068491/5000000000 : ℝ)*X 1 1+(5392358023/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328129873/2500000000 : ℝ)*X 2 0+(5392358077/10000000000 : ℝ)*X 2 1+(-261017117/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((34060637/78125000 : ℝ)*X 0 0+(4487787157/10000000000 : ℝ)*X 0 1+(847072341/2000000000 : ℝ)*X 0 2+(34060637/78125000 : ℝ)*X 1 0+(4487787157/10000000000 : ℝ)*X 1 1+(847072341/2000000000 : ℝ)*X 1 2+(34060637/78125000 : ℝ)*X 2 0+(4487787157/10000000000 : ℝ)*X 2 1+(847072341/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (487248931920528354817877013/48875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (451045539/25000000000000 : ℝ)*(base19) + (198048209/12500000000000 : ℝ)*(base23) + (97819937/50000000000000 : ℝ)*(lower2) + (39292027/10000000000000 : ℝ)*(upper3) + (2435639/12500000000000 : ℝ)*(upper5) + (2959265944126913/50000000000000 : ℝ)*(major0) + (2959265944126913/50000000000000 : ℝ)*(major1) + (2959265944126913/50000000000000 : ℝ)*(major2) + (986932918944631/12500000000000 : ℝ)*(sp0) + (3947750369496651/50000000000000 : ℝ)*(sp1) + (3947750479394893/50000000000000 : ℝ)*(sp2) + (985382368645627/25000000000000 : ℝ)*(sp3) + (3919161841/10000000000000 : ℝ)*(sp4) + (31426440091/100000000000000 : ℝ)*(sp7) + (1970780450511299/50000000000000 : ℝ)*(f.failure) + (3947751271587729/50000000000000 : ℝ)*(f.sum) + (18547942917169/3421250000000000000000000000 : ℝ)*base66 + (128620290028720303/684250000000000000000000000000000 : ℝ)*base68 + (6881566890936779697/684250000000000000000000000000000 : ℝ)*base69 + (4519191207847470303/684250000000000000000000000000000 : ℝ)*base72 + (1419913375429/13685000000000000000000000000 : ℝ)*base73 + (1401907191282220303/684250000000000000000000000000000 : ℝ)*base76 + (2523504623882970303/684250000000000000000000000000000 : ℝ)*base78 + (906881361004779697/684250000000000000000000000000000 : ℝ)*base79 + (58648880809901/13685000000000000000000000000 : ℝ)*base82 + (23200829/2500000000000000000000 : ℝ)*base90 + (23200829/2500000000000000000000 : ℝ)*base92 + (23200829/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (217267074533004344567116149/48875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7899011/1562500000000 : ℝ)*(base19) + (135049911/20000000000000 : ℝ)*(base23) + (113274189/100000000000000 : ℝ)*(upper3) + (75695627/100000000000000 : ℝ)*(lower4) + (5056217/10000000000000 : ℝ)*(upper5) + (5948571355381151/100000000000000 : ℝ)*(major0) + (5948571355381151/100000000000000 : ℝ)*(major1) + (5948571355381151/100000000000000 : ℝ)*(major2) + (13931376087/100000000000000 : ℝ)*(sp1) + (4672178947/20000000000000 : ℝ)*(sp2) + (1983894074206641/25000000000000 : ℝ)*(sp4) + (7935561859913773/100000000000000 : ℝ)*(sp5) + (7935552260682273/100000000000000 : ℝ)*(sp6) + (792313253151397/20000000000000 : ℝ)*(sp7) + (792313253151397/20000000000000 : ℝ)*(f.failure) + (1983894074206641/25000000000000 : ℝ)*(f.sum) + (974181166643/488750000000000000000000000 : ℝ)*base65 + (1553880421321744617/195500000000000000000000000000000 : ℝ)*base67 + (3379322418049744617/195500000000000000000000000000000 : ℝ)*base69 + (1112879594885244617/195500000000000000000000000000000 : ℝ)*base71 + (3087758606253/1955000000000000000000000000 : ℝ)*base74 + (5608976611908244617/195500000000000000000000000000000 : ℝ)*base75 + (689853636594255383/195500000000000000000000000000000 : ℝ)*base78 + (5020281907403244617/195500000000000000000000000000000 : ℝ)*base79 + (3209799153161/977500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (8944987/1000000000000000000000 : ℝ)*base90 + (8944987/1000000000000000000000 : ℝ)*base92 + (8944987/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1177_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5683/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (563/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1177_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1177_s7_0 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2150259907/10000000000 : ℝ)*x 0 + (53924103/100000000 : ℝ)*x 1 + (1316568763/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150259907/10000000000 : ℝ)^4185 ≤ (13069309998483/100000000000000 : ℝ)^3161 := by
    have hnat : (2150259907 : ℕ)^4185*100000000000000^3161 ≤ 13069309998483^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150259907 10000000000 13069309998483 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53924103/100000000 : ℝ)^4185 ≤ (11036580189803/25000000000000 : ℝ)^3161 := by
    have hnat : (53924103 : ℕ)^4185*25000000000000^3161 ≤ 11036580189803^3161*100000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53924103 100000000 11036580189803 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316568763/2500000000 : ℝ)^4185 ≤ (42784369222611/100000000000000 : ℝ)^3161 := by
    have hnat : (1316568763 : ℕ)^4185*100000000000000^3161 ≤ 42784369222611^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316568763 2500000000 42784369222611 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2150259907/10000000000 : ℝ), (53924103/100000000 : ℝ), (1316568763/2500000000 : ℝ)] ![(13069309998483/100000000000000 : ℝ), (11036580189803/25000000000000 : ℝ), (42784369222611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2150259907/10000000000 : ℝ)|^4185 ≤ (13069309998483/100000000000000 : ℝ)^3161
        have hw : |(-2150259907/10000000000 : ℝ)|=(2150259907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53924103/100000000 : ℝ)|^4185 ≤ (11036580189803/25000000000000 : ℝ)^3161
        have hw : |(53924103/100000000 : ℝ)|=(53924103/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316568763/2500000000 : ℝ)|^4185 ≤ (42784369222611/100000000000000 : ℝ)^3161
        have hw : |(1316568763/2500000000 : ℝ)|=(1316568763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s7_1 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336155483/2500000000 : ℝ)*x 0 + (-2214229397/10000000000 : ℝ)*x 1 + (5266275073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336155483/2500000000 : ℝ)^4185 ≤ (1745163823701/4000000000000 : ℝ)^3161 := by
    have hnat : (1336155483 : ℕ)^4185*4000000000000^3161 ≤ 1745163823701^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336155483 2500000000 1745163823701 4000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2214229397/10000000000 : ℝ)^4185 ≤ (13586534943719/100000000000000 : ℝ)^3161 := by
    have hnat : (2214229397 : ℕ)^4185*100000000000000^3161 ≤ 13586534943719^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214229397 10000000000 13586534943719 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266275073/10000000000 : ℝ)^4185 ≤ (5348046181061/12500000000000 : ℝ)^3161 := by
    have hnat : (5266275073 : ℕ)^4185*12500000000000^3161 ≤ 5348046181061^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266275073 10000000000 5348046181061 12500000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336155483/2500000000 : ℝ), (-2214229397/10000000000 : ℝ), (5266275073/10000000000 : ℝ)] ![(1745163823701/4000000000000 : ℝ), (13586534943719/100000000000000 : ℝ), (5348046181061/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336155483/2500000000 : ℝ)|^4185 ≤ (1745163823701/4000000000000 : ℝ)^3161
        have hw : |(1336155483/2500000000 : ℝ)|=(1336155483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2214229397/10000000000 : ℝ)|^4185 ≤ (13586534943719/100000000000000 : ℝ)^3161
        have hw : |(-2214229397/10000000000 : ℝ)|=(2214229397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266275073/10000000000 : ℝ)|^4185 ≤ (5348046181061/12500000000000 : ℝ)^3161
        have hw : |(5266275073/10000000000 : ℝ)|=(5266275073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s7_2 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668077743/1250000000 : ℝ)*x 0 + (5266275069/10000000000 : ℝ)*x 1 + (-1107114693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668077743/1250000000 : ℝ)^4185 ≤ (43629095722217/100000000000000 : ℝ)^3161 := by
    have hnat : (668077743 : ℕ)^4185*100000000000000^3161 ≤ 43629095722217^3161*1250000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668077743 1250000000 43629095722217 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266275069/10000000000 : ℝ)^4185 ≤ (5348046175683/12500000000000 : ℝ)^3161 := by
    have hnat : (5266275069 : ℕ)^4185*12500000000000^3161 ≤ 5348046175683^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266275069 10000000000 5348046175683 12500000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1107114693/5000000000 : ℝ)^4185 ≤ (13586534854357/100000000000000 : ℝ)^3161 := by
    have hnat : (1107114693 : ℕ)^4185*100000000000000^3161 ≤ 13586534854357^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107114693 5000000000 13586534854357 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668077743/1250000000 : ℝ), (5266275069/10000000000 : ℝ), (-1107114693/5000000000 : ℝ)] ![(43629095722217/100000000000000 : ℝ), (5348046175683/12500000000000 : ℝ), (13586534854357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668077743/1250000000 : ℝ)|^4185 ≤ (43629095722217/100000000000000 : ℝ)^3161
        have hw : |(668077743/1250000000 : ℝ)|=(668077743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266275069/10000000000 : ℝ)|^4185 ≤ (5348046175683/12500000000000 : ℝ)^3161
        have hw : |(5266275069/10000000000 : ℝ)|=(5266275069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1107114693/5000000000 : ℝ)|^4185 ≤ (13586534854357/100000000000000 : ℝ)^3161
        have hw : |(-1107114693/5000000000 : ℝ)|=(1107114693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s7_3 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4359765011/10000000000 : ℝ)*x 0 + (2117619117/5000000000 : ℝ)*x 1 + (448790489/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359765011/10000000000 : ℝ)^4185 ≤ (16658574290313/50000000000000 : ℝ)^3161 := by
    have hnat : (4359765011 : ℕ)^4185*50000000000000^3161 ≤ 16658574290313^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359765011 10000000000 16658574290313 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117619117/5000000000 : ℝ)^4185 ≤ (32063108503107/100000000000000 : ℝ)^3161 := by
    have hnat : (2117619117 : ℕ)^4185*100000000000000^3161 ≤ 32063108503107^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117619117 5000000000 32063108503107 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (448790489/1000000000 : ℝ)^4185 ≤ (34619742888957/100000000000000 : ℝ)^3161 := by
    have hnat : (448790489 : ℕ)^4185*100000000000000^3161 ≤ 34619742888957^3161*1000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448790489 1000000000 34619742888957 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359765011/10000000000 : ℝ), (2117619117/5000000000 : ℝ), (448790489/1000000000 : ℝ)] ![(16658574290313/50000000000000 : ℝ), (32063108503107/100000000000000 : ℝ), (34619742888957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359765011/10000000000 : ℝ)|^4185 ≤ (16658574290313/50000000000000 : ℝ)^3161
        have hw : |(4359765011/10000000000 : ℝ)|=(4359765011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2117619117/5000000000 : ℝ)|^4185 ≤ (32063108503107/100000000000000 : ℝ)^3161
        have hw : |(2117619117/5000000000 : ℝ)|=(2117619117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(448790489/1000000000 : ℝ)|^4185 ≤ (34619742888957/100000000000000 : ℝ)^3161
        have hw : |(448790489/1000000000 : ℝ)|=(448790489/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s7_4 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-430052941/2000000000 : ℝ)*x 0 + (1053318489/2000000000 : ℝ)*x 1 + (1348022941/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430052941/2000000000 : ℝ)^4185 ≤ (2613869721577/20000000000000 : ℝ)^3161 := by
    have hnat : (430052941 : ℕ)^4185*20000000000000^3161 ≤ 2613869721577^3161*2000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430052941 2000000000 2613869721577 20000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053318489/2000000000 : ℝ)^4185 ≤ (21393891574473/50000000000000 : ℝ)^3161 := by
    have hnat : (1053318489 : ℕ)^4185*50000000000000^3161 ≤ 21393891574473^3161*2000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053318489 2000000000 21393891574473 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348022941/2500000000 : ℝ)^4185 ≤ (44142868233527/100000000000000 : ℝ)^3161 := by
    have hnat : (1348022941 : ℕ)^4185*100000000000000^3161 ≤ 44142868233527^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348022941 2500000000 44142868233527 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-430052941/2000000000 : ℝ), (1053318489/2000000000 : ℝ), (1348022941/2500000000 : ℝ)] ![(2613869721577/20000000000000 : ℝ), (21393891574473/50000000000000 : ℝ), (44142868233527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-430052941/2000000000 : ℝ)|^4185 ≤ (2613869721577/20000000000000 : ℝ)^3161
        have hw : |(-430052941/2000000000 : ℝ)|=(430052941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053318489/2000000000 : ℝ)|^4185 ≤ (21393891574473/50000000000000 : ℝ)^3161
        have hw : |(1053318489/2000000000 : ℝ)|=(1053318489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348022941/2500000000 : ℝ)|^4185 ≤ (44142868233527/100000000000000 : ℝ)^3161
        have hw : |(1348022941/2500000000 : ℝ)|=(1348022941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s7_5 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656291659/5000000000 : ℝ)*x 0 + (-1044206343/5000000000 : ℝ)*x 1 + (1348022941/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656291659/5000000000 : ℝ)^4185 ≤ (43283170992383/100000000000000 : ℝ)^3161 := by
    have hnat : (2656291659 : ℕ)^4185*100000000000000^3161 ≤ 43283170992383^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656291659 5000000000 43283170992383 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044206343/5000000000 : ℝ)^4185 ≤ (6286980380027/50000000000000 : ℝ)^3161 := by
    have hnat : (1044206343 : ℕ)^4185*50000000000000^3161 ≤ 6286980380027^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044206343 5000000000 6286980380027 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348022941/2500000000 : ℝ)^4185 ≤ (44142868233527/100000000000000 : ℝ)^3161 := by
    have hnat : (1348022941 : ℕ)^4185*100000000000000^3161 ≤ 44142868233527^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348022941 2500000000 44142868233527 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656291659/5000000000 : ℝ), (-1044206343/5000000000 : ℝ), (1348022941/2500000000 : ℝ)] ![(43283170992383/100000000000000 : ℝ), (6286980380027/50000000000000 : ℝ), (44142868233527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656291659/5000000000 : ℝ)|^4185 ≤ (43283170992383/100000000000000 : ℝ)^3161
        have hw : |(2656291659/5000000000 : ℝ)|=(2656291659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1044206343/5000000000 : ℝ)|^4185 ≤ (6286980380027/50000000000000 : ℝ)^3161
        have hw : |(-1044206343/5000000000 : ℝ)|=(1044206343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348022941/2500000000 : ℝ)|^4185 ≤ (44142868233527/100000000000000 : ℝ)^3161
        have hw : |(1348022941/2500000000 : ℝ)|=(1348022941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s7_6 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312583307/10000000000 : ℝ)*x 0 + (1348022943/2500000000 : ℝ)*x 1 + (-208841269/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312583307/10000000000 : ℝ)^4185 ≤ (4328317087373/10000000000000 : ℝ)^3161 := by
    have hnat : (5312583307 : ℕ)^4185*10000000000000^3161 ≤ 4328317087373^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312583307 10000000000 4328317087373 10000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348022943/2500000000 : ℝ)^4185 ≤ (11035717080059/25000000000000 : ℝ)^3161 := by
    have hnat : (1348022943 : ℕ)^4185*25000000000000^3161 ≤ 11035717080059^3161*2500000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348022943 2500000000 11035717080059 25000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208841269/1000000000 : ℝ)^4185 ≤ (12573960791939/100000000000000 : ℝ)^3161 := by
    have hnat : (208841269 : ℕ)^4185*100000000000000^3161 ≤ 12573960791939^3161*1000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208841269 1000000000 12573960791939 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312583307/10000000000 : ℝ), (1348022943/2500000000 : ℝ), (-208841269/1000000000 : ℝ)] ![(4328317087373/10000000000000 : ℝ), (11035717080059/25000000000000 : ℝ), (12573960791939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312583307/10000000000 : ℝ)|^4185 ≤ (4328317087373/10000000000000 : ℝ)^3161
        have hw : |(5312583307/10000000000 : ℝ)|=(5312583307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348022943/2500000000 : ℝ)|^4185 ≤ (11035717080059/25000000000000 : ℝ)^3161
        have hw : |(1348022943/2500000000 : ℝ)|=(1348022943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-208841269/1000000000 : ℝ)|^4185 ≤ (12573960791939/100000000000000 : ℝ)^3161
        have hw : |(-208841269/1000000000 : ℝ)|=(208841269/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s7_7 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (435977461/1000000000 : ℝ)*x 0 + (2243634579/5000000000 : ℝ)*x 1 + (2117938147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435977461/1000000000 : ℝ)^4185 ≤ (16658622849551/50000000000000 : ℝ)^3161 := by
    have hnat : (435977461 : ℕ)^4185*50000000000000^3161 ≤ 16658622849551^3161*1000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435977461 1000000000 16658622849551 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243634579/5000000000 : ℝ)^4185 ≤ (6922650067897/20000000000000 : ℝ)^3161 := by
    have hnat : (2243634579 : ℕ)^4185*20000000000000^3161 ≤ 6922650067897^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243634579 5000000000 6922650067897 20000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2117938147/5000000000 : ℝ)^4185 ≤ (16034751974753/50000000000000 : ℝ)^3161 := by
    have hnat : (2117938147 : ℕ)^4185*50000000000000^3161 ≤ 16034751974753^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117938147 5000000000 16034751974753 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435977461/1000000000 : ℝ), (2243634579/5000000000 : ℝ), (2117938147/5000000000 : ℝ)] ![(16658622849551/50000000000000 : ℝ), (6922650067897/20000000000000 : ℝ), (16034751974753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435977461/1000000000 : ℝ)|^4185 ≤ (16658622849551/50000000000000 : ℝ)^3161
        have hw : |(435977461/1000000000 : ℝ)|=(435977461/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2243634579/5000000000 : ℝ)|^4185 ≤ (6922650067897/20000000000000 : ℝ)^3161
        have hw : |(2243634579/5000000000 : ℝ)|=(2243634579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2117938147/5000000000 : ℝ)|^4185 ≤ (16034751974753/50000000000000 : ℝ)^3161
        have hw : |(2117938147/5000000000 : ℝ)|=(2117938147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1177_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (5699/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1407/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (563/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (356/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (563/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (356/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (563/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (356/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (563/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (356/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (563/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (356/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (563/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (356/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (356/3125 : ℝ) ^ (8369/2048 : ℝ) ≤ (13959370080215773/100000000000000000000 : ℝ) := by
    have hpowers : (356/3125 : ℝ)^8369 ≤ (13959370080215773/100000000000000000000 : ℝ)^2048 := by
      have hnat : (356 : ℕ)^8369*100000000000000000000^2048 ≤ 13959370080215773^2048*3125^8369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        356 3125 13959370080215773 100000000000000000000 8369 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (356/3125 : ℝ)) (X := (13959370080215773/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (563/4000 : ℝ) ^ (8369/2048 : ℝ) ≤ (4141022737225857/12500000000000000000 : ℝ) := by
    have hpowers : (563/4000 : ℝ)^8369 ≤ (4141022737225857/12500000000000000000 : ℝ)^2048 := by
      have hnat : (563 : ℕ)^8369*12500000000000000000^2048 ≤ 4141022737225857^2048*4000^8369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        563 4000 4141022737225857 12500000000000000000 8369 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (563/4000 : ℝ)) (X := (4141022737225857/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013959370080215773/50000000000000000000 : ℝ) ≤ (10000683134811911/10000000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (50013959370080215773/50000000000000000000 : ℝ)^2048 ≤ (10000683134811911/10000000000000000 : ℝ)^8369 := by
      have hnat : (50013959370080215773 : ℕ)^2048*10000000000000000^8369 ≤ 10000683134811911^8369*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013959370080215773 50000000000000000000 10000683134811911 10000000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000683134811911/10000000000000000 : ℝ)) (X := (50013959370080215773/50000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047087551978022629/100000000000000000000 : ℝ) ≤ (5000576043510231/5000000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (100047087551978022629/100000000000000000000 : ℝ)^2048 ≤ (5000576043510231/5000000000000000 : ℝ)^8369 := by
      have hnat : (100047087551978022629 : ℕ)^2048*5000000000000000^8369 ≤ 5000576043510231^8369*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047087551978022629 100000000000000000000 5000576043510231 5000000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000576043510231/5000000000000000 : ℝ)) (X := (100047087551978022629/100000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254141022737225857/6250000000000000000 : ℝ) ≤ (10001621039229013/10000000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (6254141022737225857/6250000000000000000 : ℝ)^2048 ≤ (10001621039229013/10000000000000000 : ℝ)^8369 := by
      have hnat : (6254141022737225857 : ℕ)^2048*10000000000000000^8369 ≤ 10001621039229013^8369*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254141022737225857 6250000000000000000 10001621039229013 10000000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001621039229013/10000000000000000 : ℝ)) (X := (6254141022737225857/6250000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13959370080215773/100000000000000000000 : ℝ) ≤ ((26821148243580731229/26830000000000000000 : ℝ)+2*(468952208551/268300000000000 : ℝ)*(356/3125 : ℝ))^(8369/2048 : ℝ) := by
    rw [show (26821148243580731229/26830000000000000000 : ℝ)+2*(468952208551/268300000000000 : ℝ)*(356/3125 : ℝ)=(10000683134811911/10000000000000000 : ℝ) by norm_num, show 1+2*(13959370080215773/100000000000000000000 : ℝ)=(50013959370080215773/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4141022737225857/12500000000000000000 : ℝ)+(13959370080215773/100000000000000000000 : ℝ) ≤ ((26821148243580731229/26830000000000000000 : ℝ)+(468952208551/268300000000000 : ℝ)*((563/4000 : ℝ)+(356/3125 : ℝ)))^(8369/2048 : ℝ) := by
    rw [show (26821148243580731229/26830000000000000000 : ℝ)+(468952208551/268300000000000 : ℝ)*((563/4000 : ℝ)+(356/3125 : ℝ))=(5000576043510231/5000000000000000 : ℝ) by norm_num, show 1+(4141022737225857/12500000000000000000 : ℝ)+(13959370080215773/100000000000000000000 : ℝ)=(100047087551978022629/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4141022737225857/12500000000000000000 : ℝ) ≤ ((26821148243580731229/26830000000000000000 : ℝ)+2*(468952208551/268300000000000 : ℝ)*(563/4000 : ℝ))^(8369/2048 : ℝ) := by
    rw [show (26821148243580731229/26830000000000000000 : ℝ)+2*(468952208551/268300000000000 : ℝ)*(563/4000 : ℝ)=(10001621039229013/10000000000000000 : ℝ) by norm_num, show 1+2*(4141022737225857/12500000000000000000 : ℝ)=(6254141022737225857/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26821148243580731229/26830000000000000000 : ℝ)*(X 1 0+X 2 0)+(468952208551/268300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (356/3125 : ℝ)) (hi := (563/4000 : ℝ)) (c := (26821148243580731229/26830000000000000000 : ℝ)) (alpha := (468952208551/268300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26821148243580731229/26830000000000000000 : ℝ)*(X 0 1+X 2 1)+(468952208551/268300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (356/3125 : ℝ)) (hi := (563/4000 : ℝ)) (c := (26821148243580731229/26830000000000000000 : ℝ)) (alpha := (468952208551/268300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26821148243580731229/26830000000000000000 : ℝ)*(X 0 2+X 1 2)+(468952208551/268300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (356/3125 : ℝ)) (hi := (563/4000 : ℝ)) (c := (26821148243580731229/26830000000000000000 : ℝ)) (alpha := (468952208551/268300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2150259907/10000000000 : ℝ)*X 0 0+(53924103/100000000 : ℝ)*X 0 1+(1316568763/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336155483/2500000000 : ℝ)*X 1 0+(-2214229397/10000000000 : ℝ)*X 1 1+(5266275073/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668077743/1250000000 : ℝ)*X 2 0+(5266275069/10000000000 : ℝ)*X 2 1+(-1107114693/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4359765011/10000000000 : ℝ)*X 0 0+(2117619117/5000000000 : ℝ)*X 0 1+(448790489/1000000000 : ℝ)*X 0 2+(4359765011/10000000000 : ℝ)*X 1 0+(2117619117/5000000000 : ℝ)*X 1 1+(448790489/1000000000 : ℝ)*X 1 2+(4359765011/10000000000 : ℝ)*X 2 0+(2117619117/5000000000 : ℝ)*X 2 1+(448790489/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-430052941/2000000000 : ℝ)*X 0 0+(1053318489/2000000000 : ℝ)*X 0 1+(1348022941/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656291659/5000000000 : ℝ)*X 1 0+(-1044206343/5000000000 : ℝ)*X 1 1+(1348022941/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312583307/10000000000 : ℝ)*X 2 0+(1348022943/2500000000 : ℝ)*X 2 1+(-208841269/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((435977461/1000000000 : ℝ)*X 0 0+(2243634579/5000000000 : ℝ)*X 0 1+(2117938147/5000000000 : ℝ)*X 0 2+(435977461/1000000000 : ℝ)*X 1 0+(2243634579/5000000000 : ℝ)*X 1 1+(2117938147/5000000000 : ℝ)*X 1 2+(435977461/1000000000 : ℝ)*X 2 0+(2243634579/5000000000 : ℝ)*X 2 1+(2117938147/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4826515428079221252760332837/1341500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (729770187/100000000000000 : ℝ)*(base19) + (338514389/50000000000000 : ℝ)*(base23) + (18850969/50000000000000 : ℝ)*(lower2) + (93452389/100000000000000 : ℝ)*(upper3) + (62262563/100000000000000 : ℝ)*(upper5) + (5942922731553183/100000000000000 : ℝ)*(major0) + (5942922731553183/100000000000000 : ℝ)*(major1) + (5942922731553183/100000000000000 : ℝ)*(major2) + (7928019535363627/100000000000000 : ℝ)*(sp0) + (7928040158053381/100000000000000 : ℝ)*(sp1) + (7928040210794789/100000000000000 : ℝ)*(sp2) + (989448386402063/25000000000000 : ℝ)*(sp3) + (1067622997/5000000000000 : ℝ)*(sp4) + (10909746209/100000000000000 : ℝ)*(sp7) + (3957804455354461/100000000000000 : ℝ)*(f.failure) + (495502555488973/6250000000000 : ℝ)*(f.sum) + (12105007455769/6707500000000000000000000000 : ℝ)*base65 + (39249006006455751907/2683000000000000000000000000000000 : ℝ)*base67 + (3206793771155751907/2683000000000000000000000000000000 : ℝ)*base69 + (28428638815043751907/2683000000000000000000000000000000 : ℝ)*base71 + (6791434214819/6707500000000000000000000000 : ℝ)*base73 + (13049636707688751907/2683000000000000000000000000000000 : ℝ)*base75 + (59414880221551751907/2683000000000000000000000000000000 : ℝ)*base77 + (3467165664452751907/2683000000000000000000000000000000 : ℝ)*base79 + (10713902519547/13415000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (44532131/5000000000000000000000 : ℝ)*base90 + (44532131/5000000000000000000000 : ℝ)*base92 + (44532131/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (133971339965803976372733/13415000000000000000000000000 : ℝ) := by norm_num
    linear_combination (907464667/50000000000000 : ℝ)*(base19) + (985122499/50000000000000 : ℝ)*(base23) + (49612391/25000000000000 : ℝ)*(upper3) + (39376289/50000000000000 : ℝ)*(lower4) + (99136217/50000000000000 : ℝ)*(upper5) + (2986501405407907/50000000000000 : ℝ)*(major0) + (2986501405407907/50000000000000 : ℝ)*(major1) + (2986501405407907/50000000000000 : ℝ)*(major2) + (12674256759/25000000000000 : ℝ)*(sp1) + (853224663/1562500000000 : ℝ)*(sp2) + (7968168422215561/100000000000000 : ℝ)*(sp4) + (996014488782399/12500000000000 : ℝ)*(sp5) + (7968111845592131/100000000000000 : ℝ)*(sp6) + (62153701039479/1562500000000 : ℝ)*(sp7) + (62153701039479/1562500000000 : ℝ)*(f.failure) + (7968168422215561/100000000000000 : ℝ)*(f.sum) + (23678434496311/13415000000000000000000000000 : ℝ)*base66 + (6989407037705372297/1341500000000000000000000000000000 : ℝ)*base68 + (15916544247532127703/1341500000000000000000000000000000 : ℝ)*base69 + (3698981840917872297/1341500000000000000000000000000000 : ℝ)*base72 + (32961121083127/6707500000000000000000000000 : ℝ)*base73 + (7758039330384127703/1341500000000000000000000000000000 : ℝ)*base75 + (3761426425676627703/1341500000000000000000000000000000 : ℝ)*base77 + (13871196454947872297/1341500000000000000000000000000000 : ℝ)*base80 + (10322542033721/3353750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (441109/78125000000000000000 : ℝ)*base90 + (441109/78125000000000000000 : ℝ)*base92 + (441109/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1177_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5699/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1177_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1177_s8_0 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2150260597/10000000000 : ℝ)*x 0 + (2696179091/5000000000 : ℝ)*x 1 + (1053265411/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150260597/10000000000 : ℝ)^4185 ≤ (816832221931/6250000000000 : ℝ)^3161 := by
    have hnat : (2150260597 : ℕ)^4185*6250000000000^3161 ≤ 816832221931^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150260597 10000000000 816832221931 6250000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696179091/5000000000 : ℝ)^4185 ≤ (44145755861763/100000000000000 : ℝ)^3161 := by
    have hnat : (2696179091 : ℕ)^4185*100000000000000^3161 ≤ 44145755861763^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696179091 5000000000 44145755861763 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053265411/2000000000 : ℝ)^4185 ≤ (42784928570051/100000000000000 : ℝ)^3161 := by
    have hnat : (1053265411 : ℕ)^4185*100000000000000^3161 ≤ 42784928570051^3161*2000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053265411 2000000000 42784928570051 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2150260597/10000000000 : ℝ), (2696179091/5000000000 : ℝ), (1053265411/2000000000 : ℝ)] ![(816832221931/6250000000000 : ℝ), (44145755861763/100000000000000 : ℝ), (42784928570051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2150260597/10000000000 : ℝ)|^4185 ≤ (816832221931/6250000000000 : ℝ)^3161
        have hw : |(-2150260597/10000000000 : ℝ)|=(2150260597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696179091/5000000000 : ℝ)|^4185 ≤ (44145755861763/100000000000000 : ℝ)^3161
        have hw : |(2696179091/5000000000 : ℝ)|=(2696179091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053265411/2000000000 : ℝ)|^4185 ≤ (42784928570051/100000000000000 : ℝ)^3161
        have hw : |(1053265411/2000000000 : ℝ)|=(1053265411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s8_1 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344609913/10000000000 : ℝ)*x 0 + (-2214176523/10000000000 : ℝ)*x 1 + (5266327083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344609913/10000000000 : ℝ)^4185 ≤ (43628965695751/100000000000000 : ℝ)^3161 := by
    have hnat : (5344609913 : ℕ)^4185*100000000000000^3161 ≤ 43628965695751^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344609913 10000000000 43628965695751 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2214176523/10000000000 : ℝ)^4185 ≤ (6793052704857/50000000000000 : ℝ)^3161 := by
    have hnat : (2214176523 : ℕ)^4185*50000000000000^3161 ≤ 6793052704857^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214176523 10000000000 6793052704857 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266327083/10000000000 : ℝ)^4185 ≤ (21392464435611/50000000000000 : ℝ)^3161 := by
    have hnat : (5266327083 : ℕ)^4185*50000000000000^3161 ≤ 21392464435611^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266327083 10000000000 21392464435611 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344609913/10000000000 : ℝ), (-2214176523/10000000000 : ℝ), (5266327083/10000000000 : ℝ)] ![(43628965695751/100000000000000 : ℝ), (6793052704857/50000000000000 : ℝ), (21392464435611/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344609913/10000000000 : ℝ)|^4185 ≤ (43628965695751/100000000000000 : ℝ)^3161
        have hw : |(5344609913/10000000000 : ℝ)|=(5344609913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2214176523/10000000000 : ℝ)|^4185 ≤ (6793052704857/50000000000000 : ℝ)^3161
        have hw : |(-2214176523/10000000000 : ℝ)|=(2214176523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266327083/10000000000 : ℝ)|^4185 ≤ (21392464435611/50000000000000 : ℝ)^3161
        have hw : |(5266327083/10000000000 : ℝ)|=(5266327083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s8_2 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344609911/10000000000 : ℝ)*x 0 + (5266327063/10000000000 : ℝ)*x 1 + (-1107088277/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344609911/10000000000 : ℝ)^4185 ≤ (5453620709267/12500000000000 : ℝ)^3161 := by
    have hnat : (5344609911 : ℕ)^4185*12500000000000^3161 ≤ 5453620709267^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344609911 10000000000 5453620709267 12500000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266327063/10000000000 : ℝ)^4185 ≤ (427849286561/1000000000000 : ℝ)^3161 := by
    have hnat : (5266327063 : ℕ)^4185*1000000000000^3161 ≤ 427849286561^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266327063 10000000000 427849286561 1000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1107088277/5000000000 : ℝ)^4185 ≤ (13586105661549/100000000000000 : ℝ)^3161 := by
    have hnat : (1107088277 : ℕ)^4185*100000000000000^3161 ≤ 13586105661549^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107088277 5000000000 13586105661549 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344609911/10000000000 : ℝ), (5266327063/10000000000 : ℝ), (-1107088277/5000000000 : ℝ)] ![(5453620709267/12500000000000 : ℝ), (427849286561/1000000000000 : ℝ), (13586105661549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344609911/10000000000 : ℝ)|^4185 ≤ (5453620709267/12500000000000 : ℝ)^3161
        have hw : |(5344609911/10000000000 : ℝ)|=(5344609911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266327063/10000000000 : ℝ)|^4185 ≤ (427849286561/1000000000000 : ℝ)^3161
        have hw : |(5266327063/10000000000 : ℝ)|=(5266327063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1107088277/5000000000 : ℝ)|^4185 ≤ (13586105661549/100000000000000 : ℝ)^3161
        have hw : |(-1107088277/5000000000 : ℝ)|=(1107088277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s8_3 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10899419/25000000 : ℝ)*x 0 + (4235342177/10000000000 : ℝ)*x 1 + (897560063/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10899419/25000000 : ℝ)^4185 ≤ (33317174774987/100000000000000 : ℝ)^3161 := by
    have hnat : (10899419 : ℕ)^4185*100000000000000^3161 ≤ 33317174774987^3161*25000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10899419 25000000 33317174774987 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4235342177/10000000000 : ℝ)^4185 ≤ (256513202643/800000000000 : ℝ)^3161 := by
    have hnat : (4235342177 : ℕ)^4185*800000000000^3161 ≤ 256513202643^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235342177 10000000000 256513202643 800000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (897560063/2000000000 : ℝ)^4185 ≤ (17309337436927/50000000000000 : ℝ)^3161 := by
    have hnat : (897560063 : ℕ)^4185*50000000000000^3161 ≤ 17309337436927^3161*2000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897560063 2000000000 17309337436927 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10899419/25000000 : ℝ), (4235342177/10000000000 : ℝ), (897560063/2000000000 : ℝ)] ![(33317174774987/100000000000000 : ℝ), (256513202643/800000000000 : ℝ), (17309337436927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10899419/25000000 : ℝ)|^4185 ≤ (33317174774987/100000000000000 : ℝ)^3161
        have hw : |(10899419/25000000 : ℝ)|=(10899419/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4235342177/10000000000 : ℝ)|^4185 ≤ (256513202643/800000000000 : ℝ)^3161
        have hw : |(4235342177/10000000000 : ℝ)|=(4235342177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(897560063/2000000000 : ℝ)|^4185 ≤ (17309337436927/50000000000000 : ℝ)^3161
        have hw : |(897560063/2000000000 : ℝ)|=(897560063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s8_4 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-430053083/2000000000 : ℝ)*x 0 + (1053328791/2000000000 : ℝ)*x 1 + (2696020059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430053083/2000000000 : ℝ)^4185 ≤ (13069354321241/100000000000000 : ℝ)^3161 := by
    have hnat : (430053083 : ℕ)^4185*100000000000000^3161 ≤ 13069354321241^3161*2000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430053083 2000000000 13069354321241 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053328791/2000000000 : ℝ)^4185 ≤ (5348542150557/12500000000000 : ℝ)^3161 := by
    have hnat : (1053328791 : ℕ)^4185*12500000000000^3161 ≤ 5348542150557^3161*2000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053328791 2000000000 5348542150557 12500000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696020059/5000000000 : ℝ)^4185 ≤ (8828461692541/20000000000000 : ℝ)^3161 := by
    have hnat : (2696020059 : ℕ)^4185*20000000000000^3161 ≤ 8828461692541^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696020059 5000000000 8828461692541 20000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-430053083/2000000000 : ℝ), (1053328791/2000000000 : ℝ), (2696020059/5000000000 : ℝ)] ![(13069354321241/100000000000000 : ℝ), (5348542150557/12500000000000 : ℝ), (8828461692541/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-430053083/2000000000 : ℝ)|^4185 ≤ (13069354321241/100000000000000 : ℝ)^3161
        have hw : |(-430053083/2000000000 : ℝ)|=(430053083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053328791/2000000000 : ℝ)|^4185 ≤ (5348542150557/12500000000000 : ℝ)^3161
        have hw : |(1053328791/2000000000 : ℝ)|=(1053328791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696020059/5000000000 : ℝ)|^4185 ≤ (8828461692541/20000000000000 : ℝ)^3161
        have hw : |(2696020059/5000000000 : ℝ)|=(2696020059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s8_5 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062519561/2000000000 : ℝ)*x 0 + (-2088463343/10000000000 : ℝ)*x 1 + (5392040091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062519561/2000000000 : ℝ)^4185 ≤ (43283327257821/100000000000000 : ℝ)^3161 := by
    have hnat : (1062519561 : ℕ)^4185*100000000000000^3161 ≤ 43283327257821^3161*2000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062519561 2000000000 43283327257821 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2088463343/10000000000 : ℝ)^4185 ≤ (1571795570193/12500000000000 : ℝ)^3161 := by
    have hnat : (2088463343 : ℕ)^4185*12500000000000^3161 ≤ 1571795570193^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088463343 10000000000 1571795570193 12500000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392040091/10000000000 : ℝ)^4185 ≤ (44142308170063/100000000000000 : ℝ)^3161 := by
    have hnat : (5392040091 : ℕ)^4185*100000000000000^3161 ≤ 44142308170063^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392040091 10000000000 44142308170063 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062519561/2000000000 : ℝ), (-2088463343/10000000000 : ℝ), (5392040091/10000000000 : ℝ)] ![(43283327257821/100000000000000 : ℝ), (1571795570193/12500000000000 : ℝ), (44142308170063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062519561/2000000000 : ℝ)|^4185 ≤ (43283327257821/100000000000000 : ℝ)^3161
        have hw : |(1062519561/2000000000 : ℝ)|=(1062519561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2088463343/10000000000 : ℝ)|^4185 ≤ (1571795570193/12500000000000 : ℝ)^3161
        have hw : |(-2088463343/10000000000 : ℝ)|=(2088463343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392040091/10000000000 : ℝ)|^4185 ≤ (44142308170063/100000000000000 : ℝ)^3161
        have hw : |(5392040091/10000000000 : ℝ)|=(5392040091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s8_6 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656298851/5000000000 : ℝ)*x 0 + (674005021/1250000000 : ℝ)*x 1 + (-2088463377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656298851/5000000000 : ℝ)^4185 ≤ (43283326146801/100000000000000 : ℝ)^3161 := by
    have hnat : (2656298851 : ℕ)^4185*100000000000000^3161 ≤ 43283326146801^3161*5000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656298851 5000000000 43283326146801 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674005021/1250000000 : ℝ)^4185 ≤ (22071154502317/50000000000000 : ℝ)^3161 := by
    have hnat : (674005021 : ℕ)^4185*50000000000000^3161 ≤ 22071154502317^3161*1250000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674005021 1250000000 22071154502317 50000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2088463377/10000000000 : ℝ)^4185 ≤ (12574364832569/100000000000000 : ℝ)^3161 := by
    have hnat : (2088463377 : ℕ)^4185*100000000000000^3161 ≤ 12574364832569^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088463377 10000000000 12574364832569 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656298851/5000000000 : ℝ), (674005021/1250000000 : ℝ), (-2088463377/10000000000 : ℝ)] ![(43283326146801/100000000000000 : ℝ), (22071154502317/50000000000000 : ℝ), (12574364832569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656298851/5000000000 : ℝ)|^4185 ≤ (43283326146801/100000000000000 : ℝ)^3161
        have hw : |(2656298851/5000000000 : ℝ)|=(2656298851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674005021/1250000000 : ℝ)|^4185 ≤ (22071154502317/50000000000000 : ℝ)^3161
        have hw : |(674005021/1250000000 : ℝ)|=(674005021/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2088463377/10000000000 : ℝ)|^4185 ≤ (12574364832569/100000000000000 : ℝ)^3161
        have hw : |(-2088463377/10000000000 : ℝ)|=(2088463377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1177_s8_7 (p : ℝ) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4359777171/10000000000 : ℝ)*x 0 + (4487165569/10000000000 : ℝ)*x 1 + (16943917/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359777171/10000000000 : ℝ)^4185 ≤ (33317271610189/100000000000000 : ℝ)^3161 := by
    have hnat : (4359777171 : ℕ)^4185*100000000000000^3161 ≤ 33317271610189^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359777171 10000000000 33317271610189 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4487165569/10000000000 : ℝ)^4185 ≤ (4326524055353/12500000000000 : ℝ)^3161 := by
    have hnat : (4487165569 : ℕ)^4185*12500000000000^3161 ≤ 4326524055353^3161*10000000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487165569 10000000000 4326524055353 12500000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16943917/40000000 : ℝ)^4185 ≤ (32070535934331/100000000000000 : ℝ)^3161 := by
    have hnat : (16943917 : ℕ)^4185*100000000000000^3161 ≤ 32070535934331^3161*40000000^4185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16943917 40000000 32070535934331 100000000000000 4185 3161 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4185/1024 : ℝ)) 4185 3161 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359777171/10000000000 : ℝ), (4487165569/10000000000 : ℝ), (16943917/40000000 : ℝ)] ![(33317271610189/100000000000000 : ℝ), (4326524055353/12500000000000 : ℝ), (32070535934331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359777171/10000000000 : ℝ)|^4185 ≤ (33317271610189/100000000000000 : ℝ)^3161
        have hw : |(4359777171/10000000000 : ℝ)|=(4359777171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4487165569/10000000000 : ℝ)|^4185 ≤ (4326524055353/12500000000000 : ℝ)^3161
        have hw : |(4487165569/10000000000 : ℝ)|=(4487165569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16943917/40000000 : ℝ)|^4185 ≤ (32070535934331/100000000000000 : ℝ)^3161
        have hw : |(16943917/40000000 : ℝ)|=(16943917/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1177_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5699/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11399/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14069/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1407/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5699/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1407/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5699/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1407/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5699/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1407/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5699/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1407/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5699/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1407/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5699/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5699/50000 : ℝ) ^ (8369/2048 : ℝ) ≤ (13989438713313691/100000000000000000000 : ℝ) := by
    have hpowers : (5699/50000 : ℝ)^8369 ≤ (13989438713313691/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5699 : ℕ)^8369*100000000000000000000^2048 ≤ 13989438713313691^2048*50000^8369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5699 50000 13989438713313691 100000000000000000000 8369 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5699/50000 : ℝ)) (X := (13989438713313691/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1407/10000 : ℝ) ^ (8369/2048 : ℝ) ≤ (33080117364789171/100000000000000000000 : ℝ) := by
    have hpowers : (1407/10000 : ℝ)^8369 ≤ (33080117364789171/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1407 : ℕ)^8369*100000000000000000000^2048 ≤ 33080117364789171^2048*10000^8369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1407 10000 33080117364789171 100000000000000000000 8369 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1407/10000 : ℝ)) (X := (33080117364789171/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013989438713313691/50000000000000000000 : ℝ) ≤ (10000684606136191/10000000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (50013989438713313691/50000000000000000000 : ℝ)^2048 ≤ (10000684606136191/10000000000000000 : ℝ)^8369 := by
      have hnat : (50013989438713313691 : ℕ)^2048*10000000000000000^8369 ≤ 10000684606136191^8369*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013989438713313691 50000000000000000000 10000684606136191 10000000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000684606136191/10000000000000000 : ℝ)) (X := (50013989438713313691/50000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023534778039051431/50000000000000000000 : ℝ) ≤ (2500287911698647/2500000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (50023534778039051431/50000000000000000000 : ℝ)^2048 ≤ (2500287911698647/2500000000000000 : ℝ)^8369 := by
      have hnat : (50023534778039051431 : ℕ)^2048*2500000000000000^8369 ≤ 2500287911698647^8369*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023534778039051431 50000000000000000000 2500287911698647 2500000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500287911698647/2500000000000000 : ℝ)) (X := (50023534778039051431/50000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033080117364789171/50000000000000000000 : ℝ) ≤ (2000323737490597/2000000000000000 : ℝ) ^ (8369/2048 : ℝ) := by
    have hpowers : (50033080117364789171/50000000000000000000 : ℝ)^2048 ≤ (2000323737490597/2000000000000000 : ℝ)^8369 := by
      have hnat : (50033080117364789171 : ℕ)^2048*2000000000000000^8369 ≤ 2000323737490597^8369*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033080117364789171 50000000000000000000 2000323737490597 2000000000000000 2048 8369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000323737490597/2000000000000000 : ℝ)) (X := (50033080117364789171/50000000000000000000 : ℝ)) (by norm_num) 8369 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13989438713313691/100000000000000000000 : ℝ) ≤ ((1335559130437354217/1336000000000000000 : ℝ)+2*(467040658397/267200000000000 : ℝ)*(5699/50000 : ℝ))^(8369/2048 : ℝ) := by
    rw [show (1335559130437354217/1336000000000000000 : ℝ)+2*(467040658397/267200000000000 : ℝ)*(5699/50000 : ℝ)=(10000684606136191/10000000000000000 : ℝ) by norm_num, show 1+2*(13989438713313691/100000000000000000000 : ℝ)=(50013989438713313691/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33080117364789171/100000000000000000000 : ℝ)+(13989438713313691/100000000000000000000 : ℝ) ≤ ((1335559130437354217/1336000000000000000 : ℝ)+(467040658397/267200000000000 : ℝ)*((1407/10000 : ℝ)+(5699/50000 : ℝ)))^(8369/2048 : ℝ) := by
    rw [show (1335559130437354217/1336000000000000000 : ℝ)+(467040658397/267200000000000 : ℝ)*((1407/10000 : ℝ)+(5699/50000 : ℝ))=(2500287911698647/2500000000000000 : ℝ) by norm_num, show 1+(33080117364789171/100000000000000000000 : ℝ)+(13989438713313691/100000000000000000000 : ℝ)=(50023534778039051431/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33080117364789171/100000000000000000000 : ℝ) ≤ ((1335559130437354217/1336000000000000000 : ℝ)+2*(467040658397/267200000000000 : ℝ)*(1407/10000 : ℝ))^(8369/2048 : ℝ) := by
    rw [show (1335559130437354217/1336000000000000000 : ℝ)+2*(467040658397/267200000000000 : ℝ)*(1407/10000 : ℝ)=(2000323737490597/2000000000000000 : ℝ) by norm_num, show 1+2*(33080117364789171/100000000000000000000 : ℝ)=(50033080117364789171/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1335559130437354217/1336000000000000000 : ℝ)*(X 1 0+X 2 0)+(467040658397/267200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (5699/50000 : ℝ)) (hi := (1407/10000 : ℝ)) (c := (1335559130437354217/1336000000000000000 : ℝ)) (alpha := (467040658397/267200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1335559130437354217/1336000000000000000 : ℝ)*(X 0 1+X 2 1)+(467040658397/267200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (5699/50000 : ℝ)) (hi := (1407/10000 : ℝ)) (c := (1335559130437354217/1336000000000000000 : ℝ)) (alpha := (467040658397/267200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1335559130437354217/1336000000000000000 : ℝ)*(X 0 2+X 1 2)+(467040658397/267200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8369/2048 : ℝ)) (lo := (5699/50000 : ℝ)) (hi := (1407/10000 : ℝ)) (c := (1335559130437354217/1336000000000000000 : ℝ)) (alpha := (467040658397/267200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2150260597/10000000000 : ℝ)*X 0 0+(2696179091/5000000000 : ℝ)*X 0 1+(1053265411/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344609913/10000000000 : ℝ)*X 1 0+(-2214176523/10000000000 : ℝ)*X 1 1+(5266327083/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344609911/10000000000 : ℝ)*X 2 0+(5266327063/10000000000 : ℝ)*X 2 1+(-1107088277/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((10899419/25000000 : ℝ)*X 0 0+(4235342177/10000000000 : ℝ)*X 0 1+(897560063/2000000000 : ℝ)*X 0 2+(10899419/25000000 : ℝ)*X 1 0+(4235342177/10000000000 : ℝ)*X 1 1+(897560063/2000000000 : ℝ)*X 1 2+(10899419/25000000 : ℝ)*X 2 0+(4235342177/10000000000 : ℝ)*X 2 1+(897560063/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-430053083/2000000000 : ℝ)*X 0 0+(1053328791/2000000000 : ℝ)*X 0 1+(2696020059/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062519561/2000000000 : ℝ)*X 1 0+(-2088463343/10000000000 : ℝ)*X 1 1+(5392040091/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656298851/5000000000 : ℝ)*X 2 0+(674005021/1250000000 : ℝ)*X 2 1+(-2088463377/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4359777171/10000000000 : ℝ)*X 0 0+(4487165569/10000000000 : ℝ)*X 0 1+(16943917/40000000 : ℝ)*X 0 2+(4359777171/10000000000 : ℝ)*X 1 0+(4487165569/10000000000 : ℝ)*X 1 1+(16943917/40000000 : ℝ)*X 1 2+(4359777171/10000000000 : ℝ)*X 2 0+(4487165569/10000000000 : ℝ)*X 2 1+(16943917/40000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1177_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (77988840537296004442009683/16700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (883629301/100000000000000 : ℝ)*(base19) + (826026761/100000000000000 : ℝ)*(base23) + (2919939/10000000000000 : ℝ)*(lower2) + (26577069/20000000000000 : ℝ)*(upper3) + (4309169/10000000000000 : ℝ)*(upper5) + (1486959937617767/25000000000000 : ℝ)*(major0) + (1486959937617767/25000000000000 : ℝ)*(major1) + (1486959937617767/25000000000000 : ℝ)*(major2) + (3967287918269893/50000000000000 : ℝ)*(sp0) + (7934599422344129/100000000000000 : ℝ)*(sp1) + (7934599479946669/100000000000000 : ℝ)*(sp2) + (990266204165051/25000000000000 : ℝ)*(sp3) + (6117358411/25000000000000 : ℝ)*(sp4) + (7111321071/50000000000000 : ℝ)*(sp7) + (1980539519651173/50000000000000 : ℝ)*(f.failure) + (793460030597343/10000000000000 : ℝ)*(f.sum) + (11798327698299/3340000000000000000000000000 : ℝ)*base65 + (203677762836131561/33400000000000000000000000000000 : ℝ)*base68 + (97888365430268439/33400000000000000000000000000000 : ℝ)*base69 + (5900641298468439/33400000000000000000000000000000 : ℝ)*base71 + (9568498186761/3340000000000000000000000000 : ℝ)*base74 + (227610442231268439/33400000000000000000000000000000 : ℝ)*base75 + (239191420480331561/33400000000000000000000000000000 : ℝ)*base78 + (273957197858868439/33400000000000000000000000000000 : ℝ)*base79 + (7913831031939/3340000000000000000000000000 : ℝ)*base81 + (38035483/2500000000000000000000 : ℝ)*base90 + (38035483/2500000000000000000000 : ℝ)*base92 + (38035483/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (135154538645385251433783/13360000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2333386887/100000000000000 : ℝ)*(base19) + (140508103/6250000000000 : ℝ)*(base23) + (26075373/3125000000000 : ℝ)*(lower1) + (13704489/6250000000000 : ℝ)*(upper3) + (36311193/100000000000000 : ℝ)*(lower4) + (91520207/50000000000000 : ℝ)*(upper5) + (5977864936067807/100000000000000 : ℝ)*(major0) + (5977864936067807/100000000000000 : ℝ)*(major1) + (5977864936067807/100000000000000 : ℝ)*(major2) + (16681029/10000000000000 : ℝ)*(sp2) + (7974654641948737/100000000000000 : ℝ)*(sp4) + (7974652308561851/100000000000000 : ℝ)*(sp5) + (7974652227008799/100000000000000 : ℝ)*(sp6) + (995268723243733/25000000000000 : ℝ)*(sp7) + (995268723243733/25000000000000 : ℝ)*(f.failure) + (7974654641948737/100000000000000 : ℝ)*(f.sum) + (6756033541741/13360000000000000000000000000 : ℝ)*base66 + (1039251892288512881/133600000000000000000000000000000 : ℝ)*base68 + (2373320146241312881/133600000000000000000000000000000 : ℝ)*base70 + (14970361652969087119/133600000000000000000000000000000 : ℝ)*base71 + (66003302700979/13360000000000000000000000000 : ℝ)*base73 + (3299103727098687119/133600000000000000000000000000000 : ℝ)*base75 + (361925318639712881/133600000000000000000000000000000 : ℝ)*base78 + (1877185117000287119/133600000000000000000000000000000 : ℝ)*base79 + (83622768602259/13360000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (5391243/1250000000000000000000 : ℝ)*base90 + (5391243/1250000000000000000000 : ℝ)*base92 + (5391243/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1177_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5699/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1177_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1177_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5683/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1177_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1177_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1177_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8369/2048 : ℝ) ≤ p) (hpb : p ≤ (4185/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75078529/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14103/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5683/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1177_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
