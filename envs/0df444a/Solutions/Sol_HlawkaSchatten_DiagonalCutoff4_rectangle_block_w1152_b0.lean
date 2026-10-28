-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1152_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:36:11.848441+00:00
-- url     : https://prove2.me/submissions/86ab28da-c114-4e04-a548-ed610bbfe452

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
theorem support_rectangle_w1152_s0_0 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1888649867/10000000000 : ℝ)*x 0 + (6052021737/10000000000 : ℝ)*x 1 + (4781735741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1888649867/10000000000 : ℝ)^8345 ≤ (1372907047017/12500000000000 : ℝ)^6297 := by
    have hnat : (1888649867 : ℕ)^8345*12500000000000^6297 ≤ 1372907047017^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888649867 10000000000 1372907047017 12500000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6052021737/10000000000 : ℝ)^8345 ≤ (51400464968231/100000000000000 : ℝ)^6297 := by
    have hnat : (6052021737 : ℕ)^8345*100000000000000^6297 ≤ 51400464968231^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6052021737 10000000000 51400464968231 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4781735741/10000000000 : ℝ)^8345 ≤ (9404069660397/25000000000000 : ℝ)^6297 := by
    have hnat : (4781735741 : ℕ)^8345*25000000000000^6297 ≤ 9404069660397^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4781735741 10000000000 9404069660397 25000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1888649867/10000000000 : ℝ), (6052021737/10000000000 : ℝ), (4781735741/10000000000 : ℝ)] ![(1372907047017/12500000000000 : ℝ), (51400464968231/100000000000000 : ℝ), (9404069660397/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1888649867/10000000000 : ℝ)|^8345 ≤ (1372907047017/12500000000000 : ℝ)^6297
        have hw : |(-1888649867/10000000000 : ℝ)|=(1888649867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6052021737/10000000000 : ℝ)|^8345 ≤ (51400464968231/100000000000000 : ℝ)^6297
        have hw : |(6052021737/10000000000 : ℝ)|=(6052021737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4781735741/10000000000 : ℝ)|^8345 ≤ (9404069660397/25000000000000 : ℝ)^6297
        have hw : |(4781735741/10000000000 : ℝ)|=(4781735741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s0_1 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5516230199/10000000000 : ℝ)*x 0 + (-2617360821/10000000000 : ℝ)*x 1 + (4781735767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5516230199/10000000000 : ℝ)^8345 ≤ (1818342248571/4000000000000 : ℝ)^6297 := by
    have hnat : (5516230199 : ℕ)^8345*4000000000000^6297 ≤ 1818342248571^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516230199 10000000000 1818342248571 4000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2617360821/10000000000 : ℝ)^8345 ≤ (16925164856289/100000000000000 : ℝ)^6297 := by
    have hnat : (2617360821 : ℕ)^8345*100000000000000^6297 ≤ 16925164856289^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617360821 10000000000 16925164856289 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4781735767/10000000000 : ℝ)^8345 ≤ (37616278912643/100000000000000 : ℝ)^6297 := by
    have hnat : (4781735767 : ℕ)^8345*100000000000000^6297 ≤ 37616278912643^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4781735767 10000000000 37616278912643 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5516230199/10000000000 : ℝ), (-2617360821/10000000000 : ℝ), (4781735767/10000000000 : ℝ)] ![(1818342248571/4000000000000 : ℝ), (16925164856289/100000000000000 : ℝ), (37616278912643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5516230199/10000000000 : ℝ)|^8345 ≤ (1818342248571/4000000000000 : ℝ)^6297
        have hw : |(5516230199/10000000000 : ℝ)|=(5516230199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2617360821/10000000000 : ℝ)|^8345 ≤ (16925164856289/100000000000000 : ℝ)^6297
        have hw : |(-2617360821/10000000000 : ℝ)|=(2617360821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4781735767/10000000000 : ℝ)|^8345 ≤ (37616278912643/100000000000000 : ℝ)^6297
        have hw : |(4781735767/10000000000 : ℝ)|=(4781735767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s0_2 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5516230481/10000000000 : ℝ)*x 0 + (2390867837/5000000000 : ℝ)*x 1 + (-1308680287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5516230481/10000000000 : ℝ)^8345 ≤ (22729279647011/50000000000000 : ℝ)^6297 := by
    have hnat : (5516230481 : ℕ)^8345*50000000000000^6297 ≤ 22729279647011^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516230481 10000000000 22729279647011 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2390867837/5000000000 : ℝ)^8345 ≤ (18808138971551/50000000000000 : ℝ)^6297 := by
    have hnat : (2390867837 : ℕ)^8345*50000000000000^6297 ≤ 18808138971551^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2390867837 5000000000 18808138971551 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1308680287/5000000000 : ℝ)^8345 ≤ (16925162739591/100000000000000 : ℝ)^6297 := by
    have hnat : (1308680287 : ℕ)^8345*100000000000000^6297 ≤ 16925162739591^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308680287 5000000000 16925162739591 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5516230481/10000000000 : ℝ), (2390867837/5000000000 : ℝ), (-1308680287/5000000000 : ℝ)] ![(22729279647011/50000000000000 : ℝ), (18808138971551/50000000000000 : ℝ), (16925162739591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5516230481/10000000000 : ℝ)|^8345 ≤ (22729279647011/50000000000000 : ℝ)^6297
        have hw : |(5516230481/10000000000 : ℝ)|=(5516230481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2390867837/5000000000 : ℝ)|^8345 ≤ (18808138971551/50000000000000 : ℝ)^6297
        have hw : |(2390867837/5000000000 : ℝ)|=(2390867837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1308680287/5000000000 : ℝ)|^8345 ≤ (16925162739591/100000000000000 : ℝ)^6297
        have hw : |(-1308680287/5000000000 : ℝ)|=(1308680287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s0_3 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4200183299/10000000000 : ℝ)*x 0 + (1560309837/5000000000 : ℝ)*x 1 + (88324671/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4200183299/10000000000 : ℝ)^8345 ≤ (15838431920941/50000000000000 : ℝ)^6297 := by
    have hnat : (4200183299 : ℕ)^8345*50000000000000^6297 ≤ 15838431920941^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4200183299 10000000000 15838431920941 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1560309837/5000000000 : ℝ)^8345 ≤ (21367349200201/100000000000000 : ℝ)^6297 := by
    have hnat : (1560309837 : ℕ)^8345*100000000000000^6297 ≤ 21367349200201^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560309837 5000000000 21367349200201 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88324671/156250000 : ℝ)^8345 ≤ (23477893471533/50000000000000 : ℝ)^6297 := by
    have hnat : (88324671 : ℕ)^8345*50000000000000^6297 ≤ 23477893471533^6297*156250000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88324671 156250000 23477893471533 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4200183299/10000000000 : ℝ), (1560309837/5000000000 : ℝ), (88324671/156250000 : ℝ)] ![(15838431920941/50000000000000 : ℝ), (21367349200201/100000000000000 : ℝ), (23477893471533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4200183299/10000000000 : ℝ)|^8345 ≤ (15838431920941/50000000000000 : ℝ)^6297
        have hw : |(4200183299/10000000000 : ℝ)|=(4200183299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1560309837/5000000000 : ℝ)|^8345 ≤ (21367349200201/100000000000000 : ℝ)^6297
        have hw : |(1560309837/5000000000 : ℝ)|=(1560309837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(88324671/156250000 : ℝ)|^8345 ≤ (23477893471533/50000000000000 : ℝ)^6297
        have hw : |(88324671/156250000 : ℝ)|=(88324671/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s0_4 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1893766017/10000000000 : ℝ)*x 0 + (4814500499/10000000000 : ℝ)*x 1 + (601810431/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1893766017/10000000000 : ℝ)^8345 ≤ (2204540543689/20000000000000 : ℝ)^6297 := by
    have hnat : (1893766017 : ℕ)^8345*20000000000000^6297 ≤ 2204540543689^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893766017 10000000000 2204540543689 20000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4814500499/10000000000 : ℝ)^8345 ≤ (37958236647293/100000000000000 : ℝ)^6297 := by
    have hnat : (4814500499 : ℕ)^8345*100000000000000^6297 ≤ 37958236647293^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4814500499 10000000000 37958236647293 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (601810431/1000000000 : ℝ)^8345 ≤ (12754765155729/25000000000000 : ℝ)^6297 := by
    have hnat : (601810431 : ℕ)^8345*25000000000000^6297 ≤ 12754765155729^6297*1000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601810431 1000000000 12754765155729 25000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1893766017/10000000000 : ℝ), (4814500499/10000000000 : ℝ), (601810431/1000000000 : ℝ)] ![(2204540543689/20000000000000 : ℝ), (37958236647293/100000000000000 : ℝ), (12754765155729/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1893766017/10000000000 : ℝ)|^8345 ≤ (2204540543689/20000000000000 : ℝ)^6297
        have hw : |(-1893766017/10000000000 : ℝ)|=(1893766017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4814500499/10000000000 : ℝ)|^8345 ≤ (37958236647293/100000000000000 : ℝ)^6297
        have hw : |(4814500499/10000000000 : ℝ)|=(4814500499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(601810431/1000000000 : ℝ)|^8345 ≤ (12754765155729/25000000000000 : ℝ)^6297
        have hw : |(601810431/1000000000 : ℝ)|=(601810431/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s0_5 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5171016357/10000000000 : ℝ)*x 0 + (-34524807/250000000 : ℝ)*x 1 + (300905207/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171016357/10000000000 : ℝ)^8345 ≤ (1669094717163/4000000000000 : ℝ)^6297 := by
    have hnat : (5171016357 : ℕ)^8345*4000000000000^6297 ≤ 1669094717163^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171016357 10000000000 1669094717163 4000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34524807/250000000 : ℝ)^8345 ≤ (7253573347839/100000000000000 : ℝ)^6297 := by
    have hnat : (34524807 : ℕ)^8345*100000000000000^6297 ≤ 7253573347839^6297*250000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34524807 250000000 7253573347839 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (300905207/500000000 : ℝ)^8345 ≤ (51019058712999/100000000000000 : ℝ)^6297 := by
    have hnat : (300905207 : ℕ)^8345*100000000000000^6297 ≤ 51019058712999^6297*500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300905207 500000000 51019058712999 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171016357/10000000000 : ℝ), (-34524807/250000000 : ℝ), (300905207/500000000 : ℝ)] ![(1669094717163/4000000000000 : ℝ), (7253573347839/100000000000000 : ℝ), (51019058712999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171016357/10000000000 : ℝ)|^8345 ≤ (1669094717163/4000000000000 : ℝ)^6297
        have hw : |(5171016357/10000000000 : ℝ)|=(5171016357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34524807/250000000 : ℝ)|^8345 ≤ (7253573347839/100000000000000 : ℝ)^6297
        have hw : |(-34524807/250000000 : ℝ)|=(34524807/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(300905207/500000000 : ℝ)|^8345 ≤ (51019058712999/100000000000000 : ℝ)^6297
        have hw : |(300905207/500000000 : ℝ)|=(300905207/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s0_6 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (646377043/1250000000 : ℝ)*x 0 + (6018104191/10000000000 : ℝ)*x 1 + (-690496109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646377043/1250000000 : ℝ)^8345 ≤ (41727367790053/100000000000000 : ℝ)^6297 := by
    have hnat : (646377043 : ℕ)^8345*100000000000000^6297 ≤ 41727367790053^6297*1250000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646377043 1250000000 41727367790053 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6018104191/10000000000 : ℝ)^8345 ≤ (25509529642987/50000000000000 : ℝ)^6297 := by
    have hnat : (6018104191 : ℕ)^8345*50000000000000^6297 ≤ 25509529642987^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6018104191 10000000000 25509529642987 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (690496109/5000000000 : ℝ)^8345 ≤ (290142916651/4000000000000 : ℝ)^6297 := by
    have hnat : (690496109 : ℕ)^8345*4000000000000^6297 ≤ 290142916651^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690496109 5000000000 290142916651 4000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646377043/1250000000 : ℝ), (6018104191/10000000000 : ℝ), (-690496109/5000000000 : ℝ)] ![(41727367790053/100000000000000 : ℝ), (25509529642987/50000000000000 : ℝ), (290142916651/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646377043/1250000000 : ℝ)|^8345 ≤ (41727367790053/100000000000000 : ℝ)^6297
        have hw : |(646377043/1250000000 : ℝ)|=(646377043/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6018104191/10000000000 : ℝ)|^8345 ≤ (25509529642987/50000000000000 : ℝ)^6297
        have hw : |(6018104191/10000000000 : ℝ)|=(6018104191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-690496109/5000000000 : ℝ)|^8345 ≤ (290142916651/4000000000000 : ℝ)^6297
        have hw : |(-690496109/5000000000 : ℝ)|=(690496109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s0_7 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (842076399/2000000000 : ℝ)*x 0 + (223498647/400000000 : ℝ)*x 1 + (3188230283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (842076399/2000000000 : ℝ)^8345 ≤ (15889418114549/50000000000000 : ℝ)^6297 := by
    have hnat : (842076399 : ℕ)^8345*50000000000000^6297 ≤ 15889418114549^6297*2000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842076399 2000000000 15889418114549 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223498647/400000000 : ℝ)^8345 ≤ (23119079807069/50000000000000 : ℝ)^6297 := by
    have hnat : (223498647 : ℕ)^8345*50000000000000^6297 ≤ 23119079807069^6297*400000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223498647 400000000 23119079807069 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3188230283/10000000000 : ℝ)^8345 ≤ (4396600827007/20000000000000 : ℝ)^6297 := by
    have hnat : (3188230283 : ℕ)^8345*20000000000000^6297 ≤ 4396600827007^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3188230283 10000000000 4396600827007 20000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(842076399/2000000000 : ℝ), (223498647/400000000 : ℝ), (3188230283/10000000000 : ℝ)] ![(15889418114549/50000000000000 : ℝ), (23119079807069/50000000000000 : ℝ), (4396600827007/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(842076399/2000000000 : ℝ)|^8345 ≤ (15889418114549/50000000000000 : ℝ)^6297
        have hw : |(842076399/2000000000 : ℝ)|=(842076399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(223498647/400000000 : ℝ)|^8345 ≤ (23119079807069/50000000000000 : ℝ)^6297
        have hw : |(223498647/400000000 : ℝ)|=(223498647/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3188230283/10000000000 : ℝ)|^8345 ≤ (4396600827007/20000000000000 : ℝ)^6297
        have hw : |(3188230283/10000000000 : ℝ)|=(3188230283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1152_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74834429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (91/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27777/100000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (1043/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1043 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1043*1^256 ≤ 0^256*1^1043 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1043 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1043/256 : ℝ) ≤ (478338515030456601/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1043 ≤ (478338515030456601/20000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1043*20000000000000000000^256 ≤ 478338515030456601^256*5^1043 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 478338515030456601 20000000000000000000 1043 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (478338515030456601/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1043 := by
      have hnat : (1 : ℕ)^256*1^1043 ≤ 1^1043*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20478338515030456601/20000000000000000000 : ℝ) ≤ (10058180690065449/10000000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (20478338515030456601/20000000000000000000 : ℝ)^256 ≤ (10058180690065449/10000000000000000 : ℝ)^1043 := by
      have hnat : (20478338515030456601 : ℕ)^256*10000000000000000^1043 ≤ 10058180690065449^1043*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20478338515030456601 20000000000000000000 10058180690065449 10000000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10058180690065449/10000000000000000 : ℝ)) (X := (20478338515030456601/20000000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10478338515030456601/10000000000000000000 : ℝ) ≤ (5058180690065449/5000000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (10478338515030456601/10000000000000000000 : ℝ)^256 ≤ (5058180690065449/5000000000000000 : ℝ)^1043 := by
      have hnat : (10478338515030456601 : ℕ)^256*5000000000000000^1043 ≤ 5058180690065449^1043*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10478338515030456601 10000000000000000000 5058180690065449 5000000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5058180690065449/5000000000000000 : ℝ)) (X := (10478338515030456601/10000000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(58180690065449/4000000000000000 : ℝ)*(0 : ℝ))^(1043/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(58180690065449/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(478338515030456601/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(58180690065449/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1043/256 : ℝ) := by
    rw [show (1 : ℝ)+(58180690065449/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10058180690065449/10000000000000000 : ℝ) by norm_num, show 1+(478338515030456601/20000000000000000000 : ℝ)+(0 : ℝ)=(20478338515030456601/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(478338515030456601/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(58180690065449/4000000000000000 : ℝ)*(2/5 : ℝ))^(1043/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(58180690065449/4000000000000000 : ℝ)*(2/5 : ℝ)=(5058180690065449/5000000000000000 : ℝ) by norm_num, show 1+2*(478338515030456601/20000000000000000000 : ℝ)=(10478338515030456601/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(58180690065449/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58180690065449/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(58180690065449/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58180690065449/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(58180690065449/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58180690065449/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1888649867/10000000000 : ℝ)*X 0 0+(6052021737/10000000000 : ℝ)*X 0 1+(4781735741/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5516230199/10000000000 : ℝ)*X 1 0+(-2617360821/10000000000 : ℝ)*X 1 1+(4781735767/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5516230481/10000000000 : ℝ)*X 2 0+(2390867837/5000000000 : ℝ)*X 2 1+(-1308680287/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4200183299/10000000000 : ℝ)*X 0 0+(1560309837/5000000000 : ℝ)*X 0 1+(88324671/156250000 : ℝ)*X 0 2+(4200183299/10000000000 : ℝ)*X 1 0+(1560309837/5000000000 : ℝ)*X 1 1+(88324671/156250000 : ℝ)*X 1 2+(4200183299/10000000000 : ℝ)*X 2 0+(1560309837/5000000000 : ℝ)*X 2 1+(88324671/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1893766017/10000000000 : ℝ)*X 0 0+(4814500499/10000000000 : ℝ)*X 0 1+(601810431/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5171016357/10000000000 : ℝ)*X 1 0+(-34524807/250000000 : ℝ)*X 1 1+(300905207/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((646377043/1250000000 : ℝ)*X 2 0+(6018104191/10000000000 : ℝ)*X 2 1+(-690496109/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((842076399/2000000000 : ℝ)*X 0 0+(223498647/400000000 : ℝ)*X 0 1+(3188230283/10000000000 : ℝ)*X 0 2+(842076399/2000000000 : ℝ)*X 1 0+(223498647/400000000 : ℝ)*X 1 1+(3188230283/10000000000 : ℝ)*X 1 2+(842076399/2000000000 : ℝ)*X 2 0+(223498647/400000000 : ℝ)*X 2 1+(3188230283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (183379610696486047246119/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14276891/100000000000000 : ℝ)*(base1) + (471207103/100000000000000 : ℝ)*(base19) + (455250129/100000000000000 : ℝ)*(base23) + (3512591/6250000000000 : ℝ)*(base24) + (28643983/25000000000000 : ℝ)*(upper3) + (591074053014277/100000000000000 : ℝ)*(major0) + (591074053014277/100000000000000 : ℝ)*(major1) + (591074053014277/100000000000000 : ℝ)*(major2) + (787225833772317/100000000000000 : ℝ)*(sp0) + (196806592926901/25000000000000 : ℝ)*(sp1) + (393613165731561/50000000000000 : ℝ)*(sp2) + (39492032996039/10000000000000 : ℝ)*(sp3) + (1023419281/100000000000000 : ℝ)*(sp4) + (857750027/100000000000000 : ℝ)*(sp7) + (98730300496827/25000000000000 : ℝ)*(f.failure) + (787226842914707/100000000000000 : ℝ)*(f.sum) + (216670110384627/200000000000000000000000000000 : ℝ)*base66 + (662956688215373/400000000000000000000000000000 : ℝ)*base67 + (1678584661784627/400000000000000000000000000000 : ℝ)*base70 + (1052122606984627/400000000000000000000000000000 : ℝ)*base72 + (108373521215373/200000000000000000000000000000 : ℝ)*base73 + (852260366184627/400000000000000000000000000000 : ℝ)*base76 + (460558001384627/400000000000000000000000000000 : ℝ)*base78 + (1131261336215373/400000000000000000000000000000 : ℝ)*base79 + (581341893184627/200000000000000000000000000000 : ℝ)*base82 + (2356783/1250000000000000000000 : ℝ)*base89 + (2356783/1250000000000000000000 : ℝ)*base91 + (2356783/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (684861710477303943936771/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42183683/50000000000000 : ℝ)*(base1) + (1693597643/100000000000000 : ℝ)*(base19) + (338232237/20000000000000 : ℝ)*(base23) + (45990563/25000000000000 : ℝ)*(upper3) + (39915953/20000000000000 : ℝ)*(upper5) + (155954728743699/25000000000000 : ℝ)*(major0) + (155954728743699/25000000000000 : ℝ)*(major1) + (623818914974797/100000000000000 : ℝ)*(major2) + (860409591/25000000000000 : ℝ)*(sp1) + (107388337/3125000000000 : ℝ)*(sp2) + (415419138724069/50000000000000 : ℝ)*(sp4) + (207708264461191/25000000000000 : ℝ)*(sp5) + (207708266373201/25000000000000 : ℝ)*(sp6) + (6512489440847/1562500000000 : ℝ)*(sp7) + (208399704290787/50000000000000 : ℝ)*(f.failure) + (207709548270193/25000000000000 : ℝ)*(f.sum) + (430531904687743/400000000000000000000000000000 : ℝ)*base66 + (2054577989311147/400000000000000000000000000000 : ℝ)*base68 + (499640291955851/100000000000000000000000000000 : ℝ)*base69 + (1946141542111147/400000000000000000000000000000 : ℝ)*base72 + (1024850713487743/400000000000000000000000000000 : ℝ)*base74 + (1417178955155851/100000000000000000000000000000 : ℝ)*base75 + (919023807644149/100000000000000000000000000000 : ℝ)*base78 + (980890981644149/100000000000000000000000000000 : ℝ)*base80 + (7298522444149/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (4894377/2500000000000000000000 : ℝ)*base90 + (4894377/2500000000000000000000 : ℝ)*base92 + (29894377/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1152_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74834429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (91/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27777/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1152_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1152_s1_0 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1046293903/5000000000 : ℝ)*x 0 + (5698845599/10000000000 : ℝ)*x 1 + (5004355043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046293903/5000000000 : ℝ)^8345 ≤ (629095779917/5000000000000 : ℝ)^6297 := by
    have hnat : (1046293903 : ℕ)^8345*5000000000000^6297 ≤ 629095779917^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046293903 5000000000 629095779917 5000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5698845599/10000000000 : ℝ)^8345 ≤ (47463572747547/100000000000000 : ℝ)^6297 := by
    have hnat : (5698845599 : ℕ)^8345*100000000000000^6297 ≤ 47463572747547^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5698845599 10000000000 47463572747547 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5004355043/10000000000 : ℝ)^8345 ≤ (39954511639321/100000000000000 : ℝ)^6297 := by
    have hnat : (5004355043 : ℕ)^8345*100000000000000^6297 ≤ 39954511639321^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5004355043 10000000000 39954511639321 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1046293903/5000000000 : ℝ), (5698845599/10000000000 : ℝ), (5004355043/10000000000 : ℝ)] ![(629095779917/5000000000000 : ℝ), (47463572747547/100000000000000 : ℝ), (39954511639321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1046293903/5000000000 : ℝ)|^8345 ≤ (629095779917/5000000000000 : ℝ)^6297
        have hw : |(-1046293903/5000000000 : ℝ)|=(1046293903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5698845599/10000000000 : ℝ)|^8345 ≤ (47463572747547/100000000000000 : ℝ)^6297
        have hw : |(5698845599/10000000000 : ℝ)|=(5698845599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5004355043/10000000000 : ℝ)|^8345 ≤ (39954511639321/100000000000000 : ℝ)^6297
        have hw : |(5004355043/10000000000 : ℝ)|=(5004355043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s1_1 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (541857477/1000000000 : ℝ)*x 0 + (-2467182803/10000000000 : ℝ)*x 1 + (2502177091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541857477/1000000000 : ℝ)^8345 ≤ (22197567657653/50000000000000 : ℝ)^6297 := by
    have hnat : (541857477 : ℕ)^8345*50000000000000^6297 ≤ 22197567657653^6297*1000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541857477 1000000000 22197567657653 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2467182803/10000000000 : ℝ)^8345 ≤ (1956295267671/12500000000000 : ℝ)^6297 := by
    have hnat : (2467182803 : ℕ)^8345*12500000000000^6297 ≤ 1956295267671^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2467182803 10000000000 1956295267671 12500000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2502177091/5000000000 : ℝ)^8345 ≤ (2497156408089/6250000000000 : ℝ)^6297 := by
    have hnat : (2502177091 : ℕ)^8345*6250000000000^6297 ≤ 2497156408089^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2502177091 5000000000 2497156408089 6250000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541857477/1000000000 : ℝ), (-2467182803/10000000000 : ℝ), (2502177091/5000000000 : ℝ)] ![(22197567657653/50000000000000 : ℝ), (1956295267671/12500000000000 : ℝ), (2497156408089/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541857477/1000000000 : ℝ)|^8345 ≤ (22197567657653/50000000000000 : ℝ)^6297
        have hw : |(541857477/1000000000 : ℝ)|=(541857477/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2467182803/10000000000 : ℝ)|^8345 ≤ (1956295267671/12500000000000 : ℝ)^6297
        have hw : |(-2467182803/10000000000 : ℝ)|=(2467182803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2502177091/5000000000 : ℝ)|^8345 ≤ (2497156408089/6250000000000 : ℝ)^6297
        have hw : |(2502177091/5000000000 : ℝ)|=(2502177091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s1_2 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5418576827/10000000000 : ℝ)*x 0 + (625544043/1250000000 : ℝ)*x 1 + (-2467182459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5418576827/10000000000 : ℝ)^8345 ≤ (44395157649859/100000000000000 : ℝ)^6297 := by
    have hnat : (5418576827 : ℕ)^8345*100000000000000^6297 ≤ 44395157649859^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418576827 10000000000 44395157649859 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (625544043/1250000000 : ℝ)^8345 ≤ (998862077057/2500000000000 : ℝ)^6297 := by
    have hnat : (625544043 : ℕ)^8345*2500000000000^6297 ≤ 998862077057^6297*1250000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625544043 1250000000 998862077057 2500000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2467182459/10000000000 : ℝ)^8345 ≤ (15650359249529/100000000000000 : ℝ)^6297 := by
    have hnat : (2467182459 : ℕ)^8345*100000000000000^6297 ≤ 15650359249529^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2467182459 10000000000 15650359249529 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5418576827/10000000000 : ℝ), (625544043/1250000000 : ℝ), (-2467182459/10000000000 : ℝ)] ![(44395157649859/100000000000000 : ℝ), (998862077057/2500000000000 : ℝ), (15650359249529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5418576827/10000000000 : ℝ)|^8345 ≤ (44395157649859/100000000000000 : ℝ)^6297
        have hw : |(5418576827/10000000000 : ℝ)|=(5418576827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(625544043/1250000000 : ℝ)|^8345 ≤ (998862077057/2500000000000 : ℝ)^6297
        have hw : |(625544043/1250000000 : ℝ)|=(625544043/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2467182459/10000000000 : ℝ)|^8345 ≤ (15650359249529/100000000000000 : ℝ)^6297
        have hw : |(-2467182459/10000000000 : ℝ)|=(2467182459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s1_3 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (539573841/1250000000 : ℝ)*x 0 + (919728109/2500000000 : ℝ)*x 1 + (2531645271/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539573841/1250000000 : ℝ)^8345 ≤ (32845523894741/100000000000000 : ℝ)^6297 := by
    have hnat : (539573841 : ℕ)^8345*100000000000000^6297 ≤ 32845523894741^6297*1250000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539573841 1250000000 32845523894741 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (919728109/2500000000 : ℝ)^8345 ≤ (2657520035367/10000000000000 : ℝ)^6297 := by
    have hnat : (919728109 : ℕ)^8345*10000000000000^6297 ≤ 2657520035367^6297*2500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919728109 2500000000 2657520035367 10000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2531645271/5000000000 : ℝ)^8345 ≤ (40579275739327/100000000000000 : ℝ)^6297 := by
    have hnat : (2531645271 : ℕ)^8345*100000000000000^6297 ≤ 40579275739327^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2531645271 5000000000 40579275739327 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539573841/1250000000 : ℝ), (919728109/2500000000 : ℝ), (2531645271/5000000000 : ℝ)] ![(32845523894741/100000000000000 : ℝ), (2657520035367/10000000000000 : ℝ), (40579275739327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539573841/1250000000 : ℝ)|^8345 ≤ (32845523894741/100000000000000 : ℝ)^6297
        have hw : |(539573841/1250000000 : ℝ)|=(539573841/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(919728109/2500000000 : ℝ)|^8345 ≤ (2657520035367/10000000000000 : ℝ)^6297
        have hw : |(919728109/2500000000 : ℝ)|=(919728109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2531645271/5000000000 : ℝ)|^8345 ≤ (40579275739327/100000000000000 : ℝ)^6297
        have hw : |(2531645271/5000000000 : ℝ)|=(2531645271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s1_4 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2093384701/10000000000 : ℝ)*x 0 + (78340651/156250000 : ℝ)*x 1 + (5689209167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093384701/10000000000 : ℝ)^8345 ≤ (12588265744457/100000000000000 : ℝ)^6297 := by
    have hnat : (2093384701 : ℕ)^8345*100000000000000^6297 ≤ 12588265744457^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093384701 10000000000 12588265744457 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (78340651/156250000 : ℝ)^8345 ≤ (40054493241103/100000000000000 : ℝ)^6297 := by
    have hnat : (78340651 : ℕ)^8345*100000000000000^6297 ≤ 40054493241103^6297*156250000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78340651 156250000 40054493241103 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5689209167/10000000000 : ℝ)^8345 ≤ (47357240997553/100000000000000 : ℝ)^6297 := by
    have hnat : (5689209167 : ℕ)^8345*100000000000000^6297 ≤ 47357240997553^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5689209167 10000000000 47357240997553 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2093384701/10000000000 : ℝ), (78340651/156250000 : ℝ), (5689209167/10000000000 : ℝ)] ![(12588265744457/100000000000000 : ℝ), (40054493241103/100000000000000 : ℝ), (47357240997553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2093384701/10000000000 : ℝ)|^8345 ≤ (12588265744457/100000000000000 : ℝ)^6297
        have hw : |(-2093384701/10000000000 : ℝ)|=(2093384701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(78340651/156250000 : ℝ)|^8345 ≤ (40054493241103/100000000000000 : ℝ)^6297
        have hw : |(78340651/156250000 : ℝ)|=(78340651/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5689209167/10000000000 : ℝ)|^8345 ≤ (47357240997553/100000000000000 : ℝ)^6297
        have hw : |(5689209167/10000000000 : ℝ)|=(5689209167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s1_5 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1048086099/2000000000 : ℝ)*x 0 + (-1782323787/10000000000 : ℝ)*x 1 + (1137842557/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048086099/2000000000 : ℝ)^8345 ≤ (2654455879401/6250000000000 : ℝ)^6297 := by
    have hnat : (1048086099 : ℕ)^8345*6250000000000^6297 ≤ 2654455879401^6297*2000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048086099 2000000000 2654455879401 6250000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1782323787/10000000000 : ℝ)^8345 ≤ (10171425009073/100000000000000 : ℝ)^6297 := by
    have hnat : (1782323787 : ℕ)^8345*100000000000000^6297 ≤ 10171425009073^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1782323787 10000000000 10171425009073 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1137842557/2000000000 : ℝ)^8345 ≤ (47357280908841/100000000000000 : ℝ)^6297 := by
    have hnat : (1137842557 : ℕ)^8345*100000000000000^6297 ≤ 47357280908841^6297*2000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137842557 2000000000 47357280908841 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048086099/2000000000 : ℝ), (-1782323787/10000000000 : ℝ), (1137842557/2000000000 : ℝ)] ![(2654455879401/6250000000000 : ℝ), (10171425009073/100000000000000 : ℝ), (47357280908841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048086099/2000000000 : ℝ)|^8345 ≤ (2654455879401/6250000000000 : ℝ)^6297
        have hw : |(1048086099/2000000000 : ℝ)|=(1048086099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1782323787/10000000000 : ℝ)|^8345 ≤ (10171425009073/100000000000000 : ℝ)^6297
        have hw : |(-1782323787/10000000000 : ℝ)|=(1782323787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1137842557/2000000000 : ℝ)|^8345 ≤ (47357280908841/100000000000000 : ℝ)^6297
        have hw : |(1137842557/2000000000 : ℝ)|=(1137842557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s1_6 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1048085851/2000000000 : ℝ)*x 0 + (5689214501/10000000000 : ℝ)*x 1 + (-356464609/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048085851/2000000000 : ℝ)^8345 ≤ (42471280752299/100000000000000 : ℝ)^6297 := by
    have hnat : (1048085851 : ℕ)^8345*100000000000000^6297 ≤ 42471280752299^6297*2000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048085851 2000000000 42471280752299 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5689214501/10000000000 : ℝ)^8345 ≤ (2959831239911/6250000000000 : ℝ)^6297 := by
    have hnat : (5689214501 : ℕ)^8345*6250000000000^6297 ≤ 2959831239911^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5689214501 10000000000 2959831239911 6250000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (356464609/2000000000 : ℝ)^8345 ≤ (317856856169/3125000000000 : ℝ)^6297 := by
    have hnat : (356464609 : ℕ)^8345*3125000000000^6297 ≤ 317856856169^6297*2000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356464609 2000000000 317856856169 3125000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048085851/2000000000 : ℝ), (5689214501/10000000000 : ℝ), (-356464609/2000000000 : ℝ)] ![(42471280752299/100000000000000 : ℝ), (2959831239911/6250000000000 : ℝ), (317856856169/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048085851/2000000000 : ℝ)|^8345 ≤ (42471280752299/100000000000000 : ℝ)^6297
        have hw : |(1048085851/2000000000 : ℝ)|=(1048085851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5689214501/10000000000 : ℝ)|^8345 ≤ (2959831239911/6250000000000 : ℝ)^6297
        have hw : |(5689214501/10000000000 : ℝ)|=(5689214501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-356464609/2000000000 : ℝ)|^8345 ≤ (317856856169/3125000000000 : ℝ)^6297
        have hw : |(-356464609/2000000000 : ℝ)|=(356464609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s1_7 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2159084041/5000000000 : ℝ)*x 0 + (5044460819/10000000000 : ℝ)*x 1 + (3698112843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159084041/5000000000 : ℝ)^8345 ≤ (32861430699231/100000000000000 : ℝ)^6297 := by
    have hnat : (2159084041 : ℕ)^8345*100000000000000^6297 ≤ 32861430699231^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159084041 5000000000 32861430699231 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5044460819/10000000000 : ℝ)^8345 ≤ (40379406904107/100000000000000 : ℝ)^6297 := by
    have hnat : (5044460819 : ℕ)^8345*100000000000000^6297 ≤ 40379406904107^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5044460819 10000000000 40379406904107 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3698112843/10000000000 : ℝ)^8345 ≤ (26759162377787/100000000000000 : ℝ)^6297 := by
    have hnat : (3698112843 : ℕ)^8345*100000000000000^6297 ≤ 26759162377787^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3698112843 10000000000 26759162377787 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2159084041/5000000000 : ℝ), (5044460819/10000000000 : ℝ), (3698112843/10000000000 : ℝ)] ![(32861430699231/100000000000000 : ℝ), (40379406904107/100000000000000 : ℝ), (26759162377787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2159084041/5000000000 : ℝ)|^8345 ≤ (32861430699231/100000000000000 : ℝ)^6297
        have hw : |(2159084041/5000000000 : ℝ)|=(2159084041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5044460819/10000000000 : ℝ)|^8345 ≤ (40379406904107/100000000000000 : ℝ)^6297
        have hw : |(5044460819/10000000000 : ℝ)|=(5044460819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3698112843/10000000000 : ℝ)|^8345 ≤ (26759162377787/100000000000000 : ℝ)^6297
        have hw : |(3698112843/10000000000 : ℝ)|=(3698112843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s1_8 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2902623/5000000000 : ℝ)*x 0 + (274519901/500000000 : ℝ)*x 1 + (6353264251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2902623/5000000000 : ℝ)^8345 ≤ (1286009873/25000000000000 : ℝ)^6297 := by
    have hnat : (2902623 : ℕ)^8345*25000000000000^6297 ≤ 1286009873^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2902623 5000000000 1286009873 25000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274519901/500000000 : ℝ)^8345 ≤ (22588327890357/50000000000000 : ℝ)^6297 := by
    have hnat : (274519901 : ℕ)^8345*50000000000000^6297 ≤ 22588327890357^6297*500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274519901 500000000 22588327890357 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6353264251/10000000000 : ℝ)^8345 ≤ (27409100084189/50000000000000 : ℝ)^6297 := by
    have hnat : (6353264251 : ℕ)^8345*50000000000000^6297 ≤ 27409100084189^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6353264251 10000000000 27409100084189 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2902623/5000000000 : ℝ), (274519901/500000000 : ℝ), (6353264251/10000000000 : ℝ)] ![(1286009873/25000000000000 : ℝ), (22588327890357/50000000000000 : ℝ), (27409100084189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2902623/5000000000 : ℝ)|^8345 ≤ (1286009873/25000000000000 : ℝ)^6297
        have hw : |(2902623/5000000000 : ℝ)|=(2902623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(274519901/500000000 : ℝ)|^8345 ≤ (22588327890357/50000000000000 : ℝ)^6297
        have hw : |(274519901/500000000 : ℝ)|=(274519901/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6353264251/10000000000 : ℝ)|^8345 ≤ (27409100084189/50000000000000 : ℝ)^6297
        have hw : |(6353264251/10000000000 : ℝ)|=(6353264251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s1_9 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (490960591/5000000000 : ℝ)*x 0 + (-440302513/1000000000 : ℝ)*x 1 + (6943232053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (490960591/5000000000 : ℝ)^8345 ≤ (923199231397/20000000000000 : ℝ)^6297 := by
    have hnat : (490960591 : ℕ)^8345*20000000000000^6297 ≤ 923199231397^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490960591 5000000000 923199231397 20000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440302513/1000000000 : ℝ)^8345 ≤ (33719944048699/100000000000000 : ℝ)^6297 := by
    have hnat : (440302513 : ℕ)^8345*100000000000000^6297 ≤ 33719944048699^6297*1000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440302513 1000000000 33719944048699 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6943232053/10000000000 : ℝ)^8345 ≤ (2466562391099/4000000000000 : ℝ)^6297 := by
    have hnat : (6943232053 : ℕ)^8345*4000000000000^6297 ≤ 2466562391099^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6943232053 10000000000 2466562391099 4000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(490960591/5000000000 : ℝ), (-440302513/1000000000 : ℝ), (6943232053/10000000000 : ℝ)] ![(923199231397/20000000000000 : ℝ), (33719944048699/100000000000000 : ℝ), (2466562391099/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(490960591/5000000000 : ℝ)|^8345 ≤ (923199231397/20000000000000 : ℝ)^6297
        have hw : |(490960591/5000000000 : ℝ)|=(490960591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-440302513/1000000000 : ℝ)|^8345 ≤ (33719944048699/100000000000000 : ℝ)^6297
        have hw : |(-440302513/1000000000 : ℝ)|=(440302513/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6943232053/10000000000 : ℝ)|^8345 ≤ (2466562391099/4000000000000 : ℝ)^6297
        have hw : |(6943232053/10000000000 : ℝ)|=(6943232053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s1_10 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (981913561/10000000000 : ℝ)*x 0 + (6943213913/10000000000 : ℝ)*x 1 + (-880610169/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (981913561/10000000000 : ℝ)^8345 ≤ (576993584867/12500000000000 : ℝ)^6297 := by
    have hnat : (981913561 : ℕ)^8345*12500000000000^6297 ≤ 576993584867^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981913561 10000000000 576993584867 12500000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6943213913/10000000000 : ℝ)^8345 ≤ (7707980784543/12500000000000 : ℝ)^6297 := by
    have hnat : (6943213913 : ℕ)^8345*12500000000000^6297 ≤ 7707980784543^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6943213913 10000000000 7707980784543 12500000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (880610169/2000000000 : ℝ)^8345 ≤ (33720205033533/100000000000000 : ℝ)^6297 := by
    have hnat : (880610169 : ℕ)^8345*100000000000000^6297 ≤ 33720205033533^6297*2000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880610169 2000000000 33720205033533 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(981913561/10000000000 : ℝ), (6943213913/10000000000 : ℝ), (-880610169/2000000000 : ℝ)] ![(576993584867/12500000000000 : ℝ), (7707980784543/12500000000000 : ℝ), (33720205033533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(981913561/10000000000 : ℝ)|^8345 ≤ (576993584867/12500000000000 : ℝ)^6297
        have hw : |(981913561/10000000000 : ℝ)|=(981913561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6943213913/10000000000 : ℝ)|^8345 ≤ (7707980784543/12500000000000 : ℝ)^6297
        have hw : |(6943213913/10000000000 : ℝ)|=(6943213913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-880610169/2000000000 : ℝ)|^8345 ≤ (33720205033533/100000000000000 : ℝ)^6297
        have hw : |(-880610169/2000000000 : ℝ)|=(880610169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s1_11 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1914758581/10000000000 : ℝ)*x 0 + (1452386397/2500000000 : ℝ)*x 1 + (1255134449/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1914758581/10000000000 : ℝ)^8345 ≤ (11184921126557/100000000000000 : ℝ)^6297 := by
    have hnat : (1914758581 : ℕ)^8345*100000000000000^6297 ≤ 11184921126557^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914758581 10000000000 11184921126557 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1452386397/2500000000 : ℝ)^8345 ≤ (48689253980177/100000000000000 : ℝ)^6297 := by
    have hnat : (1452386397 : ℕ)^8345*100000000000000^6297 ≤ 48689253980177^6297*2500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1452386397 2500000000 48689253980177 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1255134449/2500000000 : ℝ)^8345 ≤ (2507864054701/6250000000000 : ℝ)^6297 := by
    have hnat : (1255134449 : ℕ)^8345*6250000000000^6297 ≤ 2507864054701^6297*2500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255134449 2500000000 2507864054701 6250000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1914758581/10000000000 : ℝ), (1452386397/2500000000 : ℝ), (1255134449/2500000000 : ℝ)] ![(11184921126557/100000000000000 : ℝ), (48689253980177/100000000000000 : ℝ), (2507864054701/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1914758581/10000000000 : ℝ)|^8345 ≤ (11184921126557/100000000000000 : ℝ)^6297
        have hw : |(1914758581/10000000000 : ℝ)|=(1914758581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1452386397/2500000000 : ℝ)|^8345 ≤ (48689253980177/100000000000000 : ℝ)^6297
        have hw : |(1452386397/2500000000 : ℝ)|=(1452386397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1255134449/2500000000 : ℝ)|^8345 ≤ (2507864054701/6250000000000 : ℝ)^6297
        have hw : |(1255134449/2500000000 : ℝ)|=(1255134449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1152_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74834429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27777/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (91/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1141/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2549/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27777/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (91/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27777/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (91/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27777/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (91/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27777/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (91/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27777/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (91/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27777/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (91/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (91/20000 : ℝ) ^ (1043/256 : ℝ) ≤ (28722756733/100000000000000000000 : ℝ) := by
    have hpowers : (91/20000 : ℝ)^1043 ≤ (28722756733/100000000000000000000 : ℝ)^256 := by
      have hnat : (91 : ℕ)^1043*100000000000000000000^256 ≤ 28722756733^256*20000^1043 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        91 20000 28722756733 100000000000000000000 1043 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (91/20000 : ℝ)) (X := (28722756733/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hpowhi : (27777/100000 : ℝ) ^ (1043/256 : ℝ) ≤ (541317885255624783/100000000000000000000 : ℝ) := by
    have hpowers : (27777/100000 : ℝ)^1043 ≤ (541317885255624783/100000000000000000000 : ℝ)^256 := by
      have hnat : (27777 : ℕ)^1043*100000000000000000000^256 ≤ 541317885255624783^256*100000^1043 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27777 100000 541317885255624783 100000000000000000000 1043 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27777/100000 : ℝ)) (X := (541317885255624783/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000028722756733/50000000000000000000 : ℝ) ≤ (10000000001409977/10000000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (50000000028722756733/50000000000000000000 : ℝ)^256 ≤ (10000000001409977/10000000000000000 : ℝ)^1043 := by
      have hnat : (50000000028722756733 : ℕ)^256*10000000000000000^1043 ≤ 10000000001409977^1043*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000028722756733 50000000000000000000 10000000001409977 10000000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000001409977/10000000000000000 : ℝ)) (X := (50000000028722756733/50000000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25135329478494595379/25000000000000000000 : ℝ) ≤ (625828710848627/625000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (25135329478494595379/25000000000000000000 : ℝ)^256 ≤ (625828710848627/625000000000000 : ℝ)^1043 := by
      have hnat : (25135329478494595379 : ℕ)^256*625000000000000^1043 ≤ 625828710848627^1043*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25135329478494595379 25000000000000000000 625828710848627 625000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625828710848627/625000000000000 : ℝ)) (X := (25135329478494595379/25000000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50541317885255624783/50000000000000000000 : ℝ) ≤ (10026518745746087/10000000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (50541317885255624783/50000000000000000000 : ℝ)^256 ≤ (10026518745746087/10000000000000000 : ℝ)^1043 := by
      have hnat : (50541317885255624783 : ℕ)^256*10000000000000000^1043 ≤ 10026518745746087^1043*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50541317885255624783 50000000000000000000 10026518745746087 10000000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10026518745746087/10000000000000000 : ℝ)) (X := (50541317885255624783/50000000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(28722756733/100000000000000000000 : ℝ) ≤ ((34150991751231307693/34152500000000000000 : ℝ)+2*(2651874433611/546440000000000 : ℝ)*(91/20000 : ℝ))^(1043/256 : ℝ) := by
    rw [show (34150991751231307693/34152500000000000000 : ℝ)+2*(2651874433611/546440000000000 : ℝ)*(91/20000 : ℝ)=(10000000001409977/10000000000000000 : ℝ) by norm_num, show 1+2*(28722756733/100000000000000000000 : ℝ)=(50000000028722756733/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(541317885255624783/100000000000000000000 : ℝ)+(28722756733/100000000000000000000 : ℝ) ≤ ((34150991751231307693/34152500000000000000 : ℝ)+(2651874433611/546440000000000 : ℝ)*((27777/100000 : ℝ)+(91/20000 : ℝ)))^(1043/256 : ℝ) := by
    rw [show (34150991751231307693/34152500000000000000 : ℝ)+(2651874433611/546440000000000 : ℝ)*((27777/100000 : ℝ)+(91/20000 : ℝ))=(625828710848627/625000000000000 : ℝ) by norm_num, show 1+(541317885255624783/100000000000000000000 : ℝ)+(28722756733/100000000000000000000 : ℝ)=(25135329478494595379/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(541317885255624783/100000000000000000000 : ℝ) ≤ ((34150991751231307693/34152500000000000000 : ℝ)+2*(2651874433611/546440000000000 : ℝ)*(27777/100000 : ℝ))^(1043/256 : ℝ) := by
    rw [show (34150991751231307693/34152500000000000000 : ℝ)+2*(2651874433611/546440000000000 : ℝ)*(27777/100000 : ℝ)=(10026518745746087/10000000000000000 : ℝ) by norm_num, show 1+2*(541317885255624783/100000000000000000000 : ℝ)=(50541317885255624783/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34150991751231307693/34152500000000000000 : ℝ)*(X 1 0+X 2 0)+(2651874433611/546440000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (91/20000 : ℝ)) (hi := (27777/100000 : ℝ)) (c := (34150991751231307693/34152500000000000000 : ℝ)) (alpha := (2651874433611/546440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34150991751231307693/34152500000000000000 : ℝ)*(X 0 1+X 2 1)+(2651874433611/546440000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (91/20000 : ℝ)) (hi := (27777/100000 : ℝ)) (c := (34150991751231307693/34152500000000000000 : ℝ)) (alpha := (2651874433611/546440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34150991751231307693/34152500000000000000 : ℝ)*(X 0 2+X 1 2)+(2651874433611/546440000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (91/20000 : ℝ)) (hi := (27777/100000 : ℝ)) (c := (34150991751231307693/34152500000000000000 : ℝ)) (alpha := (2651874433611/546440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1046293903/5000000000 : ℝ)*X 0 0+(5698845599/10000000000 : ℝ)*X 0 1+(5004355043/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((541857477/1000000000 : ℝ)*X 1 0+(-2467182803/10000000000 : ℝ)*X 1 1+(2502177091/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5418576827/10000000000 : ℝ)*X 2 0+(625544043/1250000000 : ℝ)*X 2 1+(-2467182459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((539573841/1250000000 : ℝ)*X 0 0+(919728109/2500000000 : ℝ)*X 0 1+(2531645271/5000000000 : ℝ)*X 0 2+(539573841/1250000000 : ℝ)*X 1 0+(919728109/2500000000 : ℝ)*X 1 1+(2531645271/5000000000 : ℝ)*X 1 2+(539573841/1250000000 : ℝ)*X 2 0+(919728109/2500000000 : ℝ)*X 2 1+(2531645271/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2093384701/10000000000 : ℝ)*X 0 0+(78340651/156250000 : ℝ)*X 0 1+(5689209167/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1048086099/2000000000 : ℝ)*X 1 0+(-1782323787/10000000000 : ℝ)*X 1 1+(1137842557/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1048085851/2000000000 : ℝ)*X 2 0+(5689214501/10000000000 : ℝ)*X 2 1+(-356464609/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2159084041/5000000000 : ℝ)*X 0 0+(5044460819/10000000000 : ℝ)*X 0 1+(3698112843/10000000000 : ℝ)*X 0 2+(2159084041/5000000000 : ℝ)*X 1 0+(5044460819/10000000000 : ℝ)*X 1 1+(3698112843/10000000000 : ℝ)*X 1 2+(2159084041/5000000000 : ℝ)*X 2 0+(5044460819/10000000000 : ℝ)*X 2 1+(3698112843/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((2902623/5000000000 : ℝ)*X 0 0+(274519901/500000000 : ℝ)*X 0 1+(6353264251/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((490960591/5000000000 : ℝ)*X 1 0+(-440302513/1000000000 : ℝ)*X 1 1+(6943232053/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((981913561/10000000000 : ℝ)*X 2 0+(6943213913/10000000000 : ℝ)*X 2 1+(-880610169/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1914758581/10000000000 : ℝ)*X 0 0+(1452386397/2500000000 : ℝ)*X 0 1+(1255134449/2500000000 : ℝ)*X 0 2+(1914758581/10000000000 : ℝ)*X 1 0+(1452386397/2500000000 : ℝ)*X 1 1+(1255134449/2500000000 : ℝ)*X 1 2+(1914758581/10000000000 : ℝ)*X 2 0+(1452386397/2500000000 : ℝ)*X 2 1+(1255134449/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4486112382028594264479059499/341525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (216226289788019/20000000000000 : ℝ)*(major0) + (216226289788019/20000000000000 : ℝ)*(major1) + (216226289788019/20000000000000 : ℝ)*(major2) + (57596343973801/4000000000000 : ℝ)*(sp0) + (719954100924051/50000000000000 : ℝ)*(sp1) + (179988253501929/12500000000000 : ℝ)*(sp2) + (722346898873269/100000000000000 : ℝ)*(sp3) + (2399558051/50000000000000 : ℝ)*(sp4) + (1117451591/25000000000000 : ℝ)*(sp5) + (1207811669/20000000000000 : ℝ)*(sp6) + (23766209/25000000000000 : ℝ)*(sp8) + (410935749/50000000000000 : ℝ)*(sp9) + (356613047/25000000000000 : ℝ)*(sp10) + (2067629899/100000000000000 : ℝ)*(sp11) + (2821675650403/390625000000 : ℝ)*(f.failure) + (1439913493525963/100000000000000 : ℝ)*(f.sum) + (8288065862827/5464400000000000000000000000 : ℝ)*base65 + (3441752209304042667/683050000000000000000000000000000 : ℝ)*base67 + (3073002183278642667/683050000000000000000000000000000 : ℝ)*base69 + (714765118490642667/683050000000000000000000000000000 : ℝ)*base71 + (91619323621241/27322000000000000000000000000 : ℝ)*base73 + (1133853456191992667/683050000000000000000000000000000 : ℝ)*base75 + (412452727809907333/683050000000000000000000000000000 : ℝ)*base78 + (2173404899621657333/683050000000000000000000000000000 : ℝ)*base80 + (170926238741307/27322000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/50000000000000 : ℝ)*base87 + (359601/39062500000000000000 : ℝ)*base90 + (359601/39062500000000000000 : ℝ)*base92 + (359601/39062500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6862565798303368300208537013/853812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (555834880268751/50000000000000 : ℝ)*(major0) + (555834880268751/50000000000000 : ℝ)*(major1) + (555834880268751/50000000000000 : ℝ)*(major2) + (2487126117/50000000000000 : ℝ)*(sp1) + (3968823267/50000000000000 : ℝ)*(sp2) + (1077172459/100000000000000 : ℝ)*(sp3) + (361470327939/24414062500 : ℝ)*(sp4) + (1480580881233969/100000000000000 : ℝ)*(sp5) + (1480578224987173/100000000000000 : ℝ)*(sp6) + (371374981858997/50000000000000 : ℝ)*(sp7) + (61016479/1562500000000 : ℝ)*(sp8) + (512806597/100000000000000 : ℝ)*(sp9) + (51414773/25000000000000 : ℝ)*(sp10) + (1843973211/100000000000000 : ℝ)*(sp11) + (148550576972733/20000000000000 : ℝ)*(f.failure) + (1480586368292799/100000000000000 : ℝ)*(f.sum) + (16591101054199/6830500000000000000000000000 : ℝ)*base65 + (2620812815848363943/1707625000000000000000000000000000 : ℝ)*base67 + (3891356911107613943/1707625000000000000000000000000000 : ℝ)*base69 + (2061929820362613943/1707625000000000000000000000000000 : ℝ)*base71 + (36881828889059/6830500000000000000000000000 : ℝ)*base73 + (3349491314033863943/1707625000000000000000000000000000 : ℝ)*base75 + (9223193613510613943/1707625000000000000000000000000000 : ℝ)*base77 + (9730226671127238943/1707625000000000000000000000000000 : ℝ)*base79 + (6367678233529/3415250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2624457/1000000000000000000000 : ℝ)*base89 + (2624457/1000000000000000000000 : ℝ)*base91 + (2624457/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1152_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74834429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27777/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (91/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1141/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2549/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1152_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1152_s2_0 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2145288991/10000000000 : ℝ)*x 0 + (1377229531/2500000000 : ℝ)*x 1 + (258038023/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145288991/10000000000 : ℝ)^8345 ≤ (13003554992063/100000000000000 : ℝ)^6297 := by
    have hnat : (2145288991 : ℕ)^8345*100000000000000^6297 ≤ 13003554992063^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145288991 10000000000 13003554992063 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1377229531/2500000000 : ℝ)^8345 ≤ (1418084925589/3125000000000 : ℝ)^6297 := by
    have hnat : (1377229531 : ℕ)^8345*3125000000000^6297 ≤ 1418084925589^6297*2500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377229531 2500000000 1418084925589 3125000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258038023/500000000 : ℝ)^8345 ≤ (41617727374949/100000000000000 : ℝ)^6297 := by
    have hnat : (258038023 : ℕ)^8345*100000000000000^6297 ≤ 41617727374949^6297*500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258038023 500000000 41617727374949 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2145288991/10000000000 : ℝ), (1377229531/2500000000 : ℝ), (258038023/500000000 : ℝ)] ![(13003554992063/100000000000000 : ℝ), (1418084925589/3125000000000 : ℝ), (41617727374949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2145288991/10000000000 : ℝ)|^8345 ≤ (13003554992063/100000000000000 : ℝ)^6297
        have hw : |(-2145288991/10000000000 : ℝ)|=(2145288991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1377229531/2500000000 : ℝ)|^8345 ≤ (1418084925589/3125000000000 : ℝ)^6297
        have hw : |(1377229531/2500000000 : ℝ)|=(1377229531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258038023/500000000 : ℝ)|^8345 ≤ (41617727374949/100000000000000 : ℝ)^6297
        have hw : |(258038023/500000000 : ℝ)|=(258038023/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s2_1 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5373435531/10000000000 : ℝ)*x 0 + (-581556499/2500000000 : ℝ)*x 1 + (5160762773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373435531/10000000000 : ℝ)^8345 ≤ (5488210801541/12500000000000 : ℝ)^6297 := by
    have hnat : (5373435531 : ℕ)^8345*12500000000000^6297 ≤ 5488210801541^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373435531 10000000000 5488210801541 12500000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (581556499/2500000000 : ℝ)^8345 ≤ (3619140371519/25000000000000 : ℝ)^6297 := by
    have hnat : (581556499 : ℕ)^8345*25000000000000^6297 ≤ 3619140371519^6297*2500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      581556499 2500000000 3619140371519 25000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5160762773/10000000000 : ℝ)^8345 ≤ (41617752094067/100000000000000 : ℝ)^6297 := by
    have hnat : (5160762773 : ℕ)^8345*100000000000000^6297 ≤ 41617752094067^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5160762773 10000000000 41617752094067 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373435531/10000000000 : ℝ), (-581556499/2500000000 : ℝ), (5160762773/10000000000 : ℝ)] ![(5488210801541/12500000000000 : ℝ), (3619140371519/25000000000000 : ℝ), (41617752094067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373435531/10000000000 : ℝ)|^8345 ≤ (5488210801541/12500000000000 : ℝ)^6297
        have hw : |(5373435531/10000000000 : ℝ)|=(5373435531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-581556499/2500000000 : ℝ)|^8345 ≤ (3619140371519/25000000000000 : ℝ)^6297
        have hw : |(-581556499/2500000000 : ℝ)|=(581556499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5160762773/10000000000 : ℝ)|^8345 ≤ (41617752094067/100000000000000 : ℝ)^6297
        have hw : |(5160762773/10000000000 : ℝ)|=(5160762773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s2_2 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5373435667/10000000000 : ℝ)*x 0 + (2580381203/5000000000 : ℝ)*x 1 + (-2326226291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373435667/10000000000 : ℝ)^8345 ≤ (43905687884981/100000000000000 : ℝ)^6297 := by
    have hnat : (5373435667 : ℕ)^8345*100000000000000^6297 ≤ 43905687884981^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373435667 10000000000 43905687884981 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2580381203/5000000000 : ℝ)^8345 ≤ (10404437042981/25000000000000 : ℝ)^6297 := by
    have hnat : (2580381203 : ℕ)^8345*25000000000000^6297 ≤ 10404437042981^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2580381203 5000000000 10404437042981 25000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2326226291/10000000000 : ℝ)^8345 ≤ (7238281959499/50000000000000 : ℝ)^6297 := by
    have hnat : (2326226291 : ℕ)^8345*50000000000000^6297 ≤ 7238281959499^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2326226291 10000000000 7238281959499 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373435667/10000000000 : ℝ), (2580381203/5000000000 : ℝ), (-2326226291/10000000000 : ℝ)] ![(43905687884981/100000000000000 : ℝ), (10404437042981/25000000000000 : ℝ), (7238281959499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373435667/10000000000 : ℝ)|^8345 ≤ (43905687884981/100000000000000 : ℝ)^6297
        have hw : |(5373435667/10000000000 : ℝ)|=(5373435667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2580381203/5000000000 : ℝ)|^8345 ≤ (10404437042981/25000000000000 : ℝ)^6297
        have hw : |(2580381203/5000000000 : ℝ)|=(2580381203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2326226291/10000000000 : ℝ)|^8345 ≤ (7238281959499/50000000000000 : ℝ)^6297
        have hw : |(-2326226291/10000000000 : ℝ)|=(2326226291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s2_3 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (870553503/2000000000 : ℝ)*x 0 + (1004860221/2500000000 : ℝ)*x 1 + (4713445523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870553503/2000000000 : ℝ)^8345 ≤ (6642164554051/20000000000000 : ℝ)^6297 := by
    have hnat : (870553503 : ℕ)^8345*20000000000000^6297 ≤ 6642164554051^6297*2000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870553503 2000000000 6642164554051 20000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004860221/2500000000 : ℝ)^8345 ≤ (29883176563197/100000000000000 : ℝ)^6297 := by
    have hnat : (1004860221 : ℕ)^8345*100000000000000^6297 ≤ 29883176563197^6297*2500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004860221 2500000000 29883176563197 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4713445523/10000000000 : ℝ)^8345 ≤ (7381200131441/20000000000000 : ℝ)^6297 := by
    have hnat : (4713445523 : ℕ)^8345*20000000000000^6297 ≤ 7381200131441^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4713445523 10000000000 7381200131441 20000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870553503/2000000000 : ℝ), (1004860221/2500000000 : ℝ), (4713445523/10000000000 : ℝ)] ![(6642164554051/20000000000000 : ℝ), (29883176563197/100000000000000 : ℝ), (7381200131441/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870553503/2000000000 : ℝ)|^8345 ≤ (6642164554051/20000000000000 : ℝ)^6297
        have hw : |(870553503/2000000000 : ℝ)|=(870553503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1004860221/2500000000 : ℝ)|^8345 ≤ (29883176563197/100000000000000 : ℝ)^6297
        have hw : |(1004860221/2500000000 : ℝ)|=(1004860221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4713445523/10000000000 : ℝ)|^8345 ≤ (7381200131441/20000000000000 : ℝ)^6297
        have hw : |(4713445523/10000000000 : ℝ)|=(4713445523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s2_4 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2145388931/10000000000 : ℝ)*x 0 + (1290786169/2500000000 : ℝ)*x 1 + (5506510109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145388931/10000000000 : ℝ)^8345 ≤ (3251089449963/25000000000000 : ℝ)^6297 := by
    have hnat : (2145388931 : ℕ)^8345*25000000000000^6297 ≤ 3251089449963^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145388931 10000000000 3251089449963 25000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1290786169/2500000000 : ℝ)^8345 ≤ (20821604746639/50000000000000 : ℝ)^6297 := by
    have hnat : (1290786169 : ℕ)^8345*50000000000000^6297 ≤ 20821604746639^6297*2500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1290786169 2500000000 20821604746639 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5506510109/10000000000 : ℝ)^8345 ≤ (22676216343297/50000000000000 : ℝ)^6297 := by
    have hnat : (5506510109 : ℕ)^8345*50000000000000^6297 ≤ 22676216343297^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506510109 10000000000 22676216343297 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2145388931/10000000000 : ℝ), (1290786169/2500000000 : ℝ), (5506510109/10000000000 : ℝ)] ![(3251089449963/25000000000000 : ℝ), (20821604746639/50000000000000 : ℝ), (22676216343297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2145388931/10000000000 : ℝ)|^8345 ≤ (3251089449963/25000000000000 : ℝ)^6297
        have hw : |(-2145388931/10000000000 : ℝ)|=(2145388931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1290786169/2500000000 : ℝ)|^8345 ≤ (20821604746639/50000000000000 : ℝ)^6297
        have hw : |(1290786169/2500000000 : ℝ)|=(1290786169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5506510109/10000000000 : ℝ)|^8345 ≤ (22676216343297/50000000000000 : ℝ)^6297
        have hw : |(5506510109/10000000000 : ℝ)|=(5506510109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s2_5 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2642520049/5000000000 : ℝ)*x 0 + (-495119083/2500000000 : ℝ)*x 1 + (1101302177/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642520049/5000000000 : ℝ)^8345 ≤ (21475540914891/50000000000000 : ℝ)^6297 := by
    have hnat : (2642520049 : ℕ)^8345*50000000000000^6297 ≤ 21475540914891^6297*5000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642520049 5000000000 21475540914891 50000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (495119083/2500000000 : ℝ)^8345 ≤ (11696477007611/100000000000000 : ℝ)^6297 := by
    have hnat : (495119083 : ℕ)^8345*100000000000000^6297 ≤ 11696477007611^6297*2500000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495119083 2500000000 11696477007611 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1101302177/2000000000 : ℝ)^8345 ≤ (45352441156499/100000000000000 : ℝ)^6297 := by
    have hnat : (1101302177 : ℕ)^8345*100000000000000^6297 ≤ 45352441156499^6297*2000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101302177 2000000000 45352441156499 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642520049/5000000000 : ℝ), (-495119083/2500000000 : ℝ), (1101302177/2000000000 : ℝ)] ![(21475540914891/50000000000000 : ℝ), (11696477007611/100000000000000 : ℝ), (45352441156499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642520049/5000000000 : ℝ)|^8345 ≤ (21475540914891/50000000000000 : ℝ)^6297
        have hw : |(2642520049/5000000000 : ℝ)|=(2642520049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-495119083/2500000000 : ℝ)|^8345 ≤ (11696477007611/100000000000000 : ℝ)^6297
        have hw : |(-495119083/2500000000 : ℝ)|=(495119083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1101302177/2000000000 : ℝ)|^8345 ≤ (45352441156499/100000000000000 : ℝ)^6297
        have hw : |(1101302177/2000000000 : ℝ)|=(1101302177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s2_6 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5285038413/10000000000 : ℝ)*x 0 + (1101302121/2000000000 : ℝ)*x 1 + (-6188997/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285038413/10000000000 : ℝ)^8345 ≤ (42951063682217/100000000000000 : ℝ)^6297 := by
    have hnat : (5285038413 : ℕ)^8345*100000000000000^6297 ≤ 42951063682217^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285038413 10000000000 42951063682217 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101302121/2000000000 : ℝ)^8345 ≤ (45352438100347/100000000000000 : ℝ)^6297 := by
    have hnat : (1101302121 : ℕ)^8345*100000000000000^6297 ≤ 45352438100347^6297*2000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101302121 2000000000 45352438100347 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6188997/31250000 : ℝ)^8345 ≤ (731031137643/6250000000000 : ℝ)^6297 := by
    have hnat : (6188997 : ℕ)^8345*6250000000000^6297 ≤ 731031137643^6297*31250000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6188997 31250000 731031137643 6250000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285038413/10000000000 : ℝ), (1101302121/2000000000 : ℝ), (-6188997/31250000 : ℝ)] ![(42951063682217/100000000000000 : ℝ), (45352438100347/100000000000000 : ℝ), (731031137643/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285038413/10000000000 : ℝ)|^8345 ≤ (42951063682217/100000000000000 : ℝ)^6297
        have hw : |(5285038413/10000000000 : ℝ)|=(5285038413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1101302121/2000000000 : ℝ)|^8345 ≤ (45352438100347/100000000000000 : ℝ)^6297
        have hw : |(1101302121/2000000000 : ℝ)|=(1101302121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6188997/31250000 : ℝ)|^8345 ≤ (731031137643/6250000000000 : ℝ)^6297
        have hw : |(-6188997/31250000 : ℝ)|=(6188997/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1152_s2_7 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (8705931/20000000 : ℝ)*x 0 + (4708694853/10000000000 : ℝ)*x 1 + (4024239199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8705931/20000000 : ℝ)^8345 ≤ (33212824669939/100000000000000 : ℝ)^6297 := by
    have hnat : (8705931 : ℕ)^8345*100000000000000^6297 ≤ 33212824669939^6297*20000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8705931 20000000 33212824669939 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4708694853/10000000000 : ℝ)^8345 ≤ (36856713382929/100000000000000 : ℝ)^6297 := by
    have hnat : (4708694853 : ℕ)^8345*100000000000000^6297 ≤ 36856713382929^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4708694853 10000000000 36856713382929 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4024239199/10000000000 : ℝ)^8345 ≤ (29930461933689/100000000000000 : ℝ)^6297 := by
    have hnat : (4024239199 : ℕ)^8345*100000000000000^6297 ≤ 29930461933689^6297*10000000000^8345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024239199 10000000000 29930461933689 100000000000000 8345 6297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8345/2048 : ℝ)) 8345 6297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8705931/20000000 : ℝ), (4708694853/10000000000 : ℝ), (4024239199/10000000000 : ℝ)] ![(33212824669939/100000000000000 : ℝ), (36856713382929/100000000000000 : ℝ), (29930461933689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8705931/20000000 : ℝ)|^8345 ≤ (33212824669939/100000000000000 : ℝ)^6297
        have hw : |(8705931/20000000 : ℝ)|=(8705931/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4708694853/10000000000 : ℝ)|^8345 ≤ (36856713382929/100000000000000 : ℝ)^6297
        have hw : |(4708694853/10000000000 : ℝ)|=(4708694853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4024239199/10000000000 : ℝ)|^8345 ≤ (29930461933689/100000000000000 : ℝ)^6297
        have hw : |(4024239199/10000000000 : ℝ)|=(4024239199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1152_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74834429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2549/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1141/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1823/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16473/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2549/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1141/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2549/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1141/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2549/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1141/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2549/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1141/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2549/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1141/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2549/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1141/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1141/20000 : ℝ) ^ (1043/256 : ℝ) ≤ (856472541301559/100000000000000000000 : ℝ) := by
    have hpowers : (1141/20000 : ℝ)^1043 ≤ (856472541301559/100000000000000000000 : ℝ)^256 := by
      have hnat : (1141 : ℕ)^1043*100000000000000000000^256 ≤ 856472541301559^256*20000^1043 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1141 20000 856472541301559 100000000000000000000 1043 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1141/20000 : ℝ)) (X := (856472541301559/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2549/12500 : ℝ) ^ (1043/256 : ℝ) ≤ (153669706233407937/100000000000000000000 : ℝ) := by
    have hpowers : (2549/12500 : ℝ)^1043 ≤ (153669706233407937/100000000000000000000 : ℝ)^256 := by
      have hnat : (2549 : ℕ)^1043*100000000000000000000^256 ≤ 153669706233407937^256*12500^1043 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2549 12500 153669706233407937 100000000000000000000 1043 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2549/12500 : ℝ)) (X := (153669706233407937/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000856472541301559/50000000000000000000 : ℝ) ≤ (1250005255406367/1250000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (50000856472541301559/50000000000000000000 : ℝ)^256 ≤ (1250005255406367/1250000000000000 : ℝ)^1043 := by
      have hnat : (50000856472541301559 : ℕ)^256*1250000000000000^1043 ≤ 1250005255406367^1043*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000856472541301559 50000000000000000000 1250005255406367 1250000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250005255406367/1250000000000000 : ℝ)) (X := (50000856472541301559/50000000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (12519315772346838687/12500000000000000000 : ℝ) ≤ (250094764286159/250000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (12519315772346838687/12500000000000000000 : ℝ)^256 ≤ (250094764286159/250000000000000 : ℝ)^1043 := by
      have hnat : (12519315772346838687 : ℕ)^256*250000000000000^1043 ≤ 250094764286159^1043*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12519315772346838687 12500000000000000000 250094764286159 250000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250094764286159/250000000000000 : ℝ)) (X := (12519315772346838687/12500000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50153669706233407937/50000000000000000000 : ℝ) ≤ (1250942387455223/1250000000000000 : ℝ) ^ (1043/256 : ℝ) := by
    have hpowers : (50153669706233407937/50000000000000000000 : ℝ)^256 ≤ (1250942387455223/1250000000000000 : ℝ)^1043 := by
      have hnat : (50153669706233407937 : ℕ)^256*1250000000000000^1043 ≤ 1250942387455223^1043*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50153669706233407937 50000000000000000000 1250942387455223 1250000000000000 256 1043 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250942387455223/1250000000000000 : ℝ)) (X := (50153669706233407937/50000000000000000000 : ℝ)) (by norm_num) 1043 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(856472541301559/100000000000000000000 : ℝ) ≤ ((18353480847814588649/18358750000000000000 : ℝ)+2*(117141506107/45896875000000 : ℝ)*(1141/20000 : ℝ))^(1043/256 : ℝ) := by
    rw [show (18353480847814588649/18358750000000000000 : ℝ)+2*(117141506107/45896875000000 : ℝ)*(1141/20000 : ℝ)=(1250005255406367/1250000000000000 : ℝ) by norm_num, show 1+2*(856472541301559/100000000000000000000 : ℝ)=(50000856472541301559/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(153669706233407937/100000000000000000000 : ℝ)+(856472541301559/100000000000000000000 : ℝ) ≤ ((18353480847814588649/18358750000000000000 : ℝ)+(117141506107/45896875000000 : ℝ)*((2549/12500 : ℝ)+(1141/20000 : ℝ)))^(1043/256 : ℝ) := by
    rw [show (18353480847814588649/18358750000000000000 : ℝ)+(117141506107/45896875000000 : ℝ)*((2549/12500 : ℝ)+(1141/20000 : ℝ))=(250094764286159/250000000000000 : ℝ) by norm_num, show 1+(153669706233407937/100000000000000000000 : ℝ)+(856472541301559/100000000000000000000 : ℝ)=(12519315772346838687/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(153669706233407937/100000000000000000000 : ℝ) ≤ ((18353480847814588649/18358750000000000000 : ℝ)+2*(117141506107/45896875000000 : ℝ)*(2549/12500 : ℝ))^(1043/256 : ℝ) := by
    rw [show (18353480847814588649/18358750000000000000 : ℝ)+2*(117141506107/45896875000000 : ℝ)*(2549/12500 : ℝ)=(1250942387455223/1250000000000000 : ℝ) by norm_num, show 1+2*(153669706233407937/100000000000000000000 : ℝ)=(50153669706233407937/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18353480847814588649/18358750000000000000 : ℝ)*(X 1 0+X 2 0)+(117141506107/45896875000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (1141/20000 : ℝ)) (hi := (2549/12500 : ℝ)) (c := (18353480847814588649/18358750000000000000 : ℝ)) (alpha := (117141506107/45896875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18353480847814588649/18358750000000000000 : ℝ)*(X 0 1+X 2 1)+(117141506107/45896875000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (1141/20000 : ℝ)) (hi := (2549/12500 : ℝ)) (c := (18353480847814588649/18358750000000000000 : ℝ)) (alpha := (117141506107/45896875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18353480847814588649/18358750000000000000 : ℝ)*(X 0 2+X 1 2)+(117141506107/45896875000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1043/256 : ℝ)) (lo := (1141/20000 : ℝ)) (hi := (2549/12500 : ℝ)) (c := (18353480847814588649/18358750000000000000 : ℝ)) (alpha := (117141506107/45896875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2145288991/10000000000 : ℝ)*X 0 0+(1377229531/2500000000 : ℝ)*X 0 1+(258038023/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5373435531/10000000000 : ℝ)*X 1 0+(-581556499/2500000000 : ℝ)*X 1 1+(5160762773/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5373435667/10000000000 : ℝ)*X 2 0+(2580381203/5000000000 : ℝ)*X 2 1+(-2326226291/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((870553503/2000000000 : ℝ)*X 0 0+(1004860221/2500000000 : ℝ)*X 0 1+(4713445523/10000000000 : ℝ)*X 0 2+(870553503/2000000000 : ℝ)*X 1 0+(1004860221/2500000000 : ℝ)*X 1 1+(4713445523/10000000000 : ℝ)*X 1 2+(870553503/2000000000 : ℝ)*X 2 0+(1004860221/2500000000 : ℝ)*X 2 1+(4713445523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2145388931/10000000000 : ℝ)*X 0 0+(1290786169/2500000000 : ℝ)*X 0 1+(5506510109/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2642520049/5000000000 : ℝ)*X 1 0+(-495119083/2500000000 : ℝ)*X 1 1+(1101302177/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5285038413/10000000000 : ℝ)*X 2 0+(1101302121/2000000000 : ℝ)*X 2 1+(-6188997/31250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((8705931/20000000 : ℝ)*X 0 0+(4708694853/10000000000 : ℝ)*X 0 1+(4024239199/10000000000 : ℝ)*X 0 2+(8705931/20000000 : ℝ)*X 1 0+(4708694853/10000000000 : ℝ)*X 1 1+(4024239199/10000000000 : ℝ)*X 1 2+(8705931/20000000 : ℝ)*X 2 0+(4708694853/10000000000 : ℝ)*X 2 1+(4024239199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1152_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (335812677453598181393558511/36717500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (474114321/50000000000000 : ℝ)*(base19) + (753040821/100000000000000 : ℝ)*(base23) + (26250849/100000000000000 : ℝ)*(upper2) + (47208579/12500000000000 : ℝ)*(upper3) + (170197169/100000000000000 : ℝ)*(upper4) + (86264735096613/4000000000000 : ℝ)*(major0) + (86264735096613/4000000000000 : ℝ)*(major1) + (1078309188707663/50000000000000 : ℝ)*(major2) + (179518018280239/6250000000000 : ℝ)*(sp0) + (2872308908036233/100000000000000 : ℝ)*(sp1) + (1436154551612027/50000000000000 : ℝ)*(sp2) + (360229432948133/25000000000000 : ℝ)*(sp3) + (21563781051/100000000000000 : ℝ)*(sp4) + (4430955817/50000000000000 : ℝ)*(sp7) + (720463296852083/50000000000000 : ℝ)*(f.failure) + (1436154928132437/50000000000000 : ℝ)*(f.sum) + (22116080382513/73435000000000000000000000000 : ℝ)*base66 + (163839117516512163/73435000000000000000000000000000 : ℝ)*base68 + (3227403835266320213/917937500000000000000000000000000 : ℝ)*base70 + (59508958312452837/73435000000000000000000000000000 : ℝ)*base71 + (14901925760029/36717500000000000000000000000 : ℝ)*base74 + (4007219129710554787/917937500000000000000000000000000 : ℝ)*base75 + (722123051913584163/73435000000000000000000000000000 : ℝ)*base78 + (339559969143544163/73435000000000000000000000000000 : ℝ)*base80 + (6464782160887/1835875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3765607/2500000000000000000000 : ℝ)*base89 + (3765607/2500000000000000000000 : ℝ)*base91 + (21234393/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3850659349747170311910425529/458968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (175847009/12500000000000 : ℝ)*(base19) + (853694227/100000000000000 : ℝ)*(base23) + (385619659/100000000000000 : ℝ)*(upper2) + (77911297/100000000000000 : ℝ)*(upper3) + (137870253/50000000000000 : ℝ)*(upper5) + (1093338279746207/50000000000000 : ℝ)*(major0) + (1093338279746207/50000000000000 : ℝ)*(major1) + (1093338279746207/50000000000000 : ℝ)*(major2) + (22566134101/100000000000000 : ℝ)*(sp1) + (1388997887/100000000000000 : ℝ)*(sp2) + (364042890224637/12500000000000 : ℝ)*(sp4) + (1456159574443461/50000000000000 : ℝ)*(sp5) + (1456170439552491/50000000000000 : ℝ)*(sp6) + (730504858763743/50000000000000 : ℝ)*(sp7) + (730504858763743/50000000000000 : ℝ)*(f.failure) + (364042890224637/12500000000000 : ℝ)*(f.sum) + (13093278505619/4589687500000000000000000000 : ℝ)*base66 + (4577642845836020657/917937500000000000000000000000000 : ℝ)*base68 + (1413582711172770657/917937500000000000000000000000000 : ℝ)*base70 + (179124394840791843/917937500000000000000000000000000 : ℝ)*base71 + (171102873704347/36717500000000000000000000000 : ℝ)*base74 + (4807348958091416843/917937500000000000000000000000000 : ℝ)*base75 + (5201061697090208157/917937500000000000000000000000000 : ℝ)*base78 + (2530375409450520657/917937500000000000000000000000000 : ℝ)*base80 + (116976738169641/73435000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (3307747/2500000000000000000000 : ℝ)*base89 + (3307747/2500000000000000000000 : ℝ)*base91 + (3307747/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1152_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74834429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2549/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1141/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1823/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16473/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1152_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1152_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74834429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1823/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16473/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1152_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1152_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1152_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74834429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1823/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16473/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1152_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
