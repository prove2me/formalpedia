-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1158_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:38:43.751027+00:00
-- url     : https://prove2.me/submissions/7be5e392-c962-49bb-95d3-dcb93f91ed65

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
theorem support_rectangle_w1158_s3_0 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2155629143/10000000000 : ℝ)*x 0 + (5427546253/10000000000 : ℝ)*x 1 + (5233568543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155629143/10000000000 : ℝ)^8351 ≤ (2618579898109/20000000000000 : ℝ)^6303 := by
    have hnat : (2155629143 : ℕ)^8351*20000000000000^6303 ≤ 2618579898109^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155629143 10000000000 2618579898109 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427546253/10000000000 : ℝ)^8351 ≤ (44500990948107/100000000000000 : ℝ)^6303 := by
    have hnat : (5427546253 : ℕ)^8351*100000000000000^6303 ≤ 44500990948107^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427546253 10000000000 44500990948107 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5233568543/10000000000 : ℝ)^8351 ≤ (42406109544729/100000000000000 : ℝ)^6303 := by
    have hnat : (5233568543 : ℕ)^8351*100000000000000^6303 ≤ 42406109544729^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233568543 10000000000 42406109544729 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2155629143/10000000000 : ℝ), (5427546253/10000000000 : ℝ), (5233568543/10000000000 : ℝ)] ![(2618579898109/20000000000000 : ℝ), (44500990948107/100000000000000 : ℝ), (42406109544729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2155629143/10000000000 : ℝ)|^8351 ≤ (2618579898109/20000000000000 : ℝ)^6303
        have hw : |(-2155629143/10000000000 : ℝ)|=(2155629143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427546253/10000000000 : ℝ)|^8351 ≤ (44500990948107/100000000000000 : ℝ)^6303
        have hw : |(5427546253/10000000000 : ℝ)|=(5427546253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5233568543/10000000000 : ℝ)|^8351 ≤ (42406109544729/100000000000000 : ℝ)^6303
        have hw : |(5233568543/10000000000 : ℝ)|=(5233568543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s3_1 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5353410939/10000000000 : ℝ)*x 0 + (-2254749581/10000000000 : ℝ)*x 1 + (2616784177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353410939/10000000000 : ℝ)^8351 ≤ (10924359424097/25000000000000 : ℝ)^6303 := by
    have hnat : (5353410939 : ℕ)^8351*25000000000000^6303 ≤ 10924359424097^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353410939 10000000000 10924359424097 25000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254749581/10000000000 : ℝ)^8351 ≤ (868528423379/6250000000000 : ℝ)^6303 := by
    have hnat : (2254749581 : ℕ)^8351*6250000000000^6303 ≤ 868528423379^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254749581 10000000000 868528423379 6250000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2616784177/5000000000 : ℝ)^8351 ≤ (21203053757861/50000000000000 : ℝ)^6303 := by
    have hnat : (2616784177 : ℕ)^8351*50000000000000^6303 ≤ 21203053757861^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616784177 5000000000 21203053757861 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353410939/10000000000 : ℝ), (-2254749581/10000000000 : ℝ), (2616784177/5000000000 : ℝ)] ![(10924359424097/25000000000000 : ℝ), (868528423379/6250000000000 : ℝ), (21203053757861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353410939/10000000000 : ℝ)|^8351 ≤ (10924359424097/25000000000000 : ℝ)^6303
        have hw : |(5353410939/10000000000 : ℝ)|=(5353410939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2254749581/10000000000 : ℝ)|^8351 ≤ (868528423379/6250000000000 : ℝ)^6303
        have hw : |(-2254749581/10000000000 : ℝ)|=(2254749581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2616784177/5000000000 : ℝ)|^8351 ≤ (21203053757861/50000000000000 : ℝ)^6303
        have hw : |(2616784177/5000000000 : ℝ)|=(2616784177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s3_2 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5353411019/10000000000 : ℝ)*x 0 + (523356839/1000000000 : ℝ)*x 1 + (-2254749427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353411019/10000000000 : ℝ)^8351 ≤ (1365544955049/3125000000000 : ℝ)^6303 := by
    have hnat : (5353411019 : ℕ)^8351*3125000000000^6303 ≤ 1365544955049^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353411019 10000000000 1365544955049 3125000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523356839/1000000000 : ℝ)^8351 ≤ (212030539511/500000000000 : ℝ)^6303 := by
    have hnat : (523356839 : ℕ)^8351*500000000000^6303 ≤ 212030539511^6303*1000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523356839 1000000000 212030539511 500000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254749427/10000000000 : ℝ)^8351 ≤ (1737056689567/12500000000000 : ℝ)^6303 := by
    have hnat : (2254749427 : ℕ)^8351*12500000000000^6303 ≤ 1737056689567^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254749427 10000000000 1737056689567 12500000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353411019/10000000000 : ℝ), (523356839/1000000000 : ℝ), (-2254749427/10000000000 : ℝ)] ![(1365544955049/3125000000000 : ℝ), (212030539511/500000000000 : ℝ), (1737056689567/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353411019/10000000000 : ℝ)|^8351 ≤ (1365544955049/3125000000000 : ℝ)^6303
        have hw : |(5353411019/10000000000 : ℝ)|=(5353411019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(523356839/1000000000 : ℝ)|^8351 ≤ (212030539511/500000000000 : ℝ)^6303
        have hw : |(523356839/1000000000 : ℝ)|=(523356839/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2254749427/10000000000 : ℝ)|^8351 ≤ (1737056689567/12500000000000 : ℝ)^6303
        have hw : |(-2254749427/10000000000 : ℝ)|=(2254749427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s3_3 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2180133447/5000000000 : ℝ)*x 0 + (4170957999/10000000000 : ℝ)*x 1 + (2279041529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180133447/5000000000 : ℝ)^8351 ≤ (33295227673853/100000000000000 : ℝ)^6303 := by
    have hnat : (2180133447 : ℕ)^8351*100000000000000^6303 ≤ 33295227673853^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180133447 5000000000 33295227673853 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4170957999/10000000000 : ℝ)^8351 ≤ (15696798406907/50000000000000 : ℝ)^6303 := by
    have hnat : (4170957999 : ℕ)^8351*50000000000000^6303 ≤ 15696798406907^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170957999 10000000000 15696798406907 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2279041529/5000000000 : ℝ)^8351 ≤ (17655587753977/50000000000000 : ℝ)^6303 := by
    have hnat : (2279041529 : ℕ)^8351*50000000000000^6303 ≤ 17655587753977^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279041529 5000000000 17655587753977 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180133447/5000000000 : ℝ), (4170957999/10000000000 : ℝ), (2279041529/5000000000 : ℝ)] ![(33295227673853/100000000000000 : ℝ), (15696798406907/50000000000000 : ℝ), (17655587753977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180133447/5000000000 : ℝ)|^8351 ≤ (33295227673853/100000000000000 : ℝ)^6303
        have hw : |(2180133447/5000000000 : ℝ)|=(2180133447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4170957999/10000000000 : ℝ)|^8351 ≤ (15696798406907/50000000000000 : ℝ)^6303
        have hw : |(4170957999/10000000000 : ℝ)|=(4170957999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2279041529/5000000000 : ℝ)|^8351 ≤ (17655587753977/50000000000000 : ℝ)^6303
        have hw : |(2279041529/5000000000 : ℝ)|=(2279041529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s3_4 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-431129287/2000000000 : ℝ)*x 0 + (81786137/156250000 : ℝ)*x 1 + (5426797933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431129287/2000000000 : ℝ)^8351 ≤ (6546519322763/50000000000000 : ℝ)^6303 := by
    have hnat : (431129287 : ℕ)^8351*50000000000000^6303 ≤ 6546519322763^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431129287 2000000000 6546519322763 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81786137/156250000 : ℝ)^8351 ≤ (5301762418253/12500000000000 : ℝ)^6303 := by
    have hnat : (81786137 : ℕ)^8351*12500000000000^6303 ≤ 5301762418253^6303*156250000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81786137 156250000 5301762418253 12500000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426797933/10000000000 : ℝ)^8351 ≤ (44492861988799/100000000000000 : ℝ)^6303 := by
    have hnat : (5426797933 : ℕ)^8351*100000000000000^6303 ≤ 44492861988799^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426797933 10000000000 44492861988799 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-431129287/2000000000 : ℝ), (81786137/156250000 : ℝ), (5426797933/10000000000 : ℝ)] ![(6546519322763/50000000000000 : ℝ), (5301762418253/12500000000000 : ℝ), (44492861988799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-431129287/2000000000 : ℝ)|^8351 ≤ (6546519322763/50000000000000 : ℝ)^6303
        have hw : |(-431129287/2000000000 : ℝ)|=(431129287/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81786137/156250000 : ℝ)|^8351 ≤ (5301762418253/12500000000000 : ℝ)^6303
        have hw : |(81786137/156250000 : ℝ)|=(81786137/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426797933/10000000000 : ℝ)|^8351 ≤ (44492861988799/100000000000000 : ℝ)^6303
        have hw : |(5426797933/10000000000 : ℝ)|=(5426797933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s3_5 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (165756571/312500000 : ℝ)*x 0 + (-1030760239/5000000000 : ℝ)*x 1 + (5426797749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165756571/312500000 : ℝ)^8351 ≤ (5395767600967/12500000000000 : ℝ)^6303 := by
    have hnat : (165756571 : ℕ)^8351*12500000000000^6303 ≤ 5395767600967^6303*312500000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165756571 312500000 5395767600967 12500000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030760239/5000000000 : ℝ)^8351 ≤ (2468199838811/20000000000000 : ℝ)^6303 := by
    have hnat : (1030760239 : ℕ)^8351*20000000000000^6303 ≤ 2468199838811^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030760239 5000000000 2468199838811 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426797749/10000000000 : ℝ)^8351 ≤ (22246429995031/50000000000000 : ℝ)^6303 := by
    have hnat : (5426797749 : ℕ)^8351*50000000000000^6303 ≤ 22246429995031^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426797749 10000000000 22246429995031 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165756571/312500000 : ℝ), (-1030760239/5000000000 : ℝ), (5426797749/10000000000 : ℝ)] ![(5395767600967/12500000000000 : ℝ), (2468199838811/20000000000000 : ℝ), (22246429995031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165756571/312500000 : ℝ)|^8351 ≤ (5395767600967/12500000000000 : ℝ)^6303
        have hw : |(165756571/312500000 : ℝ)|=(165756571/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1030760239/5000000000 : ℝ)|^8351 ≤ (2468199838811/20000000000000 : ℝ)^6303
        have hw : |(-1030760239/5000000000 : ℝ)|=(1030760239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426797749/10000000000 : ℝ)|^8351 ≤ (22246429995031/50000000000000 : ℝ)^6303
        have hw : |(5426797749/10000000000 : ℝ)|=(5426797749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s3_6 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1326052761/2500000000 : ℝ)*x 0 + (5426797147/10000000000 : ℝ)*x 1 + (-515380063/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326052761/2500000000 : ℝ)^8351 ≤ (8633229826343/20000000000000 : ℝ)^6303 := by
    have hnat : (1326052761 : ℕ)^8351*20000000000000^6303 ≤ 8633229826343^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326052761 2500000000 8633229826343 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426797147/10000000000 : ℝ)^8351 ≤ (8898570690143/20000000000000 : ℝ)^6303 := by
    have hnat : (5426797147 : ℕ)^8351*20000000000000^6303 ≤ 8898570690143^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426797147 10000000000 8898570690143 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515380063/2500000000 : ℝ)^8351 ≤ (6170498700771/50000000000000 : ℝ)^6303 := by
    have hnat : (515380063 : ℕ)^8351*50000000000000^6303 ≤ 6170498700771^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515380063 2500000000 6170498700771 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326052761/2500000000 : ℝ), (5426797147/10000000000 : ℝ), (-515380063/2500000000 : ℝ)] ![(8633229826343/20000000000000 : ℝ), (8898570690143/20000000000000 : ℝ), (6170498700771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326052761/2500000000 : ℝ)|^8351 ≤ (8633229826343/20000000000000 : ℝ)^6303
        have hw : |(1326052761/2500000000 : ℝ)|=(1326052761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426797147/10000000000 : ℝ)|^8351 ≤ (8898570690143/20000000000000 : ℝ)^6303
        have hw : |(5426797147/10000000000 : ℝ)|=(5426797147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-515380063/2500000000 : ℝ)|^8351 ≤ (6170498700771/50000000000000 : ℝ)^6303
        have hw : |(-515380063/2500000000 : ℝ)|=(515380063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s3_7 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (436030121/1000000000 : ℝ)*x 0 + (455659789/1000000000 : ℝ)*x 1 + (2086225819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436030121/1000000000 : ℝ)^8351 ≤ (16647787427969/50000000000000 : ℝ)^6303 := by
    have hnat : (436030121 : ℕ)^8351*50000000000000^6303 ≤ 16647787427969^6303*1000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436030121 1000000000 16647787427969 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (455659789/1000000000 : ℝ)^8351 ≤ (35295932393567/100000000000000 : ℝ)^6303 := by
    have hnat : (455659789 : ℕ)^8351*100000000000000^6303 ≤ 35295932393567^6303*1000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455659789 1000000000 35295932393567 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086225819/5000000000 : ℝ)^8351 ≤ (15704246367143/50000000000000 : ℝ)^6303 := by
    have hnat : (2086225819 : ℕ)^8351*50000000000000^6303 ≤ 15704246367143^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086225819 5000000000 15704246367143 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436030121/1000000000 : ℝ), (455659789/1000000000 : ℝ), (2086225819/5000000000 : ℝ)] ![(16647787427969/50000000000000 : ℝ), (35295932393567/100000000000000 : ℝ), (15704246367143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436030121/1000000000 : ℝ)|^8351 ≤ (16647787427969/50000000000000 : ℝ)^6303
        have hw : |(436030121/1000000000 : ℝ)|=(436030121/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(455659789/1000000000 : ℝ)|^8351 ≤ (35295932393567/100000000000000 : ℝ)^6303
        have hw : |(455659789/1000000000 : ℝ)|=(455659789/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086225819/5000000000 : ℝ)|^8351 ≤ (15704246367143/50000000000000 : ℝ)^6303
        have hw : |(2086225819/5000000000 : ℝ)|=(2086225819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1158_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3291/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4571/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5341/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14787/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3291/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4571/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3291/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4571/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3291/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4571/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3291/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4571/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3291/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4571/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3291/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4571/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4571/50000 : ℝ) ^ (4175/1024 : ℝ) ≤ (580778888285887/10000000000000000000 : ℝ) := by
    have hpowers : (4571/50000 : ℝ)^4175 ≤ (580778888285887/10000000000000000000 : ℝ)^1024 := by
      have hnat : (4571 : ℕ)^4175*10000000000000000000^1024 ≤ 580778888285887^1024*50000^4175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4571 50000 580778888285887 10000000000000000000 4175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4571/50000 : ℝ)) (X := (580778888285887/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3291/20000 : ℝ) ^ (4175/1024 : ℝ) ≤ (6378670271269701/10000000000000000000 : ℝ) := by
    have hpowers : (3291/20000 : ℝ)^4175 ≤ (6378670271269701/10000000000000000000 : ℝ)^1024 := by
      have hnat : (3291 : ℕ)^4175*10000000000000000000^1024 ≤ 6378670271269701^1024*20000^4175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3291 20000 6378670271269701 10000000000000000000 4175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3291/20000 : ℝ)) (X := (6378670271269701/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000580778888285887/5000000000000000000 : ℝ) ≤ (1250035610270361/1250000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (5000580778888285887/5000000000000000000 : ℝ)^1024 ≤ (1250035610270361/1250000000000000 : ℝ)^4175 := by
      have hnat : (5000580778888285887 : ℕ)^1024*1250000000000000^4175 ≤ 1250035610270361^4175*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000580778888285887 5000000000000000000 1250035610270361 1250000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250035610270361/1250000000000000 : ℝ)) (X := (5000580778888285887/5000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2501739862289888897/2500000000000000000 : ℝ) ≤ (10001706492241197/10000000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (2501739862289888897/2500000000000000000 : ℝ)^1024 ≤ (10001706492241197/10000000000000000 : ℝ)^4175 := by
      have hnat : (2501739862289888897 : ℕ)^1024*10000000000000000^4175 ≤ 10001706492241197^4175*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501739862289888897 2500000000000000000 10001706492241197 10000000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001706492241197/10000000000000000 : ℝ)) (X := (2501739862289888897/2500000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5006378670271269701/5000000000000000000 : ℝ) ≤ (5001564051159753/5000000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (5006378670271269701/5000000000000000000 : ℝ)^1024 ≤ (5001564051159753/5000000000000000 : ℝ)^4175 := by
      have hnat : (5006378670271269701 : ℕ)^1024*5000000000000000^4175 ≤ 5001564051159753^4175*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5006378670271269701 5000000000000000000 5001564051159753 5000000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001564051159753/5000000000000000 : ℝ)) (X := (5006378670271269701/5000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(580778888285887/10000000000000000000 : ℝ) ≤ ((18276522656146349547/18282500000000000000 : ℝ)+2*(1421610078309/731300000000000 : ℝ)*(4571/50000 : ℝ))^(4175/1024 : ℝ) := by
    rw [show (18276522656146349547/18282500000000000000 : ℝ)+2*(1421610078309/731300000000000 : ℝ)*(4571/50000 : ℝ)=(1250035610270361/1250000000000000 : ℝ) by norm_num, show 1+2*(580778888285887/10000000000000000000 : ℝ)=(5000580778888285887/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6378670271269701/10000000000000000000 : ℝ)+(580778888285887/10000000000000000000 : ℝ) ≤ ((18276522656146349547/18282500000000000000 : ℝ)+(1421610078309/731300000000000 : ℝ)*((3291/20000 : ℝ)+(4571/50000 : ℝ)))^(4175/1024 : ℝ) := by
    rw [show (18276522656146349547/18282500000000000000 : ℝ)+(1421610078309/731300000000000 : ℝ)*((3291/20000 : ℝ)+(4571/50000 : ℝ))=(10001706492241197/10000000000000000 : ℝ) by norm_num, show 1+(6378670271269701/10000000000000000000 : ℝ)+(580778888285887/10000000000000000000 : ℝ)=(2501739862289888897/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6378670271269701/10000000000000000000 : ℝ) ≤ ((18276522656146349547/18282500000000000000 : ℝ)+2*(1421610078309/731300000000000 : ℝ)*(3291/20000 : ℝ))^(4175/1024 : ℝ) := by
    rw [show (18276522656146349547/18282500000000000000 : ℝ)+2*(1421610078309/731300000000000 : ℝ)*(3291/20000 : ℝ)=(5001564051159753/5000000000000000 : ℝ) by norm_num, show 1+2*(6378670271269701/10000000000000000000 : ℝ)=(5006378670271269701/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18276522656146349547/18282500000000000000 : ℝ)*(X 1 0+X 2 0)+(1421610078309/731300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (4571/50000 : ℝ)) (hi := (3291/20000 : ℝ)) (c := (18276522656146349547/18282500000000000000 : ℝ)) (alpha := (1421610078309/731300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18276522656146349547/18282500000000000000 : ℝ)*(X 0 1+X 2 1)+(1421610078309/731300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (4571/50000 : ℝ)) (hi := (3291/20000 : ℝ)) (c := (18276522656146349547/18282500000000000000 : ℝ)) (alpha := (1421610078309/731300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18276522656146349547/18282500000000000000 : ℝ)*(X 0 2+X 1 2)+(1421610078309/731300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (4571/50000 : ℝ)) (hi := (3291/20000 : ℝ)) (c := (18276522656146349547/18282500000000000000 : ℝ)) (alpha := (1421610078309/731300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2155629143/10000000000 : ℝ)*X 0 0+(5427546253/10000000000 : ℝ)*X 0 1+(5233568543/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353410939/10000000000 : ℝ)*X 1 0+(-2254749581/10000000000 : ℝ)*X 1 1+(2616784177/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353411019/10000000000 : ℝ)*X 2 0+(523356839/1000000000 : ℝ)*X 2 1+(-2254749427/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2180133447/5000000000 : ℝ)*X 0 0+(4170957999/10000000000 : ℝ)*X 0 1+(2279041529/5000000000 : ℝ)*X 0 2+(2180133447/5000000000 : ℝ)*X 1 0+(4170957999/10000000000 : ℝ)*X 1 1+(2279041529/5000000000 : ℝ)*X 1 2+(2180133447/5000000000 : ℝ)*X 2 0+(4170957999/10000000000 : ℝ)*X 2 1+(2279041529/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-431129287/2000000000 : ℝ)*X 0 0+(81786137/156250000 : ℝ)*X 0 1+(5426797933/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165756571/312500000 : ℝ)*X 1 0+(-1030760239/5000000000 : ℝ)*X 1 1+(5426797749/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326052761/2500000000 : ℝ)*X 2 0+(5426797147/10000000000 : ℝ)*X 2 1+(-515380063/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((436030121/1000000000 : ℝ)*X 0 0+(455659789/1000000000 : ℝ)*X 0 1+(2086225819/5000000000 : ℝ)*X 0 2+(436030121/1000000000 : ℝ)*X 1 0+(455659789/1000000000 : ℝ)*X 1 1+(2086225819/5000000000 : ℝ)*X 1 2+(436030121/1000000000 : ℝ)*X 2 0+(455659789/1000000000 : ℝ)*X 2 1+(2086225819/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (304897743186897774928608897/57132812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (13824533/1000000000000 : ℝ)*(base19) + (664835733/50000000000000 : ℝ)*(base23) + (13899697/20000000000000 : ℝ)*(lower2) + (42004817/50000000000000 : ℝ)*(upper3) + (82249411/50000000000000 : ℝ)*(upper5) + (483652688355947/12500000000000 : ℝ)*(major0) + (483652688355947/12500000000000 : ℝ)*(major1) + (483652688355947/12500000000000 : ℝ)*(major2) + (206210061073913/4000000000000 : ℝ)*(sp0) + (5155274855571233/100000000000000 : ℝ)*(sp1) + (5155274908353067/100000000000000 : ℝ)*(sp2) + (161447232349071/6250000000000 : ℝ)*(sp3) + (6177794177/25000000000000 : ℝ)*(sp4) + (10880197187/100000000000000 : ℝ)*(sp7) + (645791649445581/25000000000000 : ℝ)*(f.failure) + (5155276238024533/100000000000000 : ℝ)*(f.sum) + (321627886562049/36565000000000000000000000000 : ℝ)*base65 + (812791065395687259/228531250000000000000000000000000 : ℝ)*base67 + (3044379074814124759/228531250000000000000000000000000 : ℝ)*base69 + (2243738143963999759/228531250000000000000000000000000 : ℝ)*base71 + (247845163942619/36565000000000000000000000000 : ℝ)*base73 + (1266075278121656009/228531250000000000000000000000000 : ℝ)*base75 + (4486926053179062259/228531250000000000000000000000000 : ℝ)*base77 + (368938891774031009/228531250000000000000000000000000 : ℝ)*base79 + (229745830313459/36565000000000000000000000000 : ℝ)*base81 + (35443/19531250000000000000 : ℝ)*base89 + (35443/19531250000000000000 : ℝ)*base91 + (35443/19531250000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (67931443465559374480251711/9141250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1248167699/100000000000000 : ℝ)*(base19) + (431702423/20000000000000 : ℝ)*(base23) + (104926839/100000000000000 : ℝ)*(upper3) + (34299043/100000000000000 : ℝ)*(lower4) + (143738693/100000000000000 : ℝ)*(upper5) + (77983894225979/2000000000000 : ℝ)*(major0) + (77983894225979/2000000000000 : ℝ)*(major1) + (77983894225979/2000000000000 : ℝ)*(major2) + (19163419419/100000000000000 : ℝ)*(sp1) + (14408735691/50000000000000 : ℝ)*(sp2) + (2597605945044887/50000000000000 : ℝ)*(sp4) + (20293716712901/390625000000 : ℝ)*(sp5) + (5195180914106277/100000000000000 : ℝ)*(sp6) + (520635456959571/20000000000000 : ℝ)*(sp7) + (520635456959571/20000000000000 : ℝ)*(f.failure) + (2597605945044887/50000000000000 : ℝ)*(f.sum) + (94481018193/731300000000000000000000000 : ℝ)*base65 + (343116377812226513/36565000000000000000000000000000 : ℝ)*base67 + (387326634825976513/36565000000000000000000000000000 : ℝ)*base69 + (163708338998061513/36565000000000000000000000000000 : ℝ)*base71 + (8829876312951/7313000000000000000000000000 : ℝ)*base73 + (67949684230343487/36565000000000000000000000000000 : ℝ)*base76 + (364268293736316513/36565000000000000000000000000000 : ℝ)*base77 + (199460819869371513/36565000000000000000000000000000 : ℝ)*base79 + (18963968247963/3656500000000000000000000000 : ℝ)*base82 + (74587/15625000000000000000 : ℝ)*base90 + (74587/15625000000000000000 : ℝ)*base92 + (74587/15625000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1158_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3291/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4571/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5341/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14787/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1158_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1158_s4_0 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2158503311/10000000000 : ℝ)*x 0 + (5401135963/10000000000 : ℝ)*x 1 + (1314524559/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158503311/10000000000 : ℝ)^8351 ≤ (13116033939037/100000000000000 : ℝ)^6303 := by
    have hnat : (2158503311 : ℕ)^8351*100000000000000^6303 ≤ 13116033939037^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158503311 10000000000 13116033939037 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401135963/10000000000 : ℝ)^8351 ≤ (8842863607391/20000000000000 : ℝ)^6303 := by
    have hnat : (5401135963 : ℕ)^8351*20000000000000^6303 ≤ 8842863607391^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401135963 10000000000 8842863607391 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1314524559/2500000000 : ℝ)^8351 ≤ (10667412004841/25000000000000 : ℝ)^6303 := by
    have hnat : (1314524559 : ℕ)^8351*25000000000000^6303 ≤ 10667412004841^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314524559 2500000000 10667412004841 25000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2158503311/10000000000 : ℝ), (5401135963/10000000000 : ℝ), (1314524559/2500000000 : ℝ)] ![(13116033939037/100000000000000 : ℝ), (8842863607391/20000000000000 : ℝ), (10667412004841/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2158503311/10000000000 : ℝ)|^8351 ≤ (13116033939037/100000000000000 : ℝ)^6303
        have hw : |(-2158503311/10000000000 : ℝ)|=(2158503311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401135963/10000000000 : ℝ)|^8351 ≤ (8842863607391/20000000000000 : ℝ)^6303
        have hw : |(5401135963/10000000000 : ℝ)|=(5401135963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1314524559/2500000000 : ℝ)|^8351 ≤ (10667412004841/25000000000000 : ℝ)^6303
        have hw : |(1314524559/2500000000 : ℝ)|=(1314524559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s4_1 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (213872223/400000000 : ℝ)*x 0 + (-2231181759/10000000000 : ℝ)*x 1 + (5258098447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213872223/400000000 : ℝ)^8351 ≤ (2181300832311/5000000000000 : ℝ)^6303 := by
    have hnat : (213872223 : ℕ)^8351*5000000000000^6303 ≤ 2181300832311^6303*400000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213872223 400000000 2181300832311 5000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2231181759/10000000000 : ℝ)^8351 ≤ (13704333054991/100000000000000 : ℝ)^6303 := by
    have hnat : (2231181759 : ℕ)^8351*100000000000000^6303 ≤ 13704333054991^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2231181759 10000000000 13704333054991 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5258098447/10000000000 : ℝ)^8351 ≤ (10667412571999/25000000000000 : ℝ)^6303 := by
    have hnat : (5258098447 : ℕ)^8351*25000000000000^6303 ≤ 10667412571999^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258098447 10000000000 10667412571999 25000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213872223/400000000 : ℝ), (-2231181759/10000000000 : ℝ), (5258098447/10000000000 : ℝ)] ![(2181300832311/5000000000000 : ℝ), (13704333054991/100000000000000 : ℝ), (10667412571999/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213872223/400000000 : ℝ)|^8351 ≤ (2181300832311/5000000000000 : ℝ)^6303
        have hw : |(213872223/400000000 : ℝ)|=(213872223/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2231181759/10000000000 : ℝ)|^8351 ≤ (13704333054991/100000000000000 : ℝ)^6303
        have hw : |(-2231181759/10000000000 : ℝ)|=(2231181759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5258098447/10000000000 : ℝ)|^8351 ≤ (10667412571999/25000000000000 : ℝ)^6303
        have hw : |(5258098447/10000000000 : ℝ)|=(5258098447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s4_2 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668350699/1250000000 : ℝ)*x 0 + (1051619713/2000000000 : ℝ)*x 1 + (-2231181581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668350699/1250000000 : ℝ)^8351 ≤ (43626016829997/100000000000000 : ℝ)^6303 := by
    have hnat : (668350699 : ℕ)^8351*100000000000000^6303 ≤ 43626016829997^6303*1250000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668350699 1250000000 43626016829997 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051619713/2000000000 : ℝ)^8351 ≤ (42669651556709/100000000000000 : ℝ)^6303 := by
    have hnat : (1051619713 : ℕ)^8351*100000000000000^6303 ≤ 42669651556709^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051619713 2000000000 42669651556709 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2231181581/10000000000 : ℝ)^8351 ≤ (13704331606439/100000000000000 : ℝ)^6303 := by
    have hnat : (2231181581 : ℕ)^8351*100000000000000^6303 ≤ 13704331606439^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2231181581 10000000000 13704331606439 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668350699/1250000000 : ℝ), (1051619713/2000000000 : ℝ), (-2231181581/10000000000 : ℝ)] ![(43626016829997/100000000000000 : ℝ), (42669651556709/100000000000000 : ℝ), (13704331606439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668350699/1250000000 : ℝ)|^8351 ≤ (43626016829997/100000000000000 : ℝ)^6303
        have hw : |(668350699/1250000000 : ℝ)|=(668350699/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1051619713/2000000000 : ℝ)|^8351 ≤ (42669651556709/100000000000000 : ℝ)^6303
        have hw : |(1051619713/2000000000 : ℝ)|=(1051619713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2231181581/10000000000 : ℝ)|^8351 ≤ (13704331606439/100000000000000 : ℝ)^6303
        have hw : |(-2231181581/10000000000 : ℝ)|=(2231181581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s4_3 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (109049613/250000000 : ℝ)*x 0 + (527695867/1250000000 : ℝ)*x 1 + (1126757461/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109049613/250000000 : ℝ)^8351 ≤ (33312606341921/100000000000000 : ℝ)^6303 := by
    have hnat : (109049613 : ℕ)^8351*100000000000000^6303 ≤ 33312606341921^6303*250000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109049613 250000000 33312606341921 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527695867/1250000000 : ℝ)^8351 ≤ (15949638883253/50000000000000 : ℝ)^6303 := by
    have hnat : (527695867 : ℕ)^8351*50000000000000^6303 ≤ 15949638883253^6303*1250000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527695867 1250000000 15949638883253 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126757461/2500000000 : ℝ)^8351 ≤ (1087128621039/3125000000000 : ℝ)^6303 := by
    have hnat : (1126757461 : ℕ)^8351*3125000000000^6303 ≤ 1087128621039^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126757461 2500000000 1087128621039 3125000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(109049613/250000000 : ℝ), (527695867/1250000000 : ℝ), (1126757461/2500000000 : ℝ)] ![(33312606341921/100000000000000 : ℝ), (15949638883253/50000000000000 : ℝ), (1087128621039/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(109049613/250000000 : ℝ)|^8351 ≤ (33312606341921/100000000000000 : ℝ)^6303
        have hw : |(109049613/250000000 : ℝ)|=(109049613/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(527695867/1250000000 : ℝ)|^8351 ≤ (15949638883253/50000000000000 : ℝ)^6303
        have hw : |(527695867/1250000000 : ℝ)|=(527695867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1126757461/2500000000 : ℝ)|^8351 ≤ (1087128621039/3125000000000 : ℝ)^6303
        have hw : |(1126757461/2500000000 : ℝ)|=(1126757461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s4_4 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1079255143/5000000000 : ℝ)*x 0 + (2629252037/5000000000 : ℝ)*x 1 + (5400728461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079255143/5000000000 : ℝ)^8351 ≤ (13116090093649/100000000000000 : ℝ)^6303 := by
    have hnat : (1079255143 : ℕ)^8351*100000000000000^6303 ≤ 13116090093649^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079255143 5000000000 13116090093649 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2629252037/5000000000 : ℝ)^8351 ≤ (8534802313349/20000000000000 : ℝ)^6303 := by
    have hnat : (2629252037 : ℕ)^8351*20000000000000^6303 ≤ 8534802313349^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629252037 5000000000 8534802313349 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400728461/10000000000 : ℝ)^8351 ≤ (44209898330571/100000000000000 : ℝ)^6303 := by
    have hnat : (5400728461 : ℕ)^8351*100000000000000^6303 ≤ 44209898330571^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400728461 10000000000 44209898330571 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1079255143/5000000000 : ℝ), (2629252037/5000000000 : ℝ), (5400728461/10000000000 : ℝ)] ![(13116090093649/100000000000000 : ℝ), (8534802313349/20000000000000 : ℝ), (44209898330571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1079255143/5000000000 : ℝ)|^8351 ≤ (13116090093649/100000000000000 : ℝ)^6303
        have hw : |(-1079255143/5000000000 : ℝ)|=(1079255143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2629252037/5000000000 : ℝ)|^8351 ≤ (8534802313349/20000000000000 : ℝ)^6303
        have hw : |(2629252037/5000000000 : ℝ)|=(2629252037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400728461/10000000000 : ℝ)|^8351 ≤ (44209898330571/100000000000000 : ℝ)^6303
        have hw : |(5400728461/10000000000 : ℝ)|=(5400728461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s4_5 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062105087/2000000000 : ℝ)*x 0 + (-2088552019/10000000000 : ℝ)*x 1 + (5400728537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062105087/2000000000 : ℝ)^8351 ≤ (43234246310843/100000000000000 : ℝ)^6303 := by
    have hnat : (1062105087 : ℕ)^8351*100000000000000^6303 ≤ 43234246310843^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062105087 2000000000 43234246310843 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2088552019/10000000000 : ℝ)^8351 ≤ (1569481815113/12500000000000 : ℝ)^6303 := by
    have hnat : (2088552019 : ℕ)^8351*12500000000000^6303 ≤ 1569481815113^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088552019 10000000000 1569481815113 12500000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400728537/10000000000 : ℝ)^8351 ≤ (22104949577423/50000000000000 : ℝ)^6303 := by
    have hnat : (5400728537 : ℕ)^8351*50000000000000^6303 ≤ 22104949577423^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400728537 10000000000 22104949577423 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062105087/2000000000 : ℝ), (-2088552019/10000000000 : ℝ), (5400728537/10000000000 : ℝ)] ![(43234246310843/100000000000000 : ℝ), (1569481815113/12500000000000 : ℝ), (22104949577423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062105087/2000000000 : ℝ)|^8351 ≤ (43234246310843/100000000000000 : ℝ)^6303
        have hw : |(1062105087/2000000000 : ℝ)|=(1062105087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2088552019/10000000000 : ℝ)|^8351 ≤ (1569481815113/12500000000000 : ℝ)^6303
        have hw : |(-2088552019/10000000000 : ℝ)|=(2088552019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400728537/10000000000 : ℝ)|^8351 ≤ (22104949577423/50000000000000 : ℝ)^6303
        have hw : |(5400728537/10000000000 : ℝ)|=(5400728537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s4_6 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310525403/10000000000 : ℝ)*x 0 + (5400728983/10000000000 : ℝ)*x 1 + (-1044275727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310525403/10000000000 : ℝ)^8351 ≤ (21617122982837/50000000000000 : ℝ)^6303 := by
    have hnat : (5310525403 : ℕ)^8351*50000000000000^6303 ≤ 21617122982837^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310525403 10000000000 21617122982837 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400728983/10000000000 : ℝ)^8351 ≤ (44209903992037/100000000000000 : ℝ)^6303 := by
    have hnat : (5400728983 : ℕ)^8351*100000000000000^6303 ≤ 44209903992037^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400728983 10000000000 44209903992037 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044275727/5000000000 : ℝ)^8351 ≤ (12555850020613/100000000000000 : ℝ)^6303 := by
    have hnat : (1044275727 : ℕ)^8351*100000000000000^6303 ≤ 12555850020613^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044275727 5000000000 12555850020613 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310525403/10000000000 : ℝ), (5400728983/10000000000 : ℝ), (-1044275727/5000000000 : ℝ)] ![(21617122982837/50000000000000 : ℝ), (44209903992037/100000000000000 : ℝ), (12555850020613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310525403/10000000000 : ℝ)|^8351 ≤ (21617122982837/50000000000000 : ℝ)^6303
        have hw : |(5310525403/10000000000 : ℝ)|=(5310525403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400728983/10000000000 : ℝ)|^8351 ≤ (44209903992037/100000000000000 : ℝ)^6303
        have hw : |(5400728983/10000000000 : ℝ)|=(5400728983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1044275727/5000000000 : ℝ)|^8351 ≤ (12555850020613/100000000000000 : ℝ)^6303
        have hw : |(-1044275727/5000000000 : ℝ)|=(1044275727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s4_7 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4361998221/10000000000 : ℝ)*x 0 + (112655523/250000000 : ℝ)*x 1 + (2111189673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361998221/10000000000 : ℝ)^8351 ≤ (33312744975411/100000000000000 : ℝ)^6303 := by
    have hnat : (4361998221 : ℕ)^8351*100000000000000^6303 ≤ 33312744975411^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361998221 10000000000 33312744975411 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112655523/250000000 : ℝ)^8351 ≤ (6955968713007/20000000000000 : ℝ)^6303 := by
    have hnat : (112655523 : ℕ)^8351*20000000000000^6303 ≤ 6955968713007^6303*250000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112655523 250000000 6955968713007 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111189673/5000000000 : ℝ)^8351 ≤ (31907411448431/100000000000000 : ℝ)^6303 := by
    have hnat : (2111189673 : ℕ)^8351*100000000000000^6303 ≤ 31907411448431^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111189673 5000000000 31907411448431 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361998221/10000000000 : ℝ), (112655523/250000000 : ℝ), (2111189673/5000000000 : ℝ)] ![(33312744975411/100000000000000 : ℝ), (6955968713007/20000000000000 : ℝ), (31907411448431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361998221/10000000000 : ℝ)|^8351 ≤ (33312744975411/100000000000000 : ℝ)^6303
        have hw : |(4361998221/10000000000 : ℝ)|=(4361998221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(112655523/250000000 : ℝ)|^8351 ≤ (6955968713007/20000000000000 : ℝ)^6303
        have hw : |(112655523/250000000 : ℝ)|=(112655523/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2111189673/5000000000 : ℝ)|^8351 ≤ (31907411448431/100000000000000 : ℝ)^6303
        have hw : |(2111189673/5000000000 : ℝ)|=(2111189673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1158_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14787/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5341/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2241/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14787/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5341/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14787/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5341/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14787/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5341/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14787/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5341/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14787/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5341/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14787/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5341/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5341/50000 : ℝ) ^ (4175/1024 : ℝ) ≤ (684782062431191/6250000000000000000 : ℝ) := by
    have hpowers : (5341/50000 : ℝ)^4175 ≤ (684782062431191/6250000000000000000 : ℝ)^1024 := by
      have hnat : (5341 : ℕ)^4175*6250000000000000000^1024 ≤ 684782062431191^1024*50000^4175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5341 50000 684782062431191 6250000000000000000 4175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5341/50000 : ℝ)) (X := (684782062431191/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14787/100000 : ℝ) ^ (4175/1024 : ℝ) ≤ (41255118241087177/100000000000000000000 : ℝ) := by
    have hpowers : (14787/100000 : ℝ)^4175 ≤ (41255118241087177/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14787 : ℕ)^4175*100000000000000000000^1024 ≤ 41255118241087177^1024*100000^4175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14787 100000 41255118241087177 100000000000000000000 4175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14787/100000 : ℝ)) (X := (41255118241087177/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125684782062431191/3125000000000000000 : ℝ) ≤ (625033588448107/625000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (3125684782062431191/3125000000000000000 : ℝ)^1024 ≤ (625033588448107/625000000000000 : ℝ)^4175 := by
      have hnat : (3125684782062431191 : ℕ)^1024*625000000000000^4175 ≤ 625033588448107^4175*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125684782062431191 3125000000000000000 625033588448107 625000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625033588448107/625000000000000 : ℝ)) (X := (3125684782062431191/3125000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052211631239986233/100000000000000000000 : ℝ) ≤ (400051213585179/400000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (100052211631239986233/100000000000000000000 : ℝ)^1024 ≤ (400051213585179/400000000000000 : ℝ)^4175 := by
      have hnat : (100052211631239986233 : ℕ)^1024*400000000000000^4175 ≤ 400051213585179^4175*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052211631239986233 100000000000000000000 400051213585179 400000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400051213585179/400000000000000 : ℝ)) (X := (100052211631239986233/100000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50041255118241087177/50000000000000000000 : ℝ) ≤ (5001011632044619/5000000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (50041255118241087177/50000000000000000000 : ℝ)^1024 ≤ (5001011632044619/5000000000000000 : ℝ)^4175 := by
      have hnat : (50041255118241087177 : ℕ)^1024*5000000000000000^4175 ≤ 5001011632044619^4175*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50041255118241087177 50000000000000000000 5001011632044619 5000000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001011632044619/5000000000000000 : ℝ)) (X := (50041255118241087177/50000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(684782062431191/6250000000000000000 : ℝ) ≤ ((10259083562778322757/10262500000000000000 : ℝ)+2*(742924459763/410500000000000 : ℝ)*(5341/50000 : ℝ))^(4175/1024 : ℝ) := by
    rw [show (10259083562778322757/10262500000000000000 : ℝ)+2*(742924459763/410500000000000 : ℝ)*(5341/50000 : ℝ)=(625033588448107/625000000000000 : ℝ) by norm_num, show 1+2*(684782062431191/6250000000000000000 : ℝ)=(3125684782062431191/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(41255118241087177/100000000000000000000 : ℝ)+(684782062431191/6250000000000000000 : ℝ) ≤ ((10259083562778322757/10262500000000000000 : ℝ)+(742924459763/410500000000000 : ℝ)*((14787/100000 : ℝ)+(5341/50000 : ℝ)))^(4175/1024 : ℝ) := by
    rw [show (10259083562778322757/10262500000000000000 : ℝ)+(742924459763/410500000000000 : ℝ)*((14787/100000 : ℝ)+(5341/50000 : ℝ))=(400051213585179/400000000000000 : ℝ) by norm_num, show 1+(41255118241087177/100000000000000000000 : ℝ)+(684782062431191/6250000000000000000 : ℝ)=(100052211631239986233/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(41255118241087177/100000000000000000000 : ℝ) ≤ ((10259083562778322757/10262500000000000000 : ℝ)+2*(742924459763/410500000000000 : ℝ)*(14787/100000 : ℝ))^(4175/1024 : ℝ) := by
    rw [show (10259083562778322757/10262500000000000000 : ℝ)+2*(742924459763/410500000000000 : ℝ)*(14787/100000 : ℝ)=(5001011632044619/5000000000000000 : ℝ) by norm_num, show 1+2*(41255118241087177/100000000000000000000 : ℝ)=(50041255118241087177/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10259083562778322757/10262500000000000000 : ℝ)*(X 1 0+X 2 0)+(742924459763/410500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (5341/50000 : ℝ)) (hi := (14787/100000 : ℝ)) (c := (10259083562778322757/10262500000000000000 : ℝ)) (alpha := (742924459763/410500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10259083562778322757/10262500000000000000 : ℝ)*(X 0 1+X 2 1)+(742924459763/410500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (5341/50000 : ℝ)) (hi := (14787/100000 : ℝ)) (c := (10259083562778322757/10262500000000000000 : ℝ)) (alpha := (742924459763/410500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10259083562778322757/10262500000000000000 : ℝ)*(X 0 2+X 1 2)+(742924459763/410500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (5341/50000 : ℝ)) (hi := (14787/100000 : ℝ)) (c := (10259083562778322757/10262500000000000000 : ℝ)) (alpha := (742924459763/410500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2158503311/10000000000 : ℝ)*X 0 0+(5401135963/10000000000 : ℝ)*X 0 1+(1314524559/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((213872223/400000000 : ℝ)*X 1 0+(-2231181759/10000000000 : ℝ)*X 1 1+(5258098447/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668350699/1250000000 : ℝ)*X 2 0+(1051619713/2000000000 : ℝ)*X 2 1+(-2231181581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((109049613/250000000 : ℝ)*X 0 0+(527695867/1250000000 : ℝ)*X 0 1+(1126757461/2500000000 : ℝ)*X 0 2+(109049613/250000000 : ℝ)*X 1 0+(527695867/1250000000 : ℝ)*X 1 1+(1126757461/2500000000 : ℝ)*X 1 2+(109049613/250000000 : ℝ)*X 2 0+(527695867/1250000000 : ℝ)*X 2 1+(1126757461/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1079255143/5000000000 : ℝ)*X 0 0+(2629252037/5000000000 : ℝ)*X 0 1+(5400728461/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062105087/2000000000 : ℝ)*X 1 0+(-2088552019/10000000000 : ℝ)*X 1 1+(5400728537/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310525403/10000000000 : ℝ)*X 2 0+(5400728983/10000000000 : ℝ)*X 2 1+(-1044275727/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4361998221/10000000000 : ℝ)*X 0 0+(112655523/250000000 : ℝ)*X 0 1+(2111189673/5000000000 : ℝ)*X 0 2+(4361998221/10000000000 : ℝ)*X 1 0+(112655523/250000000 : ℝ)*X 1 1+(2111189673/5000000000 : ℝ)*X 1 2+(4361998221/10000000000 : ℝ)*X 2 0+(112655523/250000000 : ℝ)*X 2 1+(2111189673/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (214740869176158859156251/20525000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2102699577/100000000000000 : ℝ)*(base19) + (44128003/2500000000000 : ℝ)*(base23) + (38476469/20000000000000 : ℝ)*(lower2) + (273255577/100000000000000 : ℝ)*(upper3) + (131989493/50000000000000 : ℝ)*(upper5) + (655901075529659/12500000000000 : ℝ)*(major0) + (655901075529659/12500000000000 : ℝ)*(major1) + (655901075529659/12500000000000 : ℝ)*(major2) + (1747804629148257/25000000000000 : ℝ)*(sp0) + (1747819376180501/25000000000000 : ℝ)*(sp1) + (349563892115073/5000000000000 : ℝ)*(sp2) + (1751554283056177/50000000000000 : ℝ)*(sp3) + (7636353569/12500000000000 : ℝ)*(sp4) + (28686193757/100000000000000 : ℝ)*(sp7) + (54736519567283/1562500000000 : ℝ)*(f.failure) + (6991279607421581/100000000000000 : ℝ)*(f.sum) + (27263638928111/20525000000000000000000000000 : ℝ)*base65 + (365649285930449863/128281250000000000000000000000000 : ℝ)*base67 + (35255515395762363/128281250000000000000000000000000 : ℝ)*base69 + (1359685816335331387/128281250000000000000000000000000 : ℝ)*base72 + (37133726145959/5131250000000000000000000000 : ℝ)*base73 + (1254701989862637/128281250000000000000000000000000 : ℝ)*base76 + (162230636400956387/128281250000000000000000000000000 : ℝ)*base78 + (28267278079199863/128281250000000000000000000000000 : ℝ)*base79 + (112638645360793/10262500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (26921/4882812500000000000 : ℝ)*base89 + (26921/4882812500000000000 : ℝ)*base91 + (26921/4882812500000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3438462258944001279366911037/256562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (597629387/50000000000000 : ℝ)*(base19) + (441388347/25000000000000 : ℝ)*(base23) + (33518437/6250000000000 : ℝ)*(upper3) + (13699717/10000000000000 : ℝ)*(lower4) + (31449171/50000000000000 : ℝ)*(upper5) + (5277111285873653/100000000000000 : ℝ)*(major0) + (5277111285873653/100000000000000 : ℝ)*(major1) + (5277111285873653/100000000000000 : ℝ)*(major2) + (2344297967/50000000000000 : ℝ)*(sp1) + (3537900349/6250000000000 : ℝ)*(sp2) + (70311212680767/1000000000000 : ℝ)*(sp4) + (878889423027749/12500000000000 : ℝ)*(sp5) + (7031062896117727/100000000000000 : ℝ)*(sp6) + (704620171387151/20000000000000 : ℝ)*(sp7) + (704620171387151/20000000000000 : ℝ)*(f.failure) + (70311212680767/1000000000000 : ℝ)*(f.sum) + (7989162373659/5131250000000000000000000000 : ℝ)*base66 + (9133052007137403679/1026250000000000000000000000000000 : ℝ)*base68 + (10202109093950096321/1026250000000000000000000000000000 : ℝ)*base69 + (1995479817206346321/1026250000000000000000000000000000 : ℝ)*base71 + (82129379639911/20525000000000000000000000000 : ℝ)*base74 + (3539343627522596321/1026250000000000000000000000000000 : ℝ)*base75 + (8330063217057596321/1026250000000000000000000000000000 : ℝ)*base77 + (6945316755836346321/1026250000000000000000000000000000 : ℝ)*base79 + (11620217041461/20525000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (19597/15625000000000000000 : ℝ)*base90 + (19597/15625000000000000000 : ℝ)*base92 + (19597/15625000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1158_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14787/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5341/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1158_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1158_s5_0 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1079552909/5000000000 : ℝ)*x 0 + (5394501689/10000000000 : ℝ)*x 1 + (5264336911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079552909/5000000000 : ℝ)^8351 ≤ (820055302759/6250000000000 : ℝ)^6303 := by
    have hnat : (1079552909 : ℕ)^8351*6250000000000^6303 ≤ 820055302759^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079552909 5000000000 820055302759 6250000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394501689/10000000000 : ℝ)^8351 ≤ (44142377163941/100000000000000 : ℝ)^6303 := by
    have hnat : (5394501689 : ℕ)^8351*100000000000000^6303 ≤ 44142377163941^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394501689 10000000000 44142377163941 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264336911/10000000000 : ℝ)^8351 ≤ (10684184496939/25000000000000 : ℝ)^6303 := by
    have hnat : (5264336911 : ℕ)^8351*25000000000000^6303 ≤ 10684184496939^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264336911 10000000000 10684184496939 25000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1079552909/5000000000 : ℝ), (5394501689/10000000000 : ℝ), (5264336911/10000000000 : ℝ)] ![(820055302759/6250000000000 : ℝ), (44142377163941/100000000000000 : ℝ), (10684184496939/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1079552909/5000000000 : ℝ)|^8351 ≤ (820055302759/6250000000000 : ℝ)^6303
        have hw : |(-1079552909/5000000000 : ℝ)|=(1079552909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394501689/10000000000 : ℝ)|^8351 ≤ (44142377163941/100000000000000 : ℝ)^6303
        have hw : |(5394501689/10000000000 : ℝ)|=(5394501689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264336911/10000000000 : ℝ)|^8351 ≤ (10684184496939/25000000000000 : ℝ)^6303
        have hw : |(5264336911/10000000000 : ℝ)|=(5264336911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s5_1 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336284813/2500000000 : ℝ)*x 0 + (-445029731/2000000000 : ℝ)*x 1 + (658042119/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336284813/2500000000 : ℝ)^8351 ≤ (43608003916063/100000000000000 : ℝ)^6303 := by
    have hnat : (1336284813 : ℕ)^8351*100000000000000^6303 ≤ 43608003916063^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336284813 2500000000 43608003916063 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (445029731/2000000000 : ℝ)^8351 ≤ (2731051527569/20000000000000 : ℝ)^6303 := by
    have hnat : (445029731 : ℕ)^8351*20000000000000^6303 ≤ 2731051527569^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445029731 2000000000 2731051527569 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658042119/1250000000 : ℝ)^8351 ≤ (34189390743/80000000000 : ℝ)^6303 := by
    have hnat : (658042119 : ℕ)^8351*80000000000^6303 ≤ 34189390743^6303*1250000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658042119 1250000000 34189390743 80000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336284813/2500000000 : ℝ), (-445029731/2000000000 : ℝ), (658042119/1250000000 : ℝ)] ![(43608003916063/100000000000000 : ℝ), (2731051527569/20000000000000 : ℝ), (34189390743/80000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336284813/2500000000 : ℝ)|^8351 ≤ (43608003916063/100000000000000 : ℝ)^6303
        have hw : |(1336284813/2500000000 : ℝ)|=(1336284813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-445029731/2000000000 : ℝ)|^8351 ≤ (2731051527569/20000000000000 : ℝ)^6303
        have hw : |(-445029731/2000000000 : ℝ)|=(445029731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658042119/1250000000 : ℝ)|^8351 ≤ (34189390743/80000000000 : ℝ)^6303
        have hw : |(658042119/1250000000 : ℝ)|=(658042119/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s5_2 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345139337/10000000000 : ℝ)*x 0 + (526433691/1000000000 : ℝ)*x 1 + (-1112574299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345139337/10000000000 : ℝ)^8351 ≤ (8721600966971/20000000000000 : ℝ)^6303 := by
    have hnat : (5345139337 : ℕ)^8351*20000000000000^6303 ≤ 8721600966971^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345139337 10000000000 8721600966971 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526433691/1000000000 : ℝ)^8351 ≤ (42736737977/100000000000 : ℝ)^6303 := by
    have hnat : (526433691 : ℕ)^8351*100000000000^6303 ≤ 42736737977^6303*1000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526433691 1000000000 42736737977 100000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1112574299/5000000000 : ℝ)^8351 ≤ (13655257174391/100000000000000 : ℝ)^6303 := by
    have hnat : (1112574299 : ℕ)^8351*100000000000000^6303 ≤ 13655257174391^6303*5000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112574299 5000000000 13655257174391 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345139337/10000000000 : ℝ), (526433691/1000000000 : ℝ), (-1112574299/5000000000 : ℝ)] ![(8721600966971/20000000000000 : ℝ), (42736737977/100000000000 : ℝ), (13655257174391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345139337/10000000000 : ℝ)|^8351 ≤ (8721600966971/20000000000000 : ℝ)^6303
        have hw : |(5345139337/10000000000 : ℝ)|=(5345139337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526433691/1000000000 : ℝ)|^8351 ≤ (42736737977/100000000000 : ℝ)^6303
        have hw : |(526433691/1000000000 : ℝ)|=(526433691/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1112574299/5000000000 : ℝ)|^8351 ≤ (13655257174391/100000000000000 : ℝ)^6303
        have hw : |(-1112574299/5000000000 : ℝ)|=(1112574299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s5_3 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4362336241/10000000000 : ℝ)*x 0 + (846873351/2000000000 : ℝ)*x 1 + (898827823/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362336241/10000000000 : ℝ)^8351 ≤ (6663233054731/20000000000000 : ℝ)^6303 := by
    have hnat : (4362336241 : ℕ)^8351*20000000000000^6303 ≤ 6663233054731^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362336241 10000000000 6663233054731 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846873351/2000000000 : ℝ)^8351 ≤ (32027485996623/100000000000000 : ℝ)^6303 := by
    have hnat : (846873351 : ℕ)^8351*100000000000000^6303 ≤ 32027485996623^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846873351 2000000000 32027485996623 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898827823/2000000000 : ℝ)^8351 ≤ (17328174361911/50000000000000 : ℝ)^6303 := by
    have hnat : (898827823 : ℕ)^8351*50000000000000^6303 ≤ 17328174361911^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898827823 2000000000 17328174361911 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362336241/10000000000 : ℝ), (846873351/2000000000 : ℝ), (898827823/2000000000 : ℝ)] ![(6663233054731/20000000000000 : ℝ), (32027485996623/100000000000000 : ℝ), (17328174361911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362336241/10000000000 : ℝ)|^8351 ≤ (6663233054731/20000000000000 : ℝ)^6303
        have hw : |(4362336241/10000000000 : ℝ)|=(4362336241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846873351/2000000000 : ℝ)|^8351 ≤ (32027485996623/100000000000000 : ℝ)^6303
        have hw : |(846873351/2000000000 : ℝ)|=(846873351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(898827823/2000000000 : ℝ)|^8351 ≤ (17328174361911/50000000000000 : ℝ)^6303
        have hw : |(898827823/2000000000 : ℝ)|=(898827823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s5_4 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2159110849/10000000000 : ℝ)*x 0 + (5264673241/10000000000 : ℝ)*x 1 + (5394164273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159110849/10000000000 : ℝ)^8351 ≤ (13120925351589/100000000000000 : ℝ)^6303 := by
    have hnat : (2159110849 : ℕ)^8351*100000000000000^6303 ≤ 13120925351589^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159110849 10000000000 13120925351589 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264673241/10000000000 : ℝ)^8351 ≤ (42740355574769/100000000000000 : ℝ)^6303 := by
    have hnat : (5264673241 : ℕ)^8351*100000000000000^6303 ≤ 42740355574769^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264673241 10000000000 42740355574769 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394164273/10000000000 : ℝ)^8351 ≤ (44138719053443/100000000000000 : ℝ)^6303 := by
    have hnat : (5394164273 : ℕ)^8351*100000000000000^6303 ≤ 44138719053443^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394164273 10000000000 44138719053443 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2159110849/10000000000 : ℝ), (5264673241/10000000000 : ℝ), (5394164273/10000000000 : ℝ)] ![(13120925351589/100000000000000 : ℝ), (42740355574769/100000000000000 : ℝ), (44138719053443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2159110849/10000000000 : ℝ)|^8351 ≤ (13120925351589/100000000000000 : ℝ)^6303
        have hw : |(-2159110849/10000000000 : ℝ)|=(2159110849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264673241/10000000000 : ℝ)|^8351 ≤ (42740355574769/100000000000000 : ℝ)^6303
        have hw : |(5264673241/10000000000 : ℝ)|=(5264673241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394164273/10000000000 : ℝ)|^8351 ≤ (44138719053443/100000000000000 : ℝ)^6303
        have hw : |(5394164273/10000000000 : ℝ)|=(5394164273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s5_5 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312123183/10000000000 : ℝ)*x 0 + (-419064191/2000000000 : ℝ)*x 1 + (13485411/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312123183/10000000000 : ℝ)^8351 ≤ (43251481302771/100000000000000 : ℝ)^6303 := by
    have hnat : (5312123183 : ℕ)^8351*100000000000000^6303 ≤ 43251481302771^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312123183 10000000000 43251481302771 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (419064191/2000000000 : ℝ)^8351 ≤ (2521959651047/20000000000000 : ℝ)^6303 := by
    have hnat : (419064191 : ℕ)^8351*20000000000000^6303 ≤ 2521959651047^6303*2000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419064191 2000000000 2521959651047 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13485411/25000000 : ℝ)^8351 ≤ (8827744086061/20000000000000 : ℝ)^6303 := by
    have hnat : (13485411 : ℕ)^8351*20000000000000^6303 ≤ 8827744086061^6303*25000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13485411 25000000 8827744086061 20000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312123183/10000000000 : ℝ), (-419064191/2000000000 : ℝ), (13485411/25000000 : ℝ)] ![(43251481302771/100000000000000 : ℝ), (2521959651047/20000000000000 : ℝ), (8827744086061/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312123183/10000000000 : ℝ)|^8351 ≤ (43251481302771/100000000000000 : ℝ)^6303
        have hw : |(5312123183/10000000000 : ℝ)|=(5312123183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-419064191/2000000000 : ℝ)|^8351 ≤ (2521959651047/20000000000000 : ℝ)^6303
        have hw : |(-419064191/2000000000 : ℝ)|=(419064191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13485411/25000000 : ℝ)|^8351 ≤ (8827744086061/20000000000000 : ℝ)^6303
        have hw : |(13485411/25000000 : ℝ)|=(13485411/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s5_6 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312122897/10000000000 : ℝ)*x 0 + (43153317/80000000 : ℝ)*x 1 + (-523830259/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312122897/10000000000 : ℝ)^8351 ≤ (43251478217523/100000000000000 : ℝ)^6303 := by
    have hnat : (5312122897 : ℕ)^8351*100000000000000^6303 ≤ 43251478217523^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312122897 10000000000 43251478217523 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43153317/80000000 : ℝ)^8351 ≤ (11034680717407/25000000000000 : ℝ)^6303 := by
    have hnat : (43153317 : ℕ)^8351*25000000000000^6303 ≤ 11034680717407^6303*80000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43153317 80000000 11034680717407 25000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523830259/2500000000 : ℝ)^8351 ≤ (12609798901089/100000000000000 : ℝ)^6303 := by
    have hnat : (523830259 : ℕ)^8351*100000000000000^6303 ≤ 12609798901089^6303*2500000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523830259 2500000000 12609798901089 100000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312122897/10000000000 : ℝ), (43153317/80000000 : ℝ), (-523830259/2500000000 : ℝ)] ![(43251478217523/100000000000000 : ℝ), (11034680717407/25000000000000 : ℝ), (12609798901089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312122897/10000000000 : ℝ)|^8351 ≤ (43251478217523/100000000000000 : ℝ)^6303
        have hw : |(5312122897/10000000000 : ℝ)|=(5312122897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43153317/80000000 : ℝ)|^8351 ≤ (11034680717407/25000000000000 : ℝ)^6303
        have hw : |(43153317/80000000 : ℝ)|=(43153317/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-523830259/2500000000 : ℝ)|^8351 ≤ (12609798901089/100000000000000 : ℝ)^6303
        have hw : |(-523830259/2500000000 : ℝ)|=(523830259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1158_s5_7 (p : ℝ) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4362346747/10000000000 : ℝ)*x 0 + (4493468429/10000000000 : ℝ)*x 1 + (4235039899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362346747/10000000000 : ℝ)^8351 ≤ (2082266973833/6250000000000 : ℝ)^6303 := by
    have hnat : (4362346747 : ℕ)^8351*6250000000000^6303 ≤ 2082266973833^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362346747 10000000000 2082266973833 6250000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4493468429/10000000000 : ℝ)^8351 ≤ (17324748213393/50000000000000 : ℝ)^6303 := by
    have hnat : (4493468429 : ℕ)^8351*50000000000000^6303 ≤ 17324748213393^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493468429 10000000000 17324748213393 50000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4235039899/10000000000 : ℝ)^8351 ≤ (1601711598599/5000000000000 : ℝ)^6303 := by
    have hnat : (4235039899 : ℕ)^8351*5000000000000^6303 ≤ 1601711598599^6303*10000000000^8351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235039899 10000000000 1601711598599 5000000000000 8351 6303 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8351/2048 : ℝ)) 8351 6303 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362346747/10000000000 : ℝ), (4493468429/10000000000 : ℝ), (4235039899/10000000000 : ℝ)] ![(2082266973833/6250000000000 : ℝ), (17324748213393/50000000000000 : ℝ), (1601711598599/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362346747/10000000000 : ℝ)|^8351 ≤ (2082266973833/6250000000000 : ℝ)^6303
        have hw : |(4362346747/10000000000 : ℝ)|=(4362346747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4493468429/10000000000 : ℝ)|^8351 ≤ (17324748213393/50000000000000 : ℝ)^6303
        have hw : |(4493468429/10000000000 : ℝ)|=(4493468429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4235039899/10000000000 : ℝ)|^8351 ≤ (1601711598599/5000000000000 : ℝ)^6303
        have hw : |(4235039899/10000000000 : ℝ)|=(4235039899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1158_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5669/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2819/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2241/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2241/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2241/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2241/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2241/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2241/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2241/20000 : ℝ) ^ (4175/1024 : ℝ) ≤ (1664259584929711/12500000000000000000 : ℝ) := by
    have hpowers : (2241/20000 : ℝ)^4175 ≤ (1664259584929711/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2241 : ℕ)^4175*12500000000000000000^1024 ≤ 1664259584929711^1024*20000^4175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2241 20000 1664259584929711 12500000000000000000 4175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2241/20000 : ℝ)) (X := (1664259584929711/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (4175/1024 : ℝ) ≤ (35327486388662819/100000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^4175 ≤ (35327486388662819/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2847 : ℕ)^4175*100000000000000000000^1024 ≤ 35327486388662819^1024*20000^4175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 35327486388662819 100000000000000000000 4175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (35327486388662819/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251664259584929711/6250000000000000000 : ℝ) ≤ (2000130608332971/2000000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (6251664259584929711/6250000000000000000 : ℝ)^1024 ≤ (2000130608332971/2000000000000000 : ℝ)^4175 := by
      have hnat : (6251664259584929711 : ℕ)^1024*2000000000000000^4175 ≤ 2000130608332971^4175*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251664259584929711 6250000000000000000 2000130608332971 2000000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000130608332971/2000000000000000 : ℝ)) (X := (6251664259584929711/6250000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048641563068100507/100000000000000000000 : ℝ) ≤ (10001192810070187/10000000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (100048641563068100507/100000000000000000000 : ℝ)^1024 ≤ (10001192810070187/10000000000000000 : ℝ)^4175 := by
      have hnat : (100048641563068100507 : ℕ)^1024*10000000000000000^4175 ≤ 10001192810070187^4175*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048641563068100507 100000000000000000000 10001192810070187 10000000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001192810070187/10000000000000000 : ℝ)) (X := (100048641563068100507/100000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035327486388662819/50000000000000000000 : ℝ) ≤ (10001732578475519/10000000000000000 : ℝ) ^ (4175/1024 : ℝ) := by
    have hpowers : (50035327486388662819/50000000000000000000 : ℝ)^1024 ≤ (10001732578475519/10000000000000000 : ℝ)^4175 := by
      have hnat : (50035327486388662819 : ℕ)^1024*10000000000000000^4175 ≤ 10001732578475519^4175*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035327486388662819 50000000000000000000 10001732578475519 10000000000000000 1024 4175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001732578475519/10000000000000000 : ℝ)) (X := (50035327486388662819/50000000000000000000 : ℝ)) (by norm_num) 4175 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1664259584929711/12500000000000000000 : ℝ) ≤ ((1009662750209367351/1010000000000000000 : ℝ)+2*(134942101333/75750000000000 : ℝ)*(2241/20000 : ℝ))^(4175/1024 : ℝ) := by
    rw [show (1009662750209367351/1010000000000000000 : ℝ)+2*(134942101333/75750000000000 : ℝ)*(2241/20000 : ℝ)=(2000130608332971/2000000000000000 : ℝ) by norm_num, show 1+2*(1664259584929711/12500000000000000000 : ℝ)=(6251664259584929711/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35327486388662819/100000000000000000000 : ℝ)+(1664259584929711/12500000000000000000 : ℝ) ≤ ((1009662750209367351/1010000000000000000 : ℝ)+(134942101333/75750000000000 : ℝ)*((2847/20000 : ℝ)+(2241/20000 : ℝ)))^(4175/1024 : ℝ) := by
    rw [show (1009662750209367351/1010000000000000000 : ℝ)+(134942101333/75750000000000 : ℝ)*((2847/20000 : ℝ)+(2241/20000 : ℝ))=(10001192810070187/10000000000000000 : ℝ) by norm_num, show 1+(35327486388662819/100000000000000000000 : ℝ)+(1664259584929711/12500000000000000000 : ℝ)=(100048641563068100507/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35327486388662819/100000000000000000000 : ℝ) ≤ ((1009662750209367351/1010000000000000000 : ℝ)+2*(134942101333/75750000000000 : ℝ)*(2847/20000 : ℝ))^(4175/1024 : ℝ) := by
    rw [show (1009662750209367351/1010000000000000000 : ℝ)+2*(134942101333/75750000000000 : ℝ)*(2847/20000 : ℝ)=(10001732578475519/10000000000000000 : ℝ) by norm_num, show 1+2*(35327486388662819/100000000000000000000 : ℝ)=(50035327486388662819/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1009662750209367351/1010000000000000000 : ℝ)*(X 1 0+X 2 0)+(134942101333/75750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (2241/20000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (1009662750209367351/1010000000000000000 : ℝ)) (alpha := (134942101333/75750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1009662750209367351/1010000000000000000 : ℝ)*(X 0 1+X 2 1)+(134942101333/75750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (2241/20000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (1009662750209367351/1010000000000000000 : ℝ)) (alpha := (134942101333/75750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1009662750209367351/1010000000000000000 : ℝ)*(X 0 2+X 1 2)+(134942101333/75750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4175/1024 : ℝ)) (lo := (2241/20000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (1009662750209367351/1010000000000000000 : ℝ)) (alpha := (134942101333/75750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1079552909/5000000000 : ℝ)*X 0 0+(5394501689/10000000000 : ℝ)*X 0 1+(5264336911/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336284813/2500000000 : ℝ)*X 1 0+(-445029731/2000000000 : ℝ)*X 1 1+(658042119/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345139337/10000000000 : ℝ)*X 2 0+(526433691/1000000000 : ℝ)*X 2 1+(-1112574299/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362336241/10000000000 : ℝ)*X 0 0+(846873351/2000000000 : ℝ)*X 0 1+(898827823/2000000000 : ℝ)*X 0 2+(4362336241/10000000000 : ℝ)*X 1 0+(846873351/2000000000 : ℝ)*X 1 1+(898827823/2000000000 : ℝ)*X 1 2+(4362336241/10000000000 : ℝ)*X 2 0+(846873351/2000000000 : ℝ)*X 2 1+(898827823/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2159110849/10000000000 : ℝ)*X 0 0+(5264673241/10000000000 : ℝ)*X 0 1+(5394164273/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312123183/10000000000 : ℝ)*X 1 0+(-419064191/2000000000 : ℝ)*X 1 1+(13485411/25000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312122897/10000000000 : ℝ)*X 2 0+(43153317/80000000 : ℝ)*X 2 1+(-523830259/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4362346747/10000000000 : ℝ)*X 0 0+(4493468429/10000000000 : ℝ)*X 0 1+(4235039899/10000000000 : ℝ)*X 0 2+(4362346747/10000000000 : ℝ)*X 1 0+(4493468429/10000000000 : ℝ)*X 1 1+(4235039899/10000000000 : ℝ)*X 1 2+(4362346747/10000000000 : ℝ)*X 2 0+(4493468429/10000000000 : ℝ)*X 2 1+(4235039899/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1158_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (60433540223066973649361359/6312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51887261/2500000000000 : ℝ)*(base19) + (498704611/25000000000000 : ℝ)*(base23) + (10842313/10000000000000 : ℝ)*(lower2) + (117209973/50000000000000 : ℝ)*(upper3) + (196547369/100000000000000 : ℝ)*(upper5) + (720766874695301/12500000000000 : ℝ)*(major0) + (720766874695301/12500000000000 : ℝ)*(major1) + (720766874695301/12500000000000 : ℝ)*(major2) + (7682627119189419/100000000000000 : ℝ)*(sp0) + (3841342560255743/50000000000000 : ℝ)*(sp1) + (3841342600591741/50000000000000 : ℝ)*(sp2) + (3849552061342443/100000000000000 : ℝ)*(sp3) + (30038406253/50000000000000 : ℝ)*(sp4) + (3041865943/10000000000000 : ℝ)*(sp7) + (240598905000117/6250000000000 : ℝ)*(f.failure) + (3841343598000963/50000000000000 : ℝ)*(f.sum) + (40597552679453/7575000000000000000000000000 : ℝ)*base65 + (427576021157627047/37875000000000000000000000000000 : ℝ)*base68 + (303482363203877047/37875000000000000000000000000000 : ℝ)*base70 + (213074779222502047/37875000000000000000000000000000 : ℝ)*base72 + (26149809553147/7575000000000000000000000000 : ℝ)*base74 + (1002771814575752047/37875000000000000000000000000000 : ℝ)*base76 + (3148158908252047/37875000000000000000000000000000 : ℝ)*base78 + (425914823013752047/37875000000000000000000000000000 : ℝ)*base80 + (25416013091303/7575000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (19687/2441406250000000000 : ℝ)*base90 + (19687/2441406250000000000 : ℝ)*base92 + (19687/2441406250000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4228025875598375876978403/2020000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (348046633/100000000000000 : ℝ)*(base19) + (205105983/50000000000000 : ℝ)*(base23) + (117462389/50000000000000 : ℝ)*(lower4) + (12717563/50000000000000 : ℝ)*(lower5) + (231841551474317/4000000000000 : ℝ)*(major0) + (231841551474317/4000000000000 : ℝ)*(major1) + (231841551474317/4000000000000 : ℝ)*(major2) + (1990185457/10000000000000 : ℝ)*(sp1) + (5129001053/20000000000000 : ℝ)*(sp2) + (2203835401/50000000000000 : ℝ)*(sp3) + (7722530679820403/100000000000000 : ℝ)*(sp4) + (9653138037399/125000000000 : ℝ)*(sp5) + (1930626156150793/25000000000000 : ℝ)*(sp6) + (386954241645523/10000000000000 : ℝ)*(sp7) + (241846676507877/6250000000000 : ℝ)*(f.failure) + (7722530679820403/100000000000000 : ℝ)*(f.sum) + (1397158814213/303000000000000000000000000 : ℝ)*base66 + (133496458245447199/12120000000000000000000000000000 : ℝ)*base68 + (272028624443367199/12120000000000000000000000000000 : ℝ)*base70 + (221164175796927199/12120000000000000000000000000000 : ℝ)*base72 + (82876070671/37875000000000000000000000 : ℝ)*base74 + (26943906529887199/12120000000000000000000000000000 : ℝ)*base76 + (102439605186807199/12120000000000000000000000000000 : ℝ)*base78 + (307892174832687199/12120000000000000000000000000000 : ℝ)*base80 + (168446228573/75750000000000000000000000 : ℝ)*base82 + (559123/39062500000000000000 : ℝ)*base89 + (559123/39062500000000000000 : ℝ)*base91 + (559123/39062500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1158_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5669/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1158_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1158_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3291/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4571/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5669/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1158_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1158_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1158_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4175/1024 : ℝ) ≤ p) (hpb : p ≤ (8351/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1170203/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3291/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4571/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5669/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1158_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
