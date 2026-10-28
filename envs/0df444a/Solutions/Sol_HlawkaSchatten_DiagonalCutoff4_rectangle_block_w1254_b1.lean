-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1254_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:24:44.603836+00:00
-- url     : https://prove2.me/submissions/553b1b4e-ff9c-4041-b987-076efab6d706

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
theorem support_rectangle_w1254_s3_0 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-84468057/400000000 : ℝ)*x 0 + (1354653969/2500000000 : ℝ)*x 1 + (5241533171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84468057/400000000 : ℝ)^8447 ≤ (12837520304091/100000000000000 : ℝ)^6399 := by
    have hnat : (84468057 : ℕ)^8447*100000000000000^6399 ≤ 12837520304091^6399*400000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84468057 400000000 12837520304091 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354653969/2500000000 : ℝ)^8447 ≤ (44536833309727/100000000000000 : ℝ)^6399 := by
    have hnat : (1354653969 : ℕ)^8447*100000000000000^6399 ≤ 44536833309727^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354653969 2500000000 44536833309727 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241533171/10000000000 : ℝ)^8447 ≤ (21312823184987/50000000000000 : ℝ)^6399 := by
    have hnat : (5241533171 : ℕ)^8447*50000000000000^6399 ≤ 21312823184987^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241533171 10000000000 21312823184987 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-84468057/400000000 : ℝ), (1354653969/2500000000 : ℝ), (5241533171/10000000000 : ℝ)] ![(12837520304091/100000000000000 : ℝ), (44536833309727/100000000000000 : ℝ), (21312823184987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-84468057/400000000 : ℝ)|^8447 ≤ (12837520304091/100000000000000 : ℝ)^6399
        have hw : |(-84468057/400000000 : ℝ)|=(84468057/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354653969/2500000000 : ℝ)|^8447 ≤ (44536833309727/100000000000000 : ℝ)^6399
        have hw : |(1354653969/2500000000 : ℝ)|=(1354653969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241533171/10000000000 : ℝ)|^8447 ≤ (21312823184987/50000000000000 : ℝ)^6399
        have hw : |(5241533171/10000000000 : ℝ)|=(5241533171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s3_1 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2675613339/5000000000 : ℝ)*x 0 + (-275252321/1250000000 : ℝ)*x 1 + (5241533269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675613339/5000000000 : ℝ)^8447 ≤ (21903566940053/50000000000000 : ℝ)^6399 := by
    have hnat : (2675613339 : ℕ)^8447*50000000000000^6399 ≤ 21903566940053^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675613339 5000000000 21903566940053 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (275252321/1250000000 : ℝ)^8447 ≤ (2713443736477/20000000000000 : ℝ)^6399 := by
    have hnat : (275252321 : ℕ)^8447*20000000000000^6399 ≤ 2713443736477^6399*1250000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275252321 1250000000 2713443736477 20000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241533269/10000000000 : ℝ)^8447 ≤ (42625647422007/100000000000000 : ℝ)^6399 := by
    have hnat : (5241533269 : ℕ)^8447*100000000000000^6399 ≤ 42625647422007^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241533269 10000000000 42625647422007 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675613339/5000000000 : ℝ), (-275252321/1250000000 : ℝ), (5241533269/10000000000 : ℝ)] ![(21903566940053/50000000000000 : ℝ), (2713443736477/20000000000000 : ℝ), (42625647422007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675613339/5000000000 : ℝ)|^8447 ≤ (21903566940053/50000000000000 : ℝ)^6399
        have hw : |(2675613339/5000000000 : ℝ)|=(2675613339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-275252321/1250000000 : ℝ)|^8447 ≤ (2713443736477/20000000000000 : ℝ)^6399
        have hw : |(-275252321/1250000000 : ℝ)|=(275252321/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241533269/10000000000 : ℝ)|^8447 ≤ (42625647422007/100000000000000 : ℝ)^6399
        have hw : |(5241533269/10000000000 : ℝ)|=(5241533269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s3_2 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2675613319/5000000000 : ℝ)*x 0 + (5241533737/10000000000 : ℝ)*x 1 + (-550504501/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675613319/5000000000 : ℝ)^8447 ≤ (43807133447849/100000000000000 : ℝ)^6399 := by
    have hnat : (2675613319 : ℕ)^8447*100000000000000^6399 ≤ 43807133447849^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675613319 5000000000 43807133447849 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241533737/10000000000 : ℝ)^8447 ≤ (21312826222999/50000000000000 : ℝ)^6399 := by
    have hnat : (5241533737 : ℕ)^8447*50000000000000^6399 ≤ 21312826222999^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241533737 10000000000 21312826222999 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550504501/2500000000 : ℝ)^8447 ≤ (6783607047637/50000000000000 : ℝ)^6399 := by
    have hnat : (550504501 : ℕ)^8447*50000000000000^6399 ≤ 6783607047637^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550504501 2500000000 6783607047637 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675613319/5000000000 : ℝ), (5241533737/10000000000 : ℝ), (-550504501/2500000000 : ℝ)] ![(43807133447849/100000000000000 : ℝ), (21312826222999/50000000000000 : ℝ), (6783607047637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675613319/5000000000 : ℝ)|^8447 ≤ (43807133447849/100000000000000 : ℝ)^6399
        have hw : |(2675613319/5000000000 : ℝ)|=(2675613319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241533737/10000000000 : ℝ)|^8447 ≤ (21312826222999/50000000000000 : ℝ)^6399
        have hw : |(5241533737/10000000000 : ℝ)|=(5241533737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-550504501/2500000000 : ℝ)|^8447 ≤ (6783607047637/50000000000000 : ℝ)^6399
        have hw : |(-550504501/2500000000 : ℝ)|=(550504501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s3_3 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2173744329/5000000000 : ℝ)*x 0 + (2085535661/5000000000 : ℝ)*x 1 + (2265563471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173744329/5000000000 : ℝ)^8447 ≤ (33300953841387/100000000000000 : ℝ)^6399 := by
    have hnat : (2173744329 : ℕ)^8447*100000000000000^6399 ≤ 33300953841387^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173744329 5000000000 33300953841387 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085535661/5000000000 : ℝ)^8447 ≤ (7882207639269/25000000000000 : ℝ)^6399 := by
    have hnat : (2085535661 : ℕ)^8447*25000000000000^6399 ≤ 7882207639269^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085535661 5000000000 7882207639269 25000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2265563471/5000000000 : ℝ)^8447 ≤ (8792553894571/25000000000000 : ℝ)^6399 := by
    have hnat : (2265563471 : ℕ)^8447*25000000000000^6399 ≤ 8792553894571^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265563471 5000000000 8792553894571 25000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173744329/5000000000 : ℝ), (2085535661/5000000000 : ℝ), (2265563471/5000000000 : ℝ)] ![(33300953841387/100000000000000 : ℝ), (7882207639269/25000000000000 : ℝ), (8792553894571/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173744329/5000000000 : ℝ)|^8447 ≤ (33300953841387/100000000000000 : ℝ)^6399
        have hw : |(2173744329/5000000000 : ℝ)|=(2173744329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085535661/5000000000 : ℝ)|^8447 ≤ (7882207639269/25000000000000 : ℝ)^6399
        have hw : |(2085535661/5000000000 : ℝ)|=(2085535661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2265563471/5000000000 : ℝ)|^8447 ≤ (8792553894571/25000000000000 : ℝ)^6399
        have hw : |(2265563471/5000000000 : ℝ)|=(2265563471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s3_4 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2111715597/10000000000 : ℝ)*x 0 + (5242171977/10000000000 : ℝ)*x 1 + (5417973321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2111715597/10000000000 : ℝ)^8447 ≤ (2567526806587/20000000000000 : ℝ)^6399 := by
    have hnat : (2111715597 : ℕ)^8447*20000000000000^6399 ≤ 2567526806587^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111715597 10000000000 2567526806587 20000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242171977/10000000000 : ℝ)^8447 ≤ (10658126025377/25000000000000 : ℝ)^6399 := by
    have hnat : (5242171977 : ℕ)^8447*25000000000000^6399 ≤ 10658126025377^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242171977 10000000000 10658126025377 25000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417973321/10000000000 : ℝ)^8447 ≤ (22264930927439/50000000000000 : ℝ)^6399 := by
    have hnat : (5417973321 : ℕ)^8447*50000000000000^6399 ≤ 22264930927439^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417973321 10000000000 22264930927439 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2111715597/10000000000 : ℝ), (5242171977/10000000000 : ℝ), (5417973321/10000000000 : ℝ)] ![(2567526806587/20000000000000 : ℝ), (10658126025377/25000000000000 : ℝ), (22264930927439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2111715597/10000000000 : ℝ)|^8447 ≤ (2567526806587/20000000000000 : ℝ)^6399
        have hw : |(-2111715597/10000000000 : ℝ)|=(2111715597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242171977/10000000000 : ℝ)|^8447 ≤ (10658126025377/25000000000000 : ℝ)^6399
        have hw : |(5242171977/10000000000 : ℝ)|=(5242171977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417973321/10000000000 : ℝ)|^8447 ≤ (22264930927439/50000000000000 : ℝ)^6399
        have hw : |(5417973321/10000000000 : ℝ)|=(5417973321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s3_5 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (530601303/1000000000 : ℝ)*x 0 + (-1012788959/5000000000 : ℝ)*x 1 + (135449329/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530601303/1000000000 : ℝ)^8447 ≤ (43319198068043/100000000000000 : ℝ)^6399 := by
    have hnat : (530601303 : ℕ)^8447*100000000000000^6399 ≤ 43319198068043^6399*1000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530601303 1000000000 43319198068043 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1012788959/5000000000 : ℝ)^8447 ≤ (1215094181193/10000000000000 : ℝ)^6399 := by
    have hnat : (1012788959 : ℕ)^8447*10000000000000^6399 ≤ 1215094181193^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012788959 5000000000 1215094181193 10000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135449329/250000000 : ℝ)^8447 ≤ (1391558128379/3125000000000 : ℝ)^6399 := by
    have hnat : (135449329 : ℕ)^8447*3125000000000^6399 ≤ 1391558128379^6399*250000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135449329 250000000 1391558128379 3125000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530601303/1000000000 : ℝ), (-1012788959/5000000000 : ℝ), (135449329/250000000 : ℝ)] ![(43319198068043/100000000000000 : ℝ), (1215094181193/10000000000000 : ℝ), (1391558128379/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530601303/1000000000 : ℝ)|^8447 ≤ (43319198068043/100000000000000 : ℝ)^6399
        have hw : |(530601303/1000000000 : ℝ)|=(530601303/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1012788959/5000000000 : ℝ)|^8447 ≤ (1215094181193/10000000000000 : ℝ)^6399
        have hw : |(-1012788959/5000000000 : ℝ)|=(1012788959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135449329/250000000 : ℝ)|^8447 ≤ (1391558128379/3125000000000 : ℝ)^6399
        have hw : |(135449329/250000000 : ℝ)|=(135449329/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s3_6 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5306012379/10000000000 : ℝ)*x 0 + (43343789/80000000 : ℝ)*x 1 + (-1012789083/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5306012379/10000000000 : ℝ)^8447 ≤ (21659595526071/50000000000000 : ℝ)^6399 := by
    have hnat : (5306012379 : ℕ)^8447*50000000000000^6399 ≤ 21659595526071^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5306012379 10000000000 21659595526071 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43343789/80000000 : ℝ)^8447 ≤ (44529865153089/100000000000000 : ℝ)^6399 := by
    have hnat : (43343789 : ℕ)^8447*100000000000000^6399 ≤ 44529865153089^6399*80000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43343789 80000000 44529865153089 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1012789083/5000000000 : ℝ)^8447 ≤ (3037735943939/25000000000000 : ℝ)^6399 := by
    have hnat : (1012789083 : ℕ)^8447*25000000000000^6399 ≤ 3037735943939^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012789083 5000000000 3037735943939 25000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5306012379/10000000000 : ℝ), (43343789/80000000 : ℝ), (-1012789083/5000000000 : ℝ)] ![(21659595526071/50000000000000 : ℝ), (44529865153089/100000000000000 : ℝ), (3037735943939/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5306012379/10000000000 : ℝ)|^8447 ≤ (21659595526071/50000000000000 : ℝ)^6399
        have hw : |(5306012379/10000000000 : ℝ)|=(5306012379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43343789/80000000 : ℝ)|^8447 ≤ (44529865153089/100000000000000 : ℝ)^6399
        have hw : |(43343789/80000000 : ℝ)|=(43343789/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1012789083/5000000000 : ℝ)|^8447 ≤ (3037735943939/25000000000000 : ℝ)^6399
        have hw : |(-1012789083/5000000000 : ℝ)|=(1012789083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s3_7 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4347517021/10000000000 : ℝ)*x 0 + (2264913641/5000000000 : ℝ)*x 1 + (2086188507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347517021/10000000000 : ℝ)^8447 ≤ (33301240629547/100000000000000 : ℝ)^6399 := by
    have hnat : (4347517021 : ℕ)^8447*100000000000000^6399 ≤ 33301240629547^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347517021 10000000000 33301240629547 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264913641/5000000000 : ℝ)^8447 ≤ (17578449862491/50000000000000 : ℝ)^6399 := by
    have hnat : (2264913641 : ℕ)^8447*50000000000000^6399 ≤ 17578449862491^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264913641 5000000000 17578449862491 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086188507/5000000000 : ℝ)^8447 ≤ (7885464904591/25000000000000 : ℝ)^6399 := by
    have hnat : (2086188507 : ℕ)^8447*25000000000000^6399 ≤ 7885464904591^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086188507 5000000000 7885464904591 25000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347517021/10000000000 : ℝ), (2264913641/5000000000 : ℝ), (2086188507/5000000000 : ℝ)] ![(33301240629547/100000000000000 : ℝ), (17578449862491/50000000000000 : ℝ), (7885464904591/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347517021/10000000000 : ℝ)|^8447 ≤ (33301240629547/100000000000000 : ℝ)^6399
        have hw : |(4347517021/10000000000 : ℝ)|=(4347517021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2264913641/5000000000 : ℝ)|^8447 ≤ (17578449862491/50000000000000 : ℝ)^6399
        have hw : |(2264913641/5000000000 : ℝ)|=(2264913641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086188507/5000000000 : ℝ)|^8447 ≤ (7885464904591/25000000000000 : ℝ)^6399
        have hw : |(2086188507/5000000000 : ℝ)|=(2086188507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1254_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (506/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2387/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5471/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1469/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (506/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2387/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (506/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2387/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (506/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2387/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (506/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2387/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (506/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2387/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (506/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2387/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2387/25000 : ℝ) ^ (4223/1024 : ℝ) ≤ (776327346970137/12500000000000000000 : ℝ) := by
    have hpowers : (2387/25000 : ℝ)^4223 ≤ (776327346970137/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2387 : ℕ)^4223*12500000000000000000^1024 ≤ 776327346970137^1024*25000^4223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2387 25000 776327346970137 12500000000000000000 4223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2387/25000 : ℝ)) (X := (776327346970137/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (506/3125 : ℝ) ^ (4223/1024 : ℝ) ≤ (54844958224859789/100000000000000000000 : ℝ) := by
    have hpowers : (506/3125 : ℝ)^4223 ≤ (54844958224859789/100000000000000000000 : ℝ)^1024 := by
      have hnat : (506 : ℕ)^4223*100000000000000000000^1024 ≤ 54844958224859789^1024*3125^4223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        506 3125 54844958224859789 100000000000000000000 4223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (506/3125 : ℝ)) (X := (54844958224859789/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250776327346970137/6250000000000000000 : ℝ) ≤ (2500075294511571/2500000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (6250776327346970137/6250000000000000000 : ℝ)^1024 ≤ (2500075294511571/2500000000000000 : ℝ)^4223 := by
      have hnat : (6250776327346970137 : ℕ)^1024*2500000000000000^4223 ≤ 2500075294511571^4223*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250776327346970137 6250000000000000000 2500075294511571 2500000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500075294511571/2500000000000000 : ℝ)) (X := (6250776327346970137/6250000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20012211115400124177/20000000000000000000 : ℝ) ≤ (200029602868971/200000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (20012211115400124177/20000000000000000000 : ℝ)^1024 ≤ (200029602868971/200000000000000 : ℝ)^4223 := by
      have hnat : (20012211115400124177 : ℕ)^1024*200000000000000^4223 ≤ 200029602868971^4223*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20012211115400124177 20000000000000000000 200029602868971 200000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200029602868971/200000000000000 : ℝ)) (X := (20012211115400124177/20000000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50054844958224859789/50000000000000000000 : ℝ) ≤ (78145774287897/78125000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (50054844958224859789/50000000000000000000 : ℝ)^1024 ≤ (78145774287897/78125000000000 : ℝ)^4223 := by
      have hnat : (50054844958224859789 : ℕ)^1024*78125000000000^4223 ≤ 78145774287897^4223*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50054844958224859789 50000000000000000000 78145774287897 78125000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78145774287897/78125000000000 : ℝ)) (X := (50054844958224859789/50000000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(776327346970137/12500000000000000000 : ℝ) ≤ ((4717293146563767/4718750000000000 : ℝ)+2*(589482701133/332200000000000 : ℝ)*(2387/25000 : ℝ))^(4223/1024 : ℝ) := by
    rw [show (4717293146563767/4718750000000000 : ℝ)+2*(589482701133/332200000000000 : ℝ)*(2387/25000 : ℝ)=(2500075294511571/2500000000000000 : ℝ) by norm_num, show 1+2*(776327346970137/12500000000000000000 : ℝ)=(6250776327346970137/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(54844958224859789/100000000000000000000 : ℝ)+(776327346970137/12500000000000000000 : ℝ) ≤ ((4717293146563767/4718750000000000 : ℝ)+(589482701133/332200000000000 : ℝ)*((506/3125 : ℝ)+(2387/25000 : ℝ)))^(4223/1024 : ℝ) := by
    rw [show (4717293146563767/4718750000000000 : ℝ)+(589482701133/332200000000000 : ℝ)*((506/3125 : ℝ)+(2387/25000 : ℝ))=(200029602868971/200000000000000 : ℝ) by norm_num, show 1+(54844958224859789/100000000000000000000 : ℝ)+(776327346970137/12500000000000000000 : ℝ)=(20012211115400124177/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(54844958224859789/100000000000000000000 : ℝ) ≤ ((4717293146563767/4718750000000000 : ℝ)+2*(589482701133/332200000000000 : ℝ)*(506/3125 : ℝ))^(4223/1024 : ℝ) := by
    rw [show (4717293146563767/4718750000000000 : ℝ)+2*(589482701133/332200000000000 : ℝ)*(506/3125 : ℝ)=(78145774287897/78125000000000 : ℝ) by norm_num, show 1+2*(54844958224859789/100000000000000000000 : ℝ)=(50054844958224859789/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4717293146563767/4718750000000000 : ℝ)*(X 1 0+X 2 0)+(589482701133/332200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (2387/25000 : ℝ)) (hi := (506/3125 : ℝ)) (c := (4717293146563767/4718750000000000 : ℝ)) (alpha := (589482701133/332200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4717293146563767/4718750000000000 : ℝ)*(X 0 1+X 2 1)+(589482701133/332200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (2387/25000 : ℝ)) (hi := (506/3125 : ℝ)) (c := (4717293146563767/4718750000000000 : ℝ)) (alpha := (589482701133/332200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4717293146563767/4718750000000000 : ℝ)*(X 0 2+X 1 2)+(589482701133/332200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (2387/25000 : ℝ)) (hi := (506/3125 : ℝ)) (c := (4717293146563767/4718750000000000 : ℝ)) (alpha := (589482701133/332200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-84468057/400000000 : ℝ)*X 0 0+(1354653969/2500000000 : ℝ)*X 0 1+(5241533171/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675613339/5000000000 : ℝ)*X 1 0+(-275252321/1250000000 : ℝ)*X 1 1+(5241533269/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675613319/5000000000 : ℝ)*X 2 0+(5241533737/10000000000 : ℝ)*X 2 1+(-550504501/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2173744329/5000000000 : ℝ)*X 0 0+(2085535661/5000000000 : ℝ)*X 0 1+(2265563471/5000000000 : ℝ)*X 0 2+(2173744329/5000000000 : ℝ)*X 1 0+(2085535661/5000000000 : ℝ)*X 1 1+(2265563471/5000000000 : ℝ)*X 1 2+(2173744329/5000000000 : ℝ)*X 2 0+(2085535661/5000000000 : ℝ)*X 2 1+(2265563471/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2111715597/10000000000 : ℝ)*X 0 0+(5242171977/10000000000 : ℝ)*X 0 1+(5417973321/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530601303/1000000000 : ℝ)*X 1 0+(-1012788959/5000000000 : ℝ)*X 1 1+(135449329/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5306012379/10000000000 : ℝ)*X 2 0+(43343789/80000000 : ℝ)*X 2 1+(-1012789083/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4347517021/10000000000 : ℝ)*X 0 0+(2264913641/5000000000 : ℝ)*X 0 1+(2086188507/5000000000 : ℝ)*X 0 2+(4347517021/10000000000 : ℝ)*X 1 0+(2264913641/5000000000 : ℝ)*X 1 1+(2086188507/5000000000 : ℝ)*X 1 2+(4347517021/10000000000 : ℝ)*X 2 0+(2264913641/5000000000 : ℝ)*X 2 1+(2086188507/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9404974296892777656245697/2595312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (37380107/50000000000000 : ℝ)*(base19) + (69466869/50000000000000 : ℝ)*(lower2) + (5699377/5000000000000 : ℝ)*(lower3) + (65829357/100000000000000 : ℝ)*(lower4) + (526529834256997/12500000000000 : ℝ)*(major0) + (526529834256997/12500000000000 : ℝ)*(major1) + (526529834256997/12500000000000 : ℝ)*(major2) + (2823548411980637/50000000000000 : ℝ)*(sp0) + (5647108362396991/100000000000000 : ℝ)*(sp1) + (5647120753566587/100000000000000 : ℝ)*(sp2) + (1388676484639367/50000000000000 : ℝ)*(sp3) + (373900083/1562500000000 : ℝ)*(sp4) + (6158204691/50000000000000 : ℝ)*(sp5) + (876118063/25000000000000 : ℝ)*(sp7) + (1388678236875493/50000000000000 : ℝ)*(f.failure) + (5647120753566587/100000000000000 : ℝ)*(f.sum) + (1496620911173/4152500000000000000000000000 : ℝ)*base66 + (22448559802524369/2595312500000000000000000000000 : ℝ)*base68 + (1184094946555157/324414062500000000000000000000 : ℝ)*base69 + (7538936621013747/1297656250000000000000000000000 : ℝ)*base72 + (1359052469309/2076250000000000000000000000 : ℝ)*base74 + (24623962636595613/5190625000000000000000000000000 : ℝ)*base76 + (10185581153017811/648828125000000000000000000000 : ℝ)*base78 + (71338774660145613/5190625000000000000000000000000 : ℝ)*base80 + (1844715972741/2076250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (7155467/1000000000000000000000 : ℝ)*base89 + (7155467/1000000000000000000000 : ℝ)*base91 + (7155467/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2126665310413501310084019/519062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (31168951/1250000000000 : ℝ)*(base19) + (1784398233/100000000000000 : ℝ)*(base23) + (3452077/20000000000000 : ℝ)*(upper3) + (16565113/20000000000000 : ℝ)*(lower4) + (8456459/2000000000000 : ℝ)*(upper5) + (212145698509601/5000000000000 : ℝ)*(major0) + (212145698509601/5000000000000 : ℝ)*(major1) + (212145698509601/5000000000000 : ℝ)*(major2) + (58586219773/100000000000000 : ℝ)*(sp1) + (7790016687/20000000000000 : ℝ)*(sp2) + (5688245450452689/100000000000000 : ℝ)*(sp4) + (1422046092679209/25000000000000 : ℝ)*(sp5) + (284410235798551/5000000000000 : ℝ)*(sp6) + (2797582353360423/100000000000000 : ℝ)*(sp7) + (2797582353360423/100000000000000 : ℝ)*(f.failure) + (5688245450452689/100000000000000 : ℝ)*(f.sum) + (832333416671/415250000000000000000000000 : ℝ)*base66 + (1357972196271101/519062500000000000000000000000 : ℝ)*base68 + (5742322181574851/519062500000000000000000000000 : ℝ)*base70 + (396818692900863/259531250000000000000000000000 : ℝ)*base72 + (462311709187/415250000000000000000000000 : ℝ)*base74 + (8938989105327351/519062500000000000000000000000 : ℝ)*base76 + (611532639177887/259531250000000000000000000000 : ℝ)*base77 + (1230463655489881/129765625000000000000000000000 : ℝ)*base79 + (1804530964729/415250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (16580137/2000000000000000000000 : ℝ)*base89 + (16580137/2000000000000000000000 : ℝ)*base91 + (16580137/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1254_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (506/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2387/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5471/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1469/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1254_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1254_s4_0 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056959999/5000000000 : ℝ)*x 0 + (5397012513/10000000000 : ℝ)*x 1 + (657710301/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056959999/5000000000 : ℝ)^8447 ≤ (6427663548943/50000000000000 : ℝ)^6399 := by
    have hnat : (1056959999 : ℕ)^8447*50000000000000^6399 ≤ 6427663548943^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056959999 5000000000 6427663548943 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397012513/10000000000 : ℝ)^8447 ≤ (22151295512077/50000000000000 : ℝ)^6399 := by
    have hnat : (5397012513 : ℕ)^8447*50000000000000^6399 ≤ 22151295512077^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397012513 10000000000 22151295512077 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657710301/1250000000 : ℝ)^8447 ≤ (42842081859363/100000000000000 : ℝ)^6399 := by
    have hnat : (657710301 : ℕ)^8447*100000000000000^6399 ≤ 42842081859363^6399*1250000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657710301 1250000000 42842081859363 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056959999/5000000000 : ℝ), (5397012513/10000000000 : ℝ), (657710301/1250000000 : ℝ)] ![(6427663548943/50000000000000 : ℝ), (22151295512077/50000000000000 : ℝ), (42842081859363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056959999/5000000000 : ℝ)|^8447 ≤ (6427663548943/50000000000000 : ℝ)^6399
        have hw : |(-1056959999/5000000000 : ℝ)|=(1056959999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397012513/10000000000 : ℝ)|^8447 ≤ (22151295512077/50000000000000 : ℝ)^6399
        have hw : |(5397012513/10000000000 : ℝ)|=(5397012513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657710301/1250000000 : ℝ)|^8447 ≤ (42842081859363/100000000000000 : ℝ)^6399
        have hw : |(657710301/1250000000 : ℝ)|=(657710301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s4_1 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345774747/10000000000 : ℝ)*x 0 + (-2182622571/10000000000 : ℝ)*x 1 + (328855151/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345774747/10000000000 : ℝ)^8447 ≤ (43748227627057/100000000000000 : ℝ)^6399 := by
    have hnat : (5345774747 : ℕ)^8447*100000000000000^6399 ≤ 43748227627057^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345774747 10000000000 43748227627057 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2182622571/10000000000 : ℝ)^8447 ≤ (107277523243/800000000000 : ℝ)^6399 := by
    have hnat : (2182622571 : ℕ)^8447*800000000000^6399 ≤ 107277523243^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182622571 10000000000 107277523243 800000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328855151/625000000 : ℝ)^8447 ≤ (42842081945349/100000000000000 : ℝ)^6399 := by
    have hnat : (328855151 : ℕ)^8447*100000000000000^6399 ≤ 42842081945349^6399*625000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328855151 625000000 42842081945349 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345774747/10000000000 : ℝ), (-2182622571/10000000000 : ℝ), (328855151/625000000 : ℝ)] ![(43748227627057/100000000000000 : ℝ), (107277523243/800000000000 : ℝ), (42842081945349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345774747/10000000000 : ℝ)|^8447 ≤ (43748227627057/100000000000000 : ℝ)^6399
        have hw : |(5345774747/10000000000 : ℝ)|=(5345774747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2182622571/10000000000 : ℝ)|^8447 ≤ (107277523243/800000000000 : ℝ)^6399
        have hw : |(-2182622571/10000000000 : ℝ)|=(2182622571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328855151/625000000 : ℝ)|^8447 ≤ (42842081945349/100000000000000 : ℝ)^6399
        have hw : |(328855151/625000000 : ℝ)|=(328855151/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s4_2 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668221857/1250000000 : ℝ)*x 0 + (526168231/1000000000 : ℝ)*x 1 + (-2182622567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668221857/1250000000 : ℝ)^8447 ≤ (43748228804573/100000000000000 : ℝ)^6399 := by
    have hnat : (668221857 : ℕ)^8447*100000000000000^6399 ≤ 43748228804573^6399*1250000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668221857 1250000000 43748228804573 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526168231/1000000000 : ℝ)^8447 ≤ (21421040403019/50000000000000 : ℝ)^6399 := by
    have hnat : (526168231 : ℕ)^8447*50000000000000^6399 ≤ 21421040403019^6399*1000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526168231 1000000000 21421040403019 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2182622567/10000000000 : ℝ)^8447 ≤ (2681938074587/20000000000000 : ℝ)^6399 := by
    have hnat : (2182622567 : ℕ)^8447*20000000000000^6399 ≤ 2681938074587^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182622567 10000000000 2681938074587 20000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668221857/1250000000 : ℝ), (526168231/1000000000 : ℝ), (-2182622567/10000000000 : ℝ)] ![(43748228804573/100000000000000 : ℝ), (21421040403019/50000000000000 : ℝ), (2681938074587/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668221857/1250000000 : ℝ)|^8447 ≤ (43748228804573/100000000000000 : ℝ)^6399
        have hw : |(668221857/1250000000 : ℝ)|=(668221857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526168231/1000000000 : ℝ)|^8447 ≤ (21421040403019/50000000000000 : ℝ)^6399
        have hw : |(526168231/1000000000 : ℝ)|=(526168231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2182622567/10000000000 : ℝ)|^8447 ≤ (2681938074587/20000000000000 : ℝ)^6399
        have hw : |(-2182622567/10000000000 : ℝ)|=(2182622567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s4_3 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2174409967/5000000000 : ℝ)*x 0 + (2106674033/5000000000 : ℝ)*x 1 + (4488511063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174409967/5000000000 : ℝ)^8447 ≤ (33314415481683/100000000000000 : ℝ)^6399 := by
    have hnat : (2174409967 : ℕ)^8447*100000000000000^6399 ≤ 33314415481683^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174409967 5000000000 33314415481683 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2106674033/5000000000 : ℝ)^8447 ≤ (15975678743551/50000000000000 : ℝ)^6399 := by
    have hnat : (2106674033 : ℕ)^8447*50000000000000^6399 ≤ 15975678743551^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106674033 5000000000 15975678743551 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4488511063/10000000000 : ℝ)^8447 ≤ (34734227007897/100000000000000 : ℝ)^6399 := by
    have hnat : (4488511063 : ℕ)^8447*100000000000000^6399 ≤ 34734227007897^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488511063 10000000000 34734227007897 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174409967/5000000000 : ℝ), (2106674033/5000000000 : ℝ), (4488511063/10000000000 : ℝ)] ![(33314415481683/100000000000000 : ℝ), (15975678743551/50000000000000 : ℝ), (34734227007897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174409967/5000000000 : ℝ)|^8447 ≤ (33314415481683/100000000000000 : ℝ)^6399
        have hw : |(2174409967/5000000000 : ℝ)|=(2174409967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2106674033/5000000000 : ℝ)|^8447 ≤ (15975678743551/50000000000000 : ℝ)^6399
        have hw : |(2106674033/5000000000 : ℝ)|=(2106674033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4488511063/10000000000 : ℝ)|^8447 ≤ (34734227007897/100000000000000 : ℝ)^6399
        have hw : |(4488511063/10000000000 : ℝ)|=(4488511063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s4_4 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-528481467/2500000000 : ℝ)*x 0 + (5262056171/10000000000 : ℝ)*x 1 + (269831871/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528481467/2500000000 : ℝ)^8447 ≤ (12855374219837/100000000000000 : ℝ)^6399 := by
    have hnat : (528481467 : ℕ)^8447*100000000000000^6399 ≤ 12855374219837^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528481467 2500000000 12855374219837 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262056171/10000000000 : ℝ)^8447 ≤ (21423049594939/50000000000000 : ℝ)^6399 := by
    have hnat : (5262056171 : ℕ)^8447*50000000000000^6399 ≤ 21423049594939^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262056171 10000000000 21423049594939 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269831871/500000000 : ℝ)^8447 ≤ (11074631647213/25000000000000 : ℝ)^6399 := by
    have hnat : (269831871 : ℕ)^8447*25000000000000^6399 ≤ 11074631647213^6399*500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269831871 500000000 11074631647213 25000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-528481467/2500000000 : ℝ), (5262056171/10000000000 : ℝ), (269831871/500000000 : ℝ)] ![(12855374219837/100000000000000 : ℝ), (21423049594939/50000000000000 : ℝ), (11074631647213/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-528481467/2500000000 : ℝ)|^8447 ≤ (12855374219837/100000000000000 : ℝ)^6399
        have hw : |(-528481467/2500000000 : ℝ)|=(528481467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262056171/10000000000 : ℝ)|^8447 ≤ (21423049594939/50000000000000 : ℝ)^6399
        have hw : |(5262056171/10000000000 : ℝ)|=(5262056171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269831871/500000000 : ℝ)|^8447 ≤ (11074631647213/25000000000000 : ℝ)^6399
        have hw : |(269831871/500000000 : ℝ)|=(269831871/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s4_5 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311218593/10000000000 : ℝ)*x 0 + (-1023833723/5000000000 : ℝ)*x 1 + (5396637413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311218593/10000000000 : ℝ)^8447 ≤ (43375307819997/100000000000000 : ℝ)^6399 := by
    have hnat : (5311218593 : ℕ)^8447*100000000000000^6399 ≤ 43375307819997^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311218593 10000000000 43375307819997 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1023833723/5000000000 : ℝ)^8447 ≤ (12326165647019/100000000000000 : ℝ)^6399 := by
    have hnat : (1023833723 : ℕ)^8447*100000000000000^6399 ≤ 12326165647019^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023833723 5000000000 12326165647019 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396637413/10000000000 : ℝ)^8447 ≤ (22149263256501/50000000000000 : ℝ)^6399 := by
    have hnat : (5396637413 : ℕ)^8447*50000000000000^6399 ≤ 22149263256501^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396637413 10000000000 22149263256501 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311218593/10000000000 : ℝ), (-1023833723/5000000000 : ℝ), (5396637413/10000000000 : ℝ)] ![(43375307819997/100000000000000 : ℝ), (12326165647019/100000000000000 : ℝ), (22149263256501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311218593/10000000000 : ℝ)|^8447 ≤ (43375307819997/100000000000000 : ℝ)^6399
        have hw : |(5311218593/10000000000 : ℝ)|=(5311218593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1023833723/5000000000 : ℝ)|^8447 ≤ (12326165647019/100000000000000 : ℝ)^6399
        have hw : |(-1023833723/5000000000 : ℝ)|=(1023833723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396637413/10000000000 : ℝ)|^8447 ≤ (22149263256501/50000000000000 : ℝ)^6399
        have hw : |(5396637413/10000000000 : ℝ)|=(5396637413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s4_6 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655609167/5000000000 : ℝ)*x 0 + (674579709/1250000000 : ℝ)*x 1 + (-511916861/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655609167/5000000000 : ℝ)^8447 ≤ (5421913128481/12500000000000 : ℝ)^6399 := by
    have hnat : (2655609167 : ℕ)^8447*12500000000000^6399 ≤ 5421913128481^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655609167 5000000000 5421913128481 12500000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674579709/1250000000 : ℝ)^8447 ≤ (8859705863889/20000000000000 : ℝ)^6399 := by
    have hnat : (674579709 : ℕ)^8447*20000000000000^6399 ≤ 8859705863889^6399*1250000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674579709 1250000000 8859705863889 20000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (511916861/2500000000 : ℝ)^8447 ≤ (12326165631127/100000000000000 : ℝ)^6399 := by
    have hnat : (511916861 : ℕ)^8447*100000000000000^6399 ≤ 12326165631127^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511916861 2500000000 12326165631127 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655609167/5000000000 : ℝ), (674579709/1250000000 : ℝ), (-511916861/2500000000 : ℝ)] ![(5421913128481/12500000000000 : ℝ), (8859705863889/20000000000000 : ℝ), (12326165631127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655609167/5000000000 : ℝ)|^8447 ≤ (5421913128481/12500000000000 : ℝ)^6399
        have hw : |(2655609167/5000000000 : ℝ)|=(2655609167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674579709/1250000000 : ℝ)|^8447 ≤ (8859705863889/20000000000000 : ℝ)^6399
        have hw : |(674579709/1250000000 : ℝ)|=(674579709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-511916861/2500000000 : ℝ)|^8447 ≤ (12326165631127/100000000000000 : ℝ)^6399
        have hw : |(-511916861/2500000000 : ℝ)|=(511916861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s4_7 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4348832093/10000000000 : ℝ)*x 0 + (4487751561/10000000000 : ℝ)*x 1 + (4214110777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348832093/10000000000 : ℝ)^8447 ≤ (1041079326173/3125000000000 : ℝ)^6399 := by
    have hnat : (4348832093 : ℕ)^8447*3125000000000^6399 ≤ 1041079326173^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348832093 10000000000 1041079326173 3125000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4487751561/10000000000 : ℝ)^8447 ≤ (34726468773729/100000000000000 : ℝ)^6399 := by
    have hnat : (4487751561 : ℕ)^8447*100000000000000^6399 ≤ 34726468773729^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487751561 10000000000 34726468773729 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4214110777/10000000000 : ℝ)^8447 ≤ (31958992766793/100000000000000 : ℝ)^6399 := by
    have hnat : (4214110777 : ℕ)^8447*100000000000000^6399 ≤ 31958992766793^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4214110777 10000000000 31958992766793 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348832093/10000000000 : ℝ), (4487751561/10000000000 : ℝ), (4214110777/10000000000 : ℝ)] ![(1041079326173/3125000000000 : ℝ), (34726468773729/100000000000000 : ℝ), (31958992766793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348832093/10000000000 : ℝ)|^8447 ≤ (1041079326173/3125000000000 : ℝ)^6399
        have hw : |(4348832093/10000000000 : ℝ)|=(4348832093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4487751561/10000000000 : ℝ)|^8447 ≤ (34726468773729/100000000000000 : ℝ)^6399
        have hw : |(4487751561/10000000000 : ℝ)|=(4487751561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4214110777/10000000000 : ℝ)|^8447 ≤ (31958992766793/100000000000000 : ℝ)^6399
        have hw : |(4214110777/10000000000 : ℝ)|=(4214110777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1254_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1469/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5471/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11371/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7119/50000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (5471/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1469/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5471/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1469/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5471/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1469/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5471/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1469/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5471/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1469/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5471/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5471/50000 : ℝ) ^ (4223/1024 : ℝ) ≤ (10894625665916677/100000000000000000000 : ℝ) := by
    have hpowers : (5471/50000 : ℝ)^4223 ≤ (10894625665916677/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5471 : ℕ)^4223*100000000000000000000^1024 ≤ 10894625665916677^1024*50000^4223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5471 50000 10894625665916677 100000000000000000000 4223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5471/50000 : ℝ)) (X := (10894625665916677/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1469/10000 : ℝ) ^ (4223/1024 : ℝ) ≤ (36709491011040921/100000000000000000000 : ℝ) := by
    have hpowers : (1469/10000 : ℝ)^4223 ≤ (36709491011040921/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1469 : ℕ)^4223*100000000000000000000^1024 ≤ 36709491011040921^1024*10000^4223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1469 10000 36709491011040921 100000000000000000000 4223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1469/10000 : ℝ)) (X := (36709491011040921/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010894625665916677/50000000000000000000 : ℝ) ≤ (1250066038219869/1250000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (50010894625665916677/50000000000000000000 : ℝ)^1024 ≤ (1250066038219869/1250000000000000 : ℝ)^4223 := by
      have hnat : (50010894625665916677 : ℕ)^1024*1250000000000000^4223 ≤ 1250066038219869^4223*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010894625665916677 50000000000000000000 1250066038219869 1250000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250066038219869/1250000000000000 : ℝ)) (X := (50010894625665916677/50000000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023802058338478799/50000000000000000000 : ℝ) ≤ (5000577052198331/5000000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (50023802058338478799/50000000000000000000 : ℝ)^1024 ≤ (5000577052198331/5000000000000000 : ℝ)^4223 := by
      have hnat : (50023802058338478799 : ℕ)^1024*5000000000000000^4223 ≤ 5000577052198331^4223*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023802058338478799 50000000000000000000 5000577052198331 5000000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000577052198331/5000000000000000 : ℝ)) (X := (50023802058338478799/50000000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036709491011040921/50000000000000000000 : ℝ) ≤ (2500444975758593/2500000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (50036709491011040921/50000000000000000000 : ℝ)^1024 ≤ (2500444975758593/2500000000000000 : ℝ)^4223 := by
      have hnat : (50036709491011040921 : ℕ)^1024*2500000000000000^4223 ≤ 2500444975758593^4223*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036709491011040921 50000000000000000000 2500444975758593 2500000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500444975758593/2500000000000000 : ℝ)) (X := (50036709491011040921/50000000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10894625665916677/100000000000000000000 : ℝ) ≤ ((4683535639074613307/4685000000000000000 : ℝ)+2*(62579863771/37480000000000 : ℝ)*(5471/50000 : ℝ))^(4223/1024 : ℝ) := by
    rw [show (4683535639074613307/4685000000000000000 : ℝ)+2*(62579863771/37480000000000 : ℝ)*(5471/50000 : ℝ)=(1250066038219869/1250000000000000 : ℝ) by norm_num, show 1+2*(10894625665916677/100000000000000000000 : ℝ)=(50010894625665916677/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36709491011040921/100000000000000000000 : ℝ)+(10894625665916677/100000000000000000000 : ℝ) ≤ ((4683535639074613307/4685000000000000000 : ℝ)+(62579863771/37480000000000 : ℝ)*((1469/10000 : ℝ)+(5471/50000 : ℝ)))^(4223/1024 : ℝ) := by
    rw [show (4683535639074613307/4685000000000000000 : ℝ)+(62579863771/37480000000000 : ℝ)*((1469/10000 : ℝ)+(5471/50000 : ℝ))=(5000577052198331/5000000000000000 : ℝ) by norm_num, show 1+(36709491011040921/100000000000000000000 : ℝ)+(10894625665916677/100000000000000000000 : ℝ)=(50023802058338478799/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36709491011040921/100000000000000000000 : ℝ) ≤ ((4683535639074613307/4685000000000000000 : ℝ)+2*(62579863771/37480000000000 : ℝ)*(1469/10000 : ℝ))^(4223/1024 : ℝ) := by
    rw [show (4683535639074613307/4685000000000000000 : ℝ)+2*(62579863771/37480000000000 : ℝ)*(1469/10000 : ℝ)=(2500444975758593/2500000000000000 : ℝ) by norm_num, show 1+2*(36709491011040921/100000000000000000000 : ℝ)=(50036709491011040921/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4683535639074613307/4685000000000000000 : ℝ)*(X 1 0+X 2 0)+(62579863771/37480000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (5471/50000 : ℝ)) (hi := (1469/10000 : ℝ)) (c := (4683535639074613307/4685000000000000000 : ℝ)) (alpha := (62579863771/37480000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4683535639074613307/4685000000000000000 : ℝ)*(X 0 1+X 2 1)+(62579863771/37480000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (5471/50000 : ℝ)) (hi := (1469/10000 : ℝ)) (c := (4683535639074613307/4685000000000000000 : ℝ)) (alpha := (62579863771/37480000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4683535639074613307/4685000000000000000 : ℝ)*(X 0 2+X 1 2)+(62579863771/37480000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (5471/50000 : ℝ)) (hi := (1469/10000 : ℝ)) (c := (4683535639074613307/4685000000000000000 : ℝ)) (alpha := (62579863771/37480000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1056959999/5000000000 : ℝ)*X 0 0+(5397012513/10000000000 : ℝ)*X 0 1+(657710301/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345774747/10000000000 : ℝ)*X 1 0+(-2182622571/10000000000 : ℝ)*X 1 1+(328855151/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668221857/1250000000 : ℝ)*X 2 0+(526168231/1000000000 : ℝ)*X 2 1+(-2182622567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2174409967/5000000000 : ℝ)*X 0 0+(2106674033/5000000000 : ℝ)*X 0 1+(4488511063/10000000000 : ℝ)*X 0 2+(2174409967/5000000000 : ℝ)*X 1 0+(2106674033/5000000000 : ℝ)*X 1 1+(4488511063/10000000000 : ℝ)*X 1 2+(2174409967/5000000000 : ℝ)*X 2 0+(2106674033/5000000000 : ℝ)*X 2 1+(4488511063/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-528481467/2500000000 : ℝ)*X 0 0+(5262056171/10000000000 : ℝ)*X 0 1+(269831871/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311218593/10000000000 : ℝ)*X 1 0+(-1023833723/5000000000 : ℝ)*X 1 1+(5396637413/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655609167/5000000000 : ℝ)*X 2 0+(674579709/1250000000 : ℝ)*X 2 1+(-511916861/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4348832093/10000000000 : ℝ)*X 0 0+(4487751561/10000000000 : ℝ)*X 0 1+(4214110777/10000000000 : ℝ)*X 0 2+(4348832093/10000000000 : ℝ)*X 1 0+(4487751561/10000000000 : ℝ)*X 1 1+(4214110777/10000000000 : ℝ)*X 1 2+(4348832093/10000000000 : ℝ)*X 2 0+(4487751561/10000000000 : ℝ)*X 2 1+(4214110777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2087306444840224025871/234250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1860392283/100000000000000 : ℝ)*(base19) + (948914237/50000000000000 : ℝ)*(base23) + (264207867/100000000000000 : ℝ)*(upper3) + (60532221/100000000000000 : ℝ)*(upper4) + (216651169/100000000000000 : ℝ)*(upper5) + (344490190808453/6250000000000 : ℝ)*(major0) + (344490190808453/6250000000000 : ℝ)*(major1) + (344490190808453/6250000000000 : ℝ)*(major2) + (7389383792897907/100000000000000 : ℝ)*(sp0) + (7389428112088967/100000000000000 : ℝ)*(sp1) + (923678509331597/12500000000000 : ℝ)*(sp2) + (454278946897177/12500000000000 : ℝ)*(sp3) + (46179583343/100000000000000 : ℝ)*(sp4) + (1516324503/6250000000000 : ℝ)*(sp7) + (726851167273893/20000000000000 : ℝ)*(f.failure) + (1182308795597/16000000000 : ℝ)*(f.sum) + (1376098221861/468500000000000000000000000 : ℝ)*base66 + (492447651673009071/29281250000000000000000000000000 : ℝ)*base67 + (342851640154134071/29281250000000000000000000000000 : ℝ)*base69 + (315696958332397179/29281250000000000000000000000000 : ℝ)*base72 + (2025927641481/187400000000000000000000000 : ℝ)*base73 + (45039689194990929/29281250000000000000000000000000 : ℝ)*base76 + (481589408984240929/29281250000000000000000000000000 : ℝ)*base78 + (140512717573259071/29281250000000000000000000000000 : ℝ)*base79 + (170047810609/23425000000000000000000000 : ℝ)*base81 + (405067/400000000000000000000 : ℝ)*base89 + (405067/400000000000000000000 : ℝ)*base91 + (405067/400000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (293591047377917962468486557/29281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (190924659/12500000000000 : ℝ)*(base19) + (1254581153/100000000000000 : ℝ)*(base23) + (115501299/50000000000000 : ℝ)*(upper3) + (28392177/100000000000000 : ℝ)*(lower4) + (3330161/5000000000000 : ℝ)*(upper5) + (1385608955862583/25000000000000 : ℝ)*(major0) + (1385608955862583/25000000000000 : ℝ)*(major1) + (1385608955862583/25000000000000 : ℝ)*(major2) + (34597639877/100000000000000 : ℝ)*(sp1) + (40141141269/100000000000000 : ℝ)*(sp2) + (7430444010301491/100000000000000 : ℝ)*(sp4) + (7430407885264341/100000000000000 : ℝ)*(sp5) + (7430402614579069/100000000000000 : ℝ)*(sp6) + (182721365118977/5000000000000 : ℝ)*(sp7) + (182721365118977/5000000000000 : ℝ)*(f.failure) + (7430444010301491/100000000000000 : ℝ)*(f.sum) + (2293204532499/468500000000000000000000000 : ℝ)*base66 + (59040960387191981/117125000000000000000000000000000 : ℝ)*base67 + (1524323563341816981/117125000000000000000000000000000 : ℝ)*base69 + (498266427388816981/117125000000000000000000000000000 : ℝ)*base71 + (2800999655533/937000000000000000000000000 : ℝ)*base74 + (4085343740846191981/117125000000000000000000000000000 : ℝ)*base75 + (90135018159433019/117125000000000000000000000000000 : ℝ)*base78 + (34528127163566981/117125000000000000000000000000000 : ℝ)*base79 + (4283188531509/937000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1091537/100000000000000000000 : ℝ)*base90 + (1091537/100000000000000000000 : ℝ)*base92 + (1091537/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1254_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1469/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5471/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1254_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1254_s5_0 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-132146979/625000000 : ℝ)*x 0 + (539212419/1000000000 : ℝ)*x 1 + (1316571713/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132146979/625000000 : ℝ)^8447 ≤ (2571758489413/20000000000000 : ℝ)^6399 := by
    have hnat : (132146979 : ℕ)^8447*20000000000000^6399 ≤ 2571758489413^6399*625000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132146979 625000000 2571758489413 20000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539212419/1000000000 : ℝ)^8447 ≤ (4424962919023/10000000000000 : ℝ)^6399 := by
    have hnat : (539212419 : ℕ)^8447*10000000000000^6399 ≤ 4424962919023^6399*1000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539212419 1000000000 4424962919023 10000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316571713/2500000000 : ℝ)^8447 ≤ (10722894584877/25000000000000 : ℝ)^6399 := by
    have hnat : (1316571713 : ℕ)^8447*25000000000000^6399 ≤ 10722894584877^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316571713 2500000000 10722894584877 25000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-132146979/625000000 : ℝ), (539212419/1000000000 : ℝ), (1316571713/2500000000 : ℝ)] ![(2571758489413/20000000000000 : ℝ), (4424962919023/10000000000000 : ℝ), (10722894584877/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-132146979/625000000 : ℝ)|^8447 ≤ (2571758489413/20000000000000 : ℝ)^6399
        have hw : |(-132146979/625000000 : ℝ)|=(132146979/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539212419/1000000000 : ℝ)|^8447 ≤ (4424962919023/10000000000000 : ℝ)^6399
        have hw : |(539212419/1000000000 : ℝ)|=(539212419/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316571713/2500000000 : ℝ)|^8447 ≤ (10722894584877/25000000000000 : ℝ)^6399
        have hw : |(1316571713/2500000000 : ℝ)|=(1316571713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s5_1 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068907283/2000000000 : ℝ)*x 0 + (-108908377/500000000 : ℝ)*x 1 + (105325737/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068907283/2000000000 : ℝ)^8447 ≤ (21867425275633/50000000000000 : ℝ)^6399 := by
    have hnat : (1068907283 : ℕ)^8447*50000000000000^6399 ≤ 21867425275633^6399*2000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068907283 2000000000 21867425275633 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108908377/500000000 : ℝ)^8447 ≤ (1671696388641/12500000000000 : ℝ)^6399 := by
    have hnat : (108908377 : ℕ)^8447*12500000000000^6399 ≤ 1671696388641^6399*500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108908377 500000000 1671696388641 12500000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105325737/200000000 : ℝ)^8447 ≤ (21445789159003/50000000000000 : ℝ)^6399 := by
    have hnat : (105325737 : ℕ)^8447*50000000000000^6399 ≤ 21445789159003^6399*200000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105325737 200000000 21445789159003 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068907283/2000000000 : ℝ), (-108908377/500000000 : ℝ), (105325737/200000000 : ℝ)] ![(21867425275633/50000000000000 : ℝ), (1671696388641/12500000000000 : ℝ), (21445789159003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068907283/2000000000 : ℝ)|^8447 ≤ (21867425275633/50000000000000 : ℝ)^6399
        have hw : |(1068907283/2000000000 : ℝ)|=(1068907283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-108908377/500000000 : ℝ)|^8447 ≤ (1671696388641/12500000000000 : ℝ)^6399
        have hw : |(-108908377/500000000 : ℝ)|=(108908377/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105325737/200000000 : ℝ)|^8447 ≤ (21445789159003/50000000000000 : ℝ)^6399
        have hw : |(105325737/200000000 : ℝ)|=(105325737/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s5_2 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (13361341/25000000 : ℝ)*x 0 + (5266286849/10000000000 : ℝ)*x 1 + (-1089083781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13361341/25000000 : ℝ)^8447 ≤ (8746970077847/20000000000000 : ℝ)^6399 := by
    have hnat : (13361341 : ℕ)^8447*20000000000000^6399 ≤ 8746970077847^6399*25000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13361341 25000000 8746970077847 20000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266286849/10000000000 : ℝ)^8447 ≤ (21445789153627/50000000000000 : ℝ)^6399 := by
    have hnat : (5266286849 : ℕ)^8447*50000000000000^6399 ≤ 21445789153627^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266286849 10000000000 21445789153627 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1089083781/5000000000 : ℝ)^8447 ≤ (3343392821859/25000000000000 : ℝ)^6399 := by
    have hnat : (1089083781 : ℕ)^8447*25000000000000^6399 ≤ 3343392821859^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089083781 5000000000 3343392821859 25000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13361341/25000000 : ℝ), (5266286849/10000000000 : ℝ), (-1089083781/5000000000 : ℝ)] ![(8746970077847/20000000000000 : ℝ), (21445789153627/50000000000000 : ℝ), (3343392821859/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13361341/25000000 : ℝ)|^8447 ≤ (8746970077847/20000000000000 : ℝ)^6399
        have hw : |(13361341/25000000 : ℝ)|=(13361341/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266286849/10000000000 : ℝ)|^8447 ≤ (21445789153627/50000000000000 : ℝ)^6399
        have hw : |(5266286849/10000000000 : ℝ)|=(5266286849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1089083781/5000000000 : ℝ)|^8447 ≤ (3343392821859/25000000000000 : ℝ)^6399
        have hw : |(-1089083781/5000000000 : ℝ)|=(1089083781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s5_3 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349073001/10000000000 : ℝ)*x 0 + (1055741633/2500000000 : ℝ)*x 1 + (4478828081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349073001/10000000000 : ℝ)^8447 ≤ (4164621825259/12500000000000 : ℝ)^6399 := by
    have hnat : (4349073001 : ℕ)^8447*12500000000000^6399 ≤ 4164621825259^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349073001 10000000000 4164621825259 12500000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055741633/2500000000 : ℝ)^8447 ≤ (32047677541149/100000000000000 : ℝ)^6399 := by
    have hnat : (1055741633 : ℕ)^8447*100000000000000^6399 ≤ 32047677541149^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055741633 2500000000 32047677541149 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4478828081/10000000000 : ℝ)^8447 ≤ (432941847949/1250000000000 : ℝ)^6399 := by
    have hnat : (4478828081 : ℕ)^8447*1250000000000^6399 ≤ 432941847949^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478828081 10000000000 432941847949 1250000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349073001/10000000000 : ℝ), (1055741633/2500000000 : ℝ), (4478828081/10000000000 : ℝ)] ![(4164621825259/12500000000000 : ℝ), (32047677541149/100000000000000 : ℝ), (432941847949/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349073001/10000000000 : ℝ)|^8447 ≤ (4164621825259/12500000000000 : ℝ)^6399
        have hw : |(4349073001/10000000000 : ℝ)|=(4349073001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1055741633/2500000000 : ℝ)|^8447 ≤ (32047677541149/100000000000000 : ℝ)^6399
        have hw : |(1055741633/2500000000 : ℝ)|=(1055741633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4478828081/10000000000 : ℝ)|^8447 ≤ (432941847949/1250000000000 : ℝ)^6399
        have hw : |(4478828081/10000000000 : ℝ)|=(4478828081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s5_4 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-42287123/200000000 : ℝ)*x 0 + (5266610607/10000000000 : ℝ)*x 1 + (2695899771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42287123/200000000 : ℝ)^8447 ≤ (6429414230591/50000000000000 : ℝ)^6399 := by
    have hnat : (42287123 : ℕ)^8447*50000000000000^6399 ≤ 6429414230591^6399*200000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42287123 200000000 6429414230591 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266610607/10000000000 : ℝ)^8447 ≤ (42895059136199/100000000000000 : ℝ)^6399 := by
    have hnat : (5266610607 : ℕ)^8447*100000000000000^6399 ≤ 42895059136199^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266610607 10000000000 42895059136199 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695899771/5000000000 : ℝ)^8447 ≤ (884922247641/2000000000000 : ℝ)^6399 := by
    have hnat : (2695899771 : ℕ)^8447*2000000000000^6399 ≤ 884922247641^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695899771 5000000000 884922247641 2000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42287123/200000000 : ℝ), (5266610607/10000000000 : ℝ), (2695899771/5000000000 : ℝ)] ![(6429414230591/50000000000000 : ℝ), (42895059136199/100000000000000 : ℝ), (884922247641/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42287123/200000000 : ℝ)|^8447 ≤ (6429414230591/50000000000000 : ℝ)^6399
        have hw : |(-42287123/200000000 : ℝ)|=(42287123/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266610607/10000000000 : ℝ)|^8447 ≤ (42895059136199/100000000000000 : ℝ)^6399
        have hw : |(5266610607/10000000000 : ℝ)|=(5266610607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695899771/5000000000 : ℝ)|^8447 ≤ (884922247641/2000000000000 : ℝ)^6399
        have hw : |(2695899771/5000000000 : ℝ)|=(2695899771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s5_5 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656201131/5000000000 : ℝ)*x 0 + (-513163731/2500000000 : ℝ)*x 1 + (5391800119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656201131/5000000000 : ℝ)^8447 ≤ (43388068815011/100000000000000 : ℝ)^6399 := by
    have hnat : (2656201131 : ℕ)^8447*100000000000000^6399 ≤ 43388068815011^6399*5000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656201131 5000000000 43388068815011 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513163731/2500000000 : ℝ)^8447 ≤ (6182906267327/50000000000000 : ℝ)^6399 := by
    have hnat : (513163731 : ℕ)^8447*50000000000000^6399 ≤ 6182906267327^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513163731 2500000000 6182906267327 50000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391800119/10000000000 : ℝ)^8447 ≤ (44246118632447/100000000000000 : ℝ)^6399 := by
    have hnat : (5391800119 : ℕ)^8447*100000000000000^6399 ≤ 44246118632447^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391800119 10000000000 44246118632447 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656201131/5000000000 : ℝ), (-513163731/2500000000 : ℝ), (5391800119/10000000000 : ℝ)] ![(43388068815011/100000000000000 : ℝ), (6182906267327/50000000000000 : ℝ), (44246118632447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656201131/5000000000 : ℝ)|^8447 ≤ (43388068815011/100000000000000 : ℝ)^6399
        have hw : |(2656201131/5000000000 : ℝ)|=(2656201131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-513163731/2500000000 : ℝ)|^8447 ≤ (6182906267327/50000000000000 : ℝ)^6399
        have hw : |(-513163731/2500000000 : ℝ)|=(513163731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391800119/10000000000 : ℝ)|^8447 ≤ (44246118632447/100000000000000 : ℝ)^6399
        have hw : |(5391800119/10000000000 : ℝ)|=(5391800119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s5_6 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (33202511/62500000 : ℝ)*x 0 + (5391800787/10000000000 : ℝ)*x 1 + (-410530939/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33202511/62500000 : ℝ)^8447 ≤ (677938490669/1562500000000 : ℝ)^6399 := by
    have hnat : (33202511 : ℕ)^8447*1562500000000^6399 ≤ 677938490669^6399*62500000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33202511 62500000 677938490669 1562500000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391800787/10000000000 : ℝ)^8447 ≤ (44246125868609/100000000000000 : ℝ)^6399 := by
    have hnat : (5391800787 : ℕ)^8447*100000000000000^6399 ≤ 44246125868609^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391800787 10000000000 44246125868609 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (410530939/2000000000 : ℝ)^8447 ≤ (12365810713559/100000000000000 : ℝ)^6399 := by
    have hnat : (410530939 : ℕ)^8447*100000000000000^6399 ≤ 12365810713559^6399*2000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410530939 2000000000 12365810713559 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33202511/62500000 : ℝ), (5391800787/10000000000 : ℝ), (-410530939/2000000000 : ℝ)] ![(677938490669/1562500000000 : ℝ), (44246125868609/100000000000000 : ℝ), (12365810713559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33202511/62500000 : ℝ)|^8447 ≤ (677938490669/1562500000000 : ℝ)^6399
        have hw : |(33202511/62500000 : ℝ)|=(33202511/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391800787/10000000000 : ℝ)|^8447 ≤ (44246125868609/100000000000000 : ℝ)^6399
        have hw : |(5391800787/10000000000 : ℝ)|=(5391800787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-410530939/2000000000 : ℝ)|^8447 ≤ (12365810713559/100000000000000 : ℝ)^6399
        have hw : |(-410530939/2000000000 : ℝ)|=(410530939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1254_s5_7 (p : ℝ) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1087270749/2500000000 : ℝ)*x 0 + (4478170883/10000000000 : ℝ)*x 1 + (4223626099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087270749/2500000000 : ℝ)^8447 ≤ (33317075676711/100000000000000 : ℝ)^6399 := by
    have hnat : (1087270749 : ℕ)^8447*100000000000000^6399 ≤ 33317075676711^6399*2500000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087270749 2500000000 33317075676711 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4478170883/10000000000 : ℝ)^8447 ≤ (3462863924083/10000000000000 : ℝ)^6399 := by
    have hnat : (4478170883 : ℕ)^8447*10000000000000^6399 ≤ 3462863924083^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478170883 10000000000 3462863924083 10000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4223626099/10000000000 : ℝ)^8447 ≤ (32054285070169/100000000000000 : ℝ)^6399 := by
    have hnat : (4223626099 : ℕ)^8447*100000000000000^6399 ≤ 32054285070169^6399*10000000000^8447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223626099 10000000000 32054285070169 100000000000000 8447 6399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8447/2048 : ℝ)) 8447 6399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087270749/2500000000 : ℝ), (4478170883/10000000000 : ℝ), (4223626099/10000000000 : ℝ)] ![(33317075676711/100000000000000 : ℝ), (3462863924083/10000000000000 : ℝ), (32054285070169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087270749/2500000000 : ℝ)|^8447 ≤ (33317075676711/100000000000000 : ℝ)^6399
        have hw : |(1087270749/2500000000 : ℝ)|=(1087270749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4478170883/10000000000 : ℝ)|^8447 ≤ (3462863924083/10000000000000 : ℝ)^6399
        have hw : |(4478170883/10000000000 : ℝ)|=(4478170883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4223626099/10000000000 : ℝ)|^8447 ≤ (32054285070169/100000000000000 : ℝ)^6399
        have hw : |(4223626099/10000000000 : ℝ)|=(4223626099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1254_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11469/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2827/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11371/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11371/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11371/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11371/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11371/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11371/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11371/100000 : ℝ) ^ (4223/1024 : ℝ) ≤ (3191769724125629/25000000000000000000 : ℝ) := by
    have hpowers : (11371/100000 : ℝ)^4223 ≤ (3191769724125629/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11371 : ℕ)^4223*25000000000000000000^1024 ≤ 3191769724125629^1024*100000^4223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11371 100000 3191769724125629 25000000000000000000 4223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11371/100000 : ℝ)) (X := (3191769724125629/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7119/50000 : ℝ) ^ (4223/1024 : ℝ) ≤ (3227035833856807/10000000000000000000 : ℝ) := by
    have hpowers : (7119/50000 : ℝ)^4223 ≤ (3227035833856807/10000000000000000000 : ℝ)^1024 := by
      have hnat : (7119 : ℕ)^4223*10000000000000000000^1024 ≤ 3227035833856807^1024*50000^4223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7119 50000 3227035833856807 10000000000000000000 4223 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7119/50000 : ℝ)) (X := (3227035833856807/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503191769724125629/12500000000000000000 : ℝ) ≤ (625038693537187/625000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (12503191769724125629/12500000000000000000 : ℝ)^1024 ≤ (625038693537187/625000000000000 : ℝ)^4223 := by
      have hnat : (12503191769724125629 : ℕ)^1024*625000000000000^4223 ≤ 625038693537187^4223*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503191769724125629 12500000000000000000 625038693537187 625000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625038693537187/625000000000000 : ℝ)) (X := (12503191769724125629/12500000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022518718617535293/50000000000000000000 : ℝ) ≤ (10001091888959983/10000000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (50022518718617535293/50000000000000000000 : ℝ)^1024 ≤ (10001091888959983/10000000000000000 : ℝ)^4223 := by
      have hnat : (50022518718617535293 : ℕ)^1024*10000000000000000^4223 ≤ 10001091888959983^4223*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022518718617535293 50000000000000000000 10001091888959983 10000000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001091888959983/10000000000000000 : ℝ)) (X := (50022518718617535293/50000000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003227035833856807/5000000000000000000 : ℝ) ≤ (5000782340662487/5000000000000000 : ℝ) ^ (4223/1024 : ℝ) := by
    have hpowers : (5003227035833856807/5000000000000000000 : ℝ)^1024 ≤ (5000782340662487/5000000000000000 : ℝ)^4223 := by
      have hnat : (5003227035833856807 : ℕ)^1024*5000000000000000^4223 ≤ 5000782340662487^4223*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003227035833856807 5000000000000000000 5000782340662487 5000000000000000 1024 4223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000782340662487/5000000000000000 : ℝ)) (X := (5003227035833856807/5000000000000000000 : ℝ)) (by norm_num) 4223 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3191769724125629/25000000000000000000 : ℝ) ≤ ((14330511352986608371/14335000000000000000 : ℝ)+2*(472792364991/286700000000000 : ℝ)*(11371/100000 : ℝ))^(4223/1024 : ℝ) := by
    rw [show (14330511352986608371/14335000000000000000 : ℝ)+2*(472792364991/286700000000000 : ℝ)*(11371/100000 : ℝ)=(625038693537187/625000000000000 : ℝ) by norm_num, show 1+2*(3191769724125629/25000000000000000000 : ℝ)=(12503191769724125629/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3227035833856807/10000000000000000000 : ℝ)+(3191769724125629/25000000000000000000 : ℝ) ≤ ((14330511352986608371/14335000000000000000 : ℝ)+(472792364991/286700000000000 : ℝ)*((7119/50000 : ℝ)+(11371/100000 : ℝ)))^(4223/1024 : ℝ) := by
    rw [show (14330511352986608371/14335000000000000000 : ℝ)+(472792364991/286700000000000 : ℝ)*((7119/50000 : ℝ)+(11371/100000 : ℝ))=(10001091888959983/10000000000000000 : ℝ) by norm_num, show 1+(3227035833856807/10000000000000000000 : ℝ)+(3191769724125629/25000000000000000000 : ℝ)=(50022518718617535293/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3227035833856807/10000000000000000000 : ℝ) ≤ ((14330511352986608371/14335000000000000000 : ℝ)+2*(472792364991/286700000000000 : ℝ)*(7119/50000 : ℝ))^(4223/1024 : ℝ) := by
    rw [show (14330511352986608371/14335000000000000000 : ℝ)+2*(472792364991/286700000000000 : ℝ)*(7119/50000 : ℝ)=(5000782340662487/5000000000000000 : ℝ) by norm_num, show 1+2*(3227035833856807/10000000000000000000 : ℝ)=(5003227035833856807/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14330511352986608371/14335000000000000000 : ℝ)*(X 1 0+X 2 0)+(472792364991/286700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (11371/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (14330511352986608371/14335000000000000000 : ℝ)) (alpha := (472792364991/286700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14330511352986608371/14335000000000000000 : ℝ)*(X 0 1+X 2 1)+(472792364991/286700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (11371/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (14330511352986608371/14335000000000000000 : ℝ)) (alpha := (472792364991/286700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14330511352986608371/14335000000000000000 : ℝ)*(X 0 2+X 1 2)+(472792364991/286700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4223/1024 : ℝ)) (lo := (11371/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (14330511352986608371/14335000000000000000 : ℝ)) (alpha := (472792364991/286700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-132146979/625000000 : ℝ)*X 0 0+(539212419/1000000000 : ℝ)*X 0 1+(1316571713/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068907283/2000000000 : ℝ)*X 1 0+(-108908377/500000000 : ℝ)*X 1 1+(105325737/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((13361341/25000000 : ℝ)*X 2 0+(5266286849/10000000000 : ℝ)*X 2 1+(-1089083781/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4349073001/10000000000 : ℝ)*X 0 0+(1055741633/2500000000 : ℝ)*X 0 1+(4478828081/10000000000 : ℝ)*X 0 2+(4349073001/10000000000 : ℝ)*X 1 0+(1055741633/2500000000 : ℝ)*X 1 1+(4478828081/10000000000 : ℝ)*X 1 2+(4349073001/10000000000 : ℝ)*X 2 0+(1055741633/2500000000 : ℝ)*X 2 1+(4478828081/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-42287123/200000000 : ℝ)*X 0 0+(5266610607/10000000000 : ℝ)*X 0 1+(2695899771/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656201131/5000000000 : ℝ)*X 1 0+(-513163731/2500000000 : ℝ)*X 1 1+(5391800119/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((33202511/62500000 : ℝ)*X 2 0+(5391800787/10000000000 : ℝ)*X 2 1+(-410530939/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1087270749/2500000000 : ℝ)*X 0 0+(4478170883/10000000000 : ℝ)*X 0 1+(4223626099/10000000000 : ℝ)*X 0 2+(1087270749/2500000000 : ℝ)*X 1 0+(4478170883/10000000000 : ℝ)*X 1 1+(4223626099/10000000000 : ℝ)*X 1 2+(1087270749/2500000000 : ℝ)*X 2 0+(4478170883/10000000000 : ℝ)*X 2 1+(4223626099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1254_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7584870198293593829265749667/716750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1007025383/50000000000000 : ℝ)*(base19) + (1869610929/100000000000000 : ℝ)*(base23) + (65276079/100000000000000 : ℝ)*(lower2) + (34452399/12500000000000 : ℝ)*(upper3) + (146552279/100000000000000 : ℝ)*(upper5) + (5927649521736059/100000000000000 : ℝ)*(major0) + (5927649521736059/100000000000000 : ℝ)*(major1) + (5927649521736059/100000000000000 : ℝ)*(major2) + (7946825316635831/100000000000000 : ℝ)*(sp0) + (3973438588221803/50000000000000 : ℝ)*(sp1) + (3973438660441721/50000000000000 : ℝ)*(sp2) + (1954194988647219/50000000000000 : ℝ)*(sp3) + (2693692927/5000000000000 : ℝ)*(sp4) + (3690367457/12500000000000 : ℝ)*(sp7) + (1954209750117047/50000000000000 : ℝ)*(f.failure) + (7946879190494371/100000000000000 : ℝ)*(f.sum) + (90358458959581/14335000000000000000000000000 : ℝ)*base66 + (20768139121896399889/1433500000000000000000000000000000 : ℝ)*base67 + (5217642420633600111/1433500000000000000000000000000000 : ℝ)*base70 + (4153588325001399889/1433500000000000000000000000000000 : ℝ)*base71 + (28405054493571/14335000000000000000000000000 : ℝ)*base74 + (29059898838501600111/1433500000000000000000000000000000 : ℝ)*base76 + (15149028615383600111/1433500000000000000000000000000000 : ℝ)*base78 + (12387380699001600111/1433500000000000000000000000000000 : ℝ)*base80 + (8861446492561/14335000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (13760793/1000000000000000000000 : ℝ)*base89 + (13760793/1000000000000000000000 : ℝ)*base91 + (13760793/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62427220454410521277970319/17918750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23946431/20000000000000 : ℝ)*(base8) + (72137049/25000000000000 : ℝ)*(base15) + (172027169/25000000000000 : ℝ)*(base29) + (43720239/50000000000000 : ℝ)*(upper2) + (17573229/5000000000000 : ℝ)*(lower4) + (372390489452941/6250000000000 : ℝ)*(major0) + (1489562129838933/25000000000000 : ℝ)*(major1) + (1489562129838933/25000000000000 : ℝ)*(major2) + (30293591689/100000000000000 : ℝ)*(sp2) + (5828052589/50000000000000 : ℝ)*(sp3) + (7987901730738567/100000000000000 : ℝ)*(sp4) + (159758017476277/2000000000000 : ℝ)*(sp5) + (1996967717192589/25000000000000 : ℝ)*(sp6) + (245536463500337/6250000000000 : ℝ)*(sp7) + (392859507211057/10000000000000 : ℝ)*(f.failure) + (3993950925235361/50000000000000 : ℝ)*(f.sum) + (10417533247703/3583750000000000000000000000 : ℝ)*base65 + (6478628482948716857/358375000000000000000000000000000 : ℝ)*base68 + (5031181079487841857/358375000000000000000000000000000 : ℝ)*base70 + (1518891259352855889/89593750000000000000000000000000 : ℝ)*base72 + (1400218947367/7167500000000000000000000000 : ℝ)*base73 + (4025081205738291857/358375000000000000000000000000000 : ℝ)*base76 + (44292586784730889/89593750000000000000000000000000 : ℝ)*base78 + (4580811379071166857/358375000000000000000000000000000 : ℝ)*base80 + (2908195321737/7167500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1673983/200000000000000000000 : ℝ)*base89 + (1673983/200000000000000000000 : ℝ)*base91 + (1673983/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1254_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11469/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2827/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1254_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1254_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (506/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2387/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11469/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2827/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1254_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1254_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1254_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4223/1024 : ℝ) ≤ p) (hpb : p ≤ (8447/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30332719/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (506/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2387/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11469/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2827/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1254_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
