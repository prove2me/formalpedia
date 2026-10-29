-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1549_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:09:30.386445+00:00
-- url     : https://prove2.me/submissions/3cb1ce4d-d240-4dde-8d54-829c34b4aca4

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
theorem support_rectangle_w1549_box_0 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-40186727/250000000 : ℝ)*x 0 + (107976893/200000000 : ℝ)*x 1 + (5398845309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40186727/250000000 : ℝ)^4595 ≤ (2379252497339/25000000000000 : ℝ)^3571 := by
    have hnat : (40186727 : ℕ)^4595*25000000000000^3571 ≤ 2379252497339^3571*250000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40186727 250000000 2379252497339 25000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107976893/200000000 : ℝ)^4595 ≤ (45241491442713/100000000000000 : ℝ)^3571 := by
    have hnat : (107976893 : ℕ)^4595*100000000000000^3571 ≤ 45241491442713^3571*200000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107976893 200000000 45241491442713 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5398845309/10000000000 : ℝ)^4595 ≤ (45241498548581/100000000000000 : ℝ)^3571 := by
    have hnat : (5398845309 : ℕ)^4595*100000000000000^3571 ≤ 45241498548581^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398845309 10000000000 45241498548581 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-40186727/250000000 : ℝ), (107976893/200000000 : ℝ), (5398845309/10000000000 : ℝ)] ![(2379252497339/25000000000000 : ℝ), (45241491442713/100000000000000 : ℝ), (45241498548581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-40186727/250000000 : ℝ)|^4595 ≤ (2379252497339/25000000000000 : ℝ)^3571
        have hw : |(-40186727/250000000 : ℝ)|=(40186727/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107976893/200000000 : ℝ)|^4595 ≤ (45241491442713/100000000000000 : ℝ)^3571
        have hw : |(107976893/200000000 : ℝ)|=(107976893/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5398845309/10000000000 : ℝ)|^4595 ≤ (45241498548581/100000000000000 : ℝ)^3571
        have hw : |(5398845309/10000000000 : ℝ)|=(5398845309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_box_1 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16472171/31250000 : ℝ)*x 0 + (-1784930563/10000000000 : ℝ)*x 1 + (5398845231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16472171/31250000 : ℝ)^4595 ≤ (43868688823833/100000000000000 : ℝ)^3571 := by
    have hnat : (16472171 : ℕ)^4595*100000000000000^3571 ≤ 43868688823833^3571*31250000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16472171 31250000 43868688823833 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1784930563/10000000000 : ℝ)^4595 ≤ (1088981345889/10000000000000 : ℝ)^3571 := by
    have hnat : (1784930563 : ℕ)^4595*10000000000000^3571 ≤ 1088981345889^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1784930563 10000000000 1088981345889 10000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5398845231/10000000000 : ℝ)^4595 ≤ (22620748853761/50000000000000 : ℝ)^3571 := by
    have hnat : (5398845231 : ℕ)^4595*50000000000000^3571 ≤ 22620748853761^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398845231 10000000000 22620748853761 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16472171/31250000 : ℝ), (-1784930563/10000000000 : ℝ), (5398845231/10000000000 : ℝ)] ![(43868688823833/100000000000000 : ℝ), (1088981345889/10000000000000 : ℝ), (22620748853761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16472171/31250000 : ℝ)|^4595 ≤ (43868688823833/100000000000000 : ℝ)^3571
        have hw : |(16472171/31250000 : ℝ)|=(16472171/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1784930563/10000000000 : ℝ)|^4595 ≤ (1088981345889/10000000000000 : ℝ)^3571
        have hw : |(-1784930563/10000000000 : ℝ)|=(1784930563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5398845231/10000000000 : ℝ)|^4595 ≤ (22620748853761/50000000000000 : ℝ)^3571
        have hw : |(5398845231/10000000000 : ℝ)|=(5398845231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_box_2 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1317773649/2500000000 : ℝ)*x 0 + (5398845567/10000000000 : ℝ)*x 1 + (-178493027/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317773649/2500000000 : ℝ)^4595 ≤ (8773737499183/20000000000000 : ℝ)^3571 := by
    have hnat : (1317773649 : ℕ)^4595*20000000000000^3571 ≤ 8773737499183^3571*2500000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317773649 2500000000 8773737499183 20000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398845567/10000000000 : ℝ)^4595 ≤ (9048300266109/20000000000000 : ℝ)^3571 := by
    have hnat : (5398845567 : ℕ)^4595*20000000000000^3571 ≤ 9048300266109^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398845567 10000000000 9048300266109 20000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (178493027/1000000000 : ℝ)^4595 ≤ (10889811158707/100000000000000 : ℝ)^3571 := by
    have hnat : (178493027 : ℕ)^4595*100000000000000^3571 ≤ 10889811158707^3571*1000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178493027 1000000000 10889811158707 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1317773649/2500000000 : ℝ), (5398845567/10000000000 : ℝ), (-178493027/1000000000 : ℝ)] ![(8773737499183/20000000000000 : ℝ), (9048300266109/20000000000000 : ℝ), (10889811158707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1317773649/2500000000 : ℝ)|^4595 ≤ (8773737499183/20000000000000 : ℝ)^3571
        have hw : |(1317773649/2500000000 : ℝ)|=(1317773649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398845567/10000000000 : ℝ)|^4595 ≤ (9048300266109/20000000000000 : ℝ)^3571
        have hw : |(5398845567/10000000000 : ℝ)|=(5398845567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-178493027/1000000000 : ℝ)|^4595 ≤ (10889811158707/100000000000000 : ℝ)^3571
        have hw : |(-178493027/1000000000 : ℝ)|=(178493027/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_box_3 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (445434013/1000000000 : ℝ)*x 0 + (4158855121/10000000000 : ℝ)*x 1 + (831771/2000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (445434013/1000000000 : ℝ)^4595 ≤ (7064809506357/20000000000000 : ℝ)^3571 := by
    have hnat : (445434013 : ℕ)^4595*20000000000000^3571 ≤ 7064809506357^3571*1000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445434013 1000000000 7064809506357 20000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4158855121/10000000000 : ℝ)^4595 ≤ (16168988417303/50000000000000 : ℝ)^3571 := by
    have hnat : (4158855121 : ℕ)^4595*50000000000000^3571 ≤ 16168988417303^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158855121 10000000000 16168988417303 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (831771/2000000 : ℝ)^4595 ≤ (2021123476497/6250000000000 : ℝ)^3571 := by
    have hnat : (831771 : ℕ)^4595*6250000000000^3571 ≤ 2021123476497^3571*2000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831771 2000000 2021123476497 6250000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(445434013/1000000000 : ℝ), (4158855121/10000000000 : ℝ), (831771/2000000 : ℝ)] ![(7064809506357/20000000000000 : ℝ), (16168988417303/50000000000000 : ℝ), (2021123476497/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(445434013/1000000000 : ℝ)|^4595 ≤ (7064809506357/20000000000000 : ℝ)^3571
        have hw : |(445434013/1000000000 : ℝ)|=(445434013/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4158855121/10000000000 : ℝ)|^4595 ≤ (16168988417303/50000000000000 : ℝ)^3571
        have hw : |(4158855121/10000000000 : ℝ)|=(4158855121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(831771/2000000 : ℝ)|^4595 ≤ (2021123476497/6250000000000 : ℝ)^3571
        have hw : |(831771/2000000 : ℝ)|=(831771/2000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_box_4 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2027359381/10000000000 : ℝ)*x 0 + (5244635703/10000000000 : ℝ)*x 1 + (5244635203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2027359381/10000000000 : ℝ)^4595 ≤ (12828919327159/100000000000000 : ℝ)^3571 := by
    have hnat : (2027359381 : ℕ)^4595*100000000000000^3571 ≤ 12828919327159^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2027359381 10000000000 12828919327159 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244635703/10000000000 : ℝ)^4595 ≤ (43585543003523/100000000000000 : ℝ)^3571 := by
    have hnat : (5244635703 : ℕ)^4595*100000000000000^3571 ≤ 43585543003523^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244635703 10000000000 43585543003523 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244635203/10000000000 : ℝ)^4595 ≤ (43585537656737/100000000000000 : ℝ)^3571 := by
    have hnat : (5244635203 : ℕ)^4595*100000000000000^3571 ≤ 43585537656737^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244635203 10000000000 43585537656737 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2027359381/10000000000 : ℝ), (5244635703/10000000000 : ℝ), (5244635203/10000000000 : ℝ)] ![(12828919327159/100000000000000 : ℝ), (43585543003523/100000000000000 : ℝ), (43585537656737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2027359381/10000000000 : ℝ)|^4595 ≤ (12828919327159/100000000000000 : ℝ)^3571
        have hw : |(-2027359381/10000000000 : ℝ)|=(2027359381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244635703/10000000000 : ℝ)|^4595 ≤ (43585543003523/100000000000000 : ℝ)^3571
        have hw : |(5244635703/10000000000 : ℝ)|=(5244635703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244635203/10000000000 : ℝ)|^4595 ≤ (43585537656737/100000000000000 : ℝ)^3571
        have hw : |(5244635203/10000000000 : ℝ)|=(5244635203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_box_5 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378155991/10000000000 : ℝ)*x 0 + (-924535733/5000000000 : ℝ)*x 1 + (5244636027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378155991/10000000000 : ℝ)^4595 ≤ (11254633087031/25000000000000 : ℝ)^3571 := by
    have hnat : (5378155991 : ℕ)^4595*25000000000000^3571 ≤ 11254633087031^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378155991 10000000000 11254633087031 25000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (924535733/5000000000 : ℝ)^4595 ≤ (5697960583271/50000000000000 : ℝ)^3571 := by
    have hnat : (924535733 : ℕ)^4595*50000000000000^3571 ≤ 5697960583271^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924535733 5000000000 5697960583271 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244636027/10000000000 : ℝ)^4595 ≤ (43585546468241/100000000000000 : ℝ)^3571 := by
    have hnat : (5244636027 : ℕ)^4595*100000000000000^3571 ≤ 43585546468241^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244636027 10000000000 43585546468241 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378155991/10000000000 : ℝ), (-924535733/5000000000 : ℝ), (5244636027/10000000000 : ℝ)] ![(11254633087031/25000000000000 : ℝ), (5697960583271/50000000000000 : ℝ), (43585546468241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378155991/10000000000 : ℝ)|^4595 ≤ (11254633087031/25000000000000 : ℝ)^3571
        have hw : |(5378155991/10000000000 : ℝ)|=(5378155991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-924535733/5000000000 : ℝ)|^4595 ≤ (5697960583271/50000000000000 : ℝ)^3571
        have hw : |(-924535733/5000000000 : ℝ)|=(924535733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244636027/10000000000 : ℝ)|^4595 ≤ (43585546468241/100000000000000 : ℝ)^3571
        have hw : |(5244636027/10000000000 : ℝ)|=(5244636027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_box_6 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378158061/10000000000 : ℝ)*x 0 + (5244634867/10000000000 : ℝ)*x 1 + (-924535109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378158061/10000000000 : ℝ)^4595 ≤ (45018554643971/100000000000000 : ℝ)^3571 := by
    have hnat : (5378158061 : ℕ)^4595*100000000000000^3571 ≤ 45018554643971^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378158061 10000000000 45018554643971 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244634867/10000000000 : ℝ)^4595 ≤ (43585534063697/100000000000000 : ℝ)^3571 := by
    have hnat : (5244634867 : ℕ)^4595*100000000000000^3571 ≤ 43585534063697^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244634867 10000000000 43585534063697 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (924535109/5000000000 : ℝ)^4595 ≤ (11395911269487/100000000000000 : ℝ)^3571 := by
    have hnat : (924535109 : ℕ)^4595*100000000000000^3571 ≤ 11395911269487^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924535109 5000000000 11395911269487 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378158061/10000000000 : ℝ), (5244634867/10000000000 : ℝ), (-924535109/5000000000 : ℝ)] ![(45018554643971/100000000000000 : ℝ), (43585534063697/100000000000000 : ℝ), (11395911269487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378158061/10000000000 : ℝ)|^4595 ≤ (45018554643971/100000000000000 : ℝ)^3571
        have hw : |(5378158061/10000000000 : ℝ)|=(5378158061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244634867/10000000000 : ℝ)|^4595 ≤ (43585534063697/100000000000000 : ℝ)^3571
        have hw : |(5244634867/10000000000 : ℝ)|=(5244634867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-924535109/5000000000 : ℝ)|^4595 ≤ (11395911269487/100000000000000 : ℝ)^3571
        have hw : |(-924535109/5000000000 : ℝ)|=(924535109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_box_7 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4048759547/10000000000 : ℝ)*x 0 + (872303077/2000000000 : ℝ)*x 1 + (2180757883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4048759547/10000000000 : ℝ)^4595 ≤ (15620316765929/50000000000000 : ℝ)^3571 := by
    have hnat : (4048759547 : ℕ)^4595*50000000000000^3571 ≤ 15620316765929^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4048759547 10000000000 15620316765929 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (872303077/2000000000 : ℝ)^4595 ≤ (8594920322661/25000000000000 : ℝ)^3571 := by
    have hnat : (872303077 : ℕ)^4595*25000000000000^3571 ≤ 8594920322661^3571*2000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872303077 2000000000 8594920322661 25000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2180757883/5000000000 : ℝ)^4595 ≤ (34379685155071/100000000000000 : ℝ)^3571 := by
    have hnat : (2180757883 : ℕ)^4595*100000000000000^3571 ≤ 34379685155071^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180757883 5000000000 34379685155071 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4048759547/10000000000 : ℝ), (872303077/2000000000 : ℝ), (2180757883/5000000000 : ℝ)] ![(15620316765929/50000000000000 : ℝ), (8594920322661/25000000000000 : ℝ), (34379685155071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4048759547/10000000000 : ℝ)|^4595 ≤ (15620316765929/50000000000000 : ℝ)^3571
        have hw : |(4048759547/10000000000 : ℝ)|=(4048759547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(872303077/2000000000 : ℝ)|^4595 ≤ (8594920322661/25000000000000 : ℝ)^3571
        have hw : |(872303077/2000000000 : ℝ)|=(872303077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2180757883/5000000000 : ℝ)|^4595 ≤ (34379685155071/100000000000000 : ℝ)^3571
        have hw : |(2180757883/5000000000 : ℝ)|=(2180757883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_box_8 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1938447689/10000000000 : ℝ)*x 0 + (642025961/1250000000 : ℝ)*x 1 + (541918397/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1938447689/10000000000 : ℝ)^4595 ≤ (37842378363/312500000000 : ℝ)^3571 := by
    have hnat : (1938447689 : ℕ)^4595*312500000000^3571 ≤ 37842378363^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1938447689 10000000000 37842378363 312500000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (642025961/1250000000 : ℝ)^4595 ≤ (21214757094117/50000000000000 : ℝ)^3571 := by
    have hnat : (642025961 : ℕ)^4595*50000000000000^3571 ≤ 21214757094117^3571*1250000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642025961 1250000000 21214757094117 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541918397/1000000000 : ℝ)^4595 ≤ (22730462359927/50000000000000 : ℝ)^3571 := by
    have hnat : (541918397 : ℕ)^4595*50000000000000^3571 ≤ 22730462359927^3571*1000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541918397 1000000000 22730462359927 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1938447689/10000000000 : ℝ), (642025961/1250000000 : ℝ), (541918397/1000000000 : ℝ)] ![(37842378363/312500000000 : ℝ), (21214757094117/50000000000000 : ℝ), (22730462359927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1938447689/10000000000 : ℝ)|^4595 ≤ (37842378363/312500000000 : ℝ)^3571
        have hw : |(-1938447689/10000000000 : ℝ)|=(1938447689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(642025961/1250000000 : ℝ)|^4595 ≤ (21214757094117/50000000000000 : ℝ)^3571
        have hw : |(642025961/1250000000 : ℝ)|=(642025961/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541918397/1000000000 : ℝ)|^4595 ≤ (22730462359927/50000000000000 : ℝ)^3571
        have hw : |(541918397/1000000000 : ℝ)|=(541918397/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_box_9 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256970067/10000000000 : ℝ)*x 0 + (-888116953/5000000000 : ℝ)*x 1 + (5419184053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256970067/10000000000 : ℝ)^4595 ≤ (21858742932083/50000000000000 : ℝ)^3571 := by
    have hnat : (5256970067 : ℕ)^4595*50000000000000^3571 ≤ 21858742932083^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256970067 10000000000 21858742932083 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (888116953/5000000000 : ℝ)^4595 ≤ (2705397125211/25000000000000 : ℝ)^3571 := by
    have hnat : (888116953 : ℕ)^4595*25000000000000^3571 ≤ 2705397125211^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888116953 5000000000 2705397125211 25000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419184053/10000000000 : ℝ)^4595 ≤ (45460925615793/100000000000000 : ℝ)^3571 := by
    have hnat : (5419184053 : ℕ)^4595*100000000000000^3571 ≤ 45460925615793^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419184053 10000000000 45460925615793 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256970067/10000000000 : ℝ), (-888116953/5000000000 : ℝ), (5419184053/10000000000 : ℝ)] ![(21858742932083/50000000000000 : ℝ), (2705397125211/25000000000000 : ℝ), (45460925615793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256970067/10000000000 : ℝ)|^4595 ≤ (21858742932083/50000000000000 : ℝ)^3571
        have hw : |(5256970067/10000000000 : ℝ)|=(5256970067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-888116953/5000000000 : ℝ)|^4595 ≤ (2705397125211/25000000000000 : ℝ)^3571
        have hw : |(-888116953/5000000000 : ℝ)|=(888116953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419184053/10000000000 : ℝ)|^4595 ≤ (45460925615793/100000000000000 : ℝ)^3571
        have hw : |(5419184053/10000000000 : ℝ)|=(5419184053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_box_10 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628485041/5000000000 : ℝ)*x 0 + (1354796003/2500000000 : ℝ)*x 1 + (-888116971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628485041/5000000000 : ℝ)^4595 ≤ (43717486024677/100000000000000 : ℝ)^3571 := by
    have hnat : (2628485041 : ℕ)^4595*100000000000000^3571 ≤ 43717486024677^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628485041 5000000000 43717486024677 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354796003/2500000000 : ℝ)^4595 ≤ (45460925173221/100000000000000 : ℝ)^3571 := by
    have hnat : (1354796003 : ℕ)^4595*100000000000000^3571 ≤ 45460925173221^3571*2500000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354796003 2500000000 45460925173221 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (888116971/5000000000 : ℝ)^4595 ≤ (2164317756613/20000000000000 : ℝ)^3571 := by
    have hnat : (888116971 : ℕ)^4595*20000000000000^3571 ≤ 2164317756613^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888116971 5000000000 2164317756613 20000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628485041/5000000000 : ℝ), (1354796003/2500000000 : ℝ), (-888116971/5000000000 : ℝ)] ![(43717486024677/100000000000000 : ℝ), (45460925173221/100000000000000 : ℝ), (2164317756613/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628485041/5000000000 : ℝ)|^4595 ≤ (43717486024677/100000000000000 : ℝ)^3571
        have hw : |(2628485041/5000000000 : ℝ)|=(2628485041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354796003/2500000000 : ℝ)|^4595 ≤ (45460925173221/100000000000000 : ℝ)^3571
        have hw : |(1354796003/2500000000 : ℝ)|=(1354796003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-888116971/5000000000 : ℝ)|^4595 ≤ (2164317756613/20000000000000 : ℝ)^3571
        have hw : |(-888116971/5000000000 : ℝ)|=(888116971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_box_11 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2253342571/5000000000 : ℝ)*x 0 + (103302321/250000000 : ℝ)*x 1 + (4132092619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2253342571/5000000000 : ℝ)^4595 ≤ (35859088633981/100000000000000 : ℝ)^3571 := by
    have hnat : (2253342571 : ℕ)^4595*100000000000000^3571 ≤ 35859088633981^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253342571 5000000000 35859088633981 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103302321/250000000 : ℝ)^4595 ≤ (8017614193983/25000000000000 : ℝ)^3571 := by
    have hnat : (103302321 : ℕ)^4595*25000000000000^3571 ≤ 8017614193983^3571*250000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103302321 250000000 8017614193983 25000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4132092619/10000000000 : ℝ)^4595 ≤ (32070454568827/100000000000000 : ℝ)^3571 := by
    have hnat : (4132092619 : ℕ)^4595*100000000000000^3571 ≤ 32070454568827^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4132092619 10000000000 32070454568827 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2253342571/5000000000 : ℝ), (103302321/250000000 : ℝ), (4132092619/10000000000 : ℝ)] ![(35859088633981/100000000000000 : ℝ), (8017614193983/25000000000000 : ℝ), (32070454568827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2253342571/5000000000 : ℝ)|^4595 ≤ (35859088633981/100000000000000 : ℝ)^3571
        have hw : |(2253342571/5000000000 : ℝ)|=(2253342571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(103302321/250000000 : ℝ)|^4595 ≤ (8017614193983/25000000000000 : ℝ)^3571
        have hw : |(103302321/250000000 : ℝ)|=(103302321/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4132092619/10000000000 : ℝ)|^4595 ≤ (32070454568827/100000000000000 : ℝ)^3571
        have hw : |(4132092619/10000000000 : ℝ)|=(4132092619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_box_12 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-848070453/5000000000 : ℝ)*x 0 + (2751952769/5000000000 : ℝ)*x 1 + (5229588923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (848070453/5000000000 : ℝ)^4595 ≤ (10197805807699/100000000000000 : ℝ)^3571 := by
    have hnat : (848070453 : ℕ)^4595*100000000000000^3571 ≤ 10197805807699^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848070453 5000000000 10197805807699 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2751952769/5000000000 : ℝ)^4595 ≤ (1855099550871/4000000000000 : ℝ)^3571 := by
    have hnat : (2751952769 : ℕ)^4595*4000000000000^3571 ≤ 1855099550871^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751952769 5000000000 1855099550871 4000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229588923/10000000000 : ℝ)^4595 ≤ (43424705410187/100000000000000 : ℝ)^3571 := by
    have hnat : (5229588923 : ℕ)^4595*100000000000000^3571 ≤ 43424705410187^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229588923 10000000000 43424705410187 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-848070453/5000000000 : ℝ), (2751952769/5000000000 : ℝ), (5229588923/10000000000 : ℝ)] ![(10197805807699/100000000000000 : ℝ), (1855099550871/4000000000000 : ℝ), (43424705410187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-848070453/5000000000 : ℝ)|^4595 ≤ (10197805807699/100000000000000 : ℝ)^3571
        have hw : |(-848070453/5000000000 : ℝ)|=(848070453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2751952769/5000000000 : ℝ)|^4595 ≤ (1855099550871/4000000000000 : ℝ)^3571
        have hw : |(2751952769/5000000000 : ℝ)|=(2751952769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229588923/10000000000 : ℝ)|^4595 ≤ (43424705410187/100000000000000 : ℝ)^3571
        have hw : |(5229588923/10000000000 : ℝ)|=(5229588923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_box_13 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5388604213/10000000000 : ℝ)*x 0 + (-1855156467/10000000000 : ℝ)*x 1 + (326849271/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5388604213/10000000000 : ℝ)^4595 ≤ (1410346901603/3125000000000 : ℝ)^3571 := by
    have hnat : (5388604213 : ℕ)^4595*3125000000000^3571 ≤ 1410346901603^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388604213 10000000000 1410346901603 3125000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1855156467/10000000000 : ℝ)^4595 ≤ (5722099999809/50000000000000 : ℝ)^3571 := by
    have hnat : (1855156467 : ℕ)^4595*50000000000000^3571 ≤ 5722099999809^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1855156467 10000000000 5722099999809 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326849271/625000000 : ℝ)^4595 ≤ (4342469913823/10000000000000 : ℝ)^3571 := by
    have hnat : (326849271 : ℕ)^4595*10000000000000^3571 ≤ 4342469913823^3571*625000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326849271 625000000 4342469913823 10000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5388604213/10000000000 : ℝ), (-1855156467/10000000000 : ℝ), (326849271/625000000 : ℝ)] ![(1410346901603/3125000000000 : ℝ), (5722099999809/50000000000000 : ℝ), (4342469913823/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5388604213/10000000000 : ℝ)|^4595 ≤ (1410346901603/3125000000000 : ℝ)^3571
        have hw : |(5388604213/10000000000 : ℝ)|=(5388604213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1855156467/10000000000 : ℝ)|^4595 ≤ (5722099999809/50000000000000 : ℝ)^3571
        have hw : |(-1855156467/10000000000 : ℝ)|=(1855156467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326849271/625000000 : ℝ)|^4595 ≤ (4342469913823/10000000000000 : ℝ)^3571
        have hw : |(326849271/625000000 : ℝ)|=(326849271/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_box_14 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538860387/1000000000 : ℝ)*x 0 + (5229588681/10000000000 : ℝ)*x 1 + (-1855156469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538860387/1000000000 : ℝ)^4595 ≤ (45131097154807/100000000000000 : ℝ)^3571 := by
    have hnat : (538860387 : ℕ)^4595*100000000000000^3571 ≤ 45131097154807^3571*1000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538860387 1000000000 45131097154807 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5229588681/10000000000 : ℝ)^4595 ≤ (21712351412237/50000000000000 : ℝ)^3571 := by
    have hnat : (5229588681 : ℕ)^4595*50000000000000^3571 ≤ 21712351412237^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229588681 10000000000 21712351412237 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1855156469/10000000000 : ℝ)^4595 ≤ (5722100007747/50000000000000 : ℝ)^3571 := by
    have hnat : (1855156469 : ℕ)^4595*50000000000000^3571 ≤ 5722100007747^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1855156469 10000000000 5722100007747 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538860387/1000000000 : ℝ), (5229588681/10000000000 : ℝ), (-1855156469/10000000000 : ℝ)] ![(45131097154807/100000000000000 : ℝ), (21712351412237/50000000000000 : ℝ), (5722100007747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538860387/1000000000 : ℝ)|^4595 ≤ (45131097154807/100000000000000 : ℝ)^3571
        have hw : |(538860387/1000000000 : ℝ)|=(538860387/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5229588681/10000000000 : ℝ)|^4595 ≤ (21712351412237/50000000000000 : ℝ)^3571
        have hw : |(5229588681/10000000000 : ℝ)|=(5229588681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1855156469/10000000000 : ℝ)|^4595 ≤ (5722100007747/50000000000000 : ℝ)^3571
        have hw : |(-1855156469/10000000000 : ℝ)|=(1855156469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1549_box_15 (p : ℝ) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2004162111/5000000000 : ℝ)*x 0 + (4381265039/10000000000 : ℝ)*x 1 + (2190632687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2004162111/5000000000 : ℝ)^4595 ≤ (15419869263577/50000000000000 : ℝ)^3571 := by
    have hnat : (2004162111 : ℕ)^4595*50000000000000^3571 ≤ 15419869263577^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004162111 5000000000 15419869263577 50000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4381265039/10000000000 : ℝ)^4595 ≤ (8645032257159/25000000000000 : ℝ)^3571 := by
    have hnat : (4381265039 : ℕ)^4595*25000000000000^3571 ≤ 8645032257159^3571*10000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4381265039 10000000000 8645032257159 25000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2190632687/5000000000 : ℝ)^4595 ≤ (34580132430897/100000000000000 : ℝ)^3571 := by
    have hnat : (2190632687 : ℕ)^4595*100000000000000^3571 ≤ 34580132430897^3571*5000000000^4595 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190632687 5000000000 34580132430897 100000000000000 4595 3571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4595/1024 : ℝ)) 4595 3571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2004162111/5000000000 : ℝ), (4381265039/10000000000 : ℝ), (2190632687/5000000000 : ℝ)] ![(15419869263577/50000000000000 : ℝ), (8645032257159/25000000000000 : ℝ), (34580132430897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2004162111/5000000000 : ℝ)|^4595 ≤ (15419869263577/50000000000000 : ℝ)^3571
        have hw : |(2004162111/5000000000 : ℝ)|=(2004162111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4381265039/10000000000 : ℝ)|^4595 ≤ (8645032257159/25000000000000 : ℝ)^3571
        have hw : |(4381265039/10000000000 : ℝ)|=(4381265039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2190632687/5000000000 : ℝ)|^4595 ≤ (34580132430897/100000000000000 : ℝ)^3571
        have hw : |(2190632687/5000000000 : ℝ)|=(2190632687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1549_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83170743/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11051/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63793/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58803/100000 : ℝ) ∧ (20177/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (21559/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11051/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11051/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11051/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11051/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11051/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11051/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11051/100000 : ℝ) ^ (4593/1024 : ℝ) ≤ (320036708116811/6250000000000000000 : ℝ) := by
    have hpowers : (11051/100000 : ℝ)^4593 ≤ (320036708116811/6250000000000000000 : ℝ)^1024 := by
      have hnat : (11051 : ℕ)^4593*6250000000000000000^1024 ≤ 320036708116811^1024*100000^4593 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11051 100000 320036708116811 6250000000000000000 4593 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11051/100000 : ℝ)) (X := (320036708116811/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4593/1024 : ℝ) ≤ (23252356809962847/100000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4593 ≤ (23252356809962847/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4593*100000000000000000000^1024 ≤ 23252356809962847^1024*20000^4593 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 23252356809962847 100000000000000000000 4593 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (23252356809962847/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125320036708116811/3125000000000000000 : ℝ) ≤ (400009132632793/400000000000000 : ℝ) ^ (4593/1024 : ℝ) := by
    have hpowers : (3125320036708116811/3125000000000000000 : ℝ)^1024 ≤ (400009132632793/400000000000000 : ℝ)^4593 := by
      have hnat : (3125320036708116811 : ℕ)^1024*400000000000000^4593 ≤ 400009132632793^4593*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125320036708116811 3125000000000000000 400009132632793 400000000000000 1024 4593 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400009132632793/400000000000000 : ℝ)) (X := (3125320036708116811/3125000000000000000 : ℝ)) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100028372944139831823/100000000000000000000 : ℝ) ≤ (1250079062411671/1250000000000000 : ℝ) ^ (4593/1024 : ℝ) := by
    have hpowers : (100028372944139831823/100000000000000000000 : ℝ)^1024 ≤ (1250079062411671/1250000000000000 : ℝ)^4593 := by
      have hnat : (100028372944139831823 : ℕ)^1024*1250000000000000^4593 ≤ 1250079062411671^4593*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100028372944139831823 100000000000000000000 1250079062411671 1250000000000000 1024 4593 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250079062411671/1250000000000000 : ℝ)) (X := (100028372944139831823/100000000000000000000 : ℝ)) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023252356809962847/50000000000000000000 : ℝ) ≤ (10001036682766911/10000000000000000 : ℝ) ^ (4593/1024 : ℝ) := by
    have hpowers : (50023252356809962847/50000000000000000000 : ℝ)^1024 ≤ (10001036682766911/10000000000000000 : ℝ)^4593 := by
      have hnat : (50023252356809962847 : ℕ)^1024*10000000000000000^4593 ≤ 10001036682766911^4593*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023252356809962847 50000000000000000000 10001036682766911 10000000000000000 1024 4593 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001036682766911/10000000000000000 : ℝ)) (X := (50023252356809962847/50000000000000000000 : ℝ)) (by norm_num) 4593 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(320036708116811/6250000000000000000 : ℝ) ≤ ((5541509886151607083/5542500000000000000 : ℝ)+2*(404183473543/443400000000000 : ℝ)*(11051/100000 : ℝ))^(4593/1024 : ℝ) := by
    rw [show (5541509886151607083/5542500000000000000 : ℝ)+2*(404183473543/443400000000000 : ℝ)*(11051/100000 : ℝ)=(400009132632793/400000000000000 : ℝ) by norm_num, show 1+2*(320036708116811/6250000000000000000 : ℝ)=(3125320036708116811/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23252356809962847/100000000000000000000 : ℝ)+(320036708116811/6250000000000000000 : ℝ) ≤ ((5541509886151607083/5542500000000000000 : ℝ)+(404183473543/443400000000000 : ℝ)*((3097/20000 : ℝ)+(11051/100000 : ℝ)))^(4593/1024 : ℝ) := by
    rw [show (5541509886151607083/5542500000000000000 : ℝ)+(404183473543/443400000000000 : ℝ)*((3097/20000 : ℝ)+(11051/100000 : ℝ))=(1250079062411671/1250000000000000 : ℝ) by norm_num, show 1+(23252356809962847/100000000000000000000 : ℝ)+(320036708116811/6250000000000000000 : ℝ)=(100028372944139831823/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23252356809962847/100000000000000000000 : ℝ) ≤ ((5541509886151607083/5542500000000000000 : ℝ)+2*(404183473543/443400000000000 : ℝ)*(3097/20000 : ℝ))^(4593/1024 : ℝ) := by
    rw [show (5541509886151607083/5542500000000000000 : ℝ)+2*(404183473543/443400000000000 : ℝ)*(3097/20000 : ℝ)=(10001036682766911/10000000000000000 : ℝ) by norm_num, show 1+2*(23252356809962847/100000000000000000000 : ℝ)=(50023252356809962847/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5541509886151607083/5542500000000000000 : ℝ)*(X 1 0+X 2 0)+(404183473543/443400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4593/1024 : ℝ)) (lo := (11051/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (5541509886151607083/5542500000000000000 : ℝ)) (alpha := (404183473543/443400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5541509886151607083/5542500000000000000 : ℝ)*(X 0 1+X 2 1)+(404183473543/443400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4593/1024 : ℝ)) (lo := (11051/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (5541509886151607083/5542500000000000000 : ℝ)) (alpha := (404183473543/443400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5541509886151607083/5542500000000000000 : ℝ)*(X 0 2+X 1 2)+(404183473543/443400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4593/1024 : ℝ)) (lo := (11051/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (5541509886151607083/5542500000000000000 : ℝ)) (alpha := (404183473543/443400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-40186727/250000000 : ℝ)*X 0 0+(107976893/200000000 : ℝ)*X 0 1+(5398845309/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((16472171/31250000 : ℝ)*X 1 0+(-1784930563/10000000000 : ℝ)*X 1 1+(5398845231/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1317773649/2500000000 : ℝ)*X 2 0+(5398845567/10000000000 : ℝ)*X 2 1+(-178493027/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((445434013/1000000000 : ℝ)*X 0 0+(4158855121/10000000000 : ℝ)*X 0 1+(831771/2000000 : ℝ)*X 0 2+(445434013/1000000000 : ℝ)*X 1 0+(4158855121/10000000000 : ℝ)*X 1 1+(831771/2000000 : ℝ)*X 1 2+(445434013/1000000000 : ℝ)*X 2 0+(4158855121/10000000000 : ℝ)*X 2 1+(831771/2000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2027359381/10000000000 : ℝ)*X 0 0+(5244635703/10000000000 : ℝ)*X 0 1+(5244635203/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5378155991/10000000000 : ℝ)*X 1 0+(-924535733/5000000000 : ℝ)*X 1 1+(5244636027/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5378158061/10000000000 : ℝ)*X 2 0+(5244634867/10000000000 : ℝ)*X 2 1+(-924535109/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4048759547/10000000000 : ℝ)*X 0 0+(872303077/2000000000 : ℝ)*X 0 1+(2180757883/5000000000 : ℝ)*X 0 2+(4048759547/10000000000 : ℝ)*X 1 0+(872303077/2000000000 : ℝ)*X 1 1+(2180757883/5000000000 : ℝ)*X 1 2+(4048759547/10000000000 : ℝ)*X 2 0+(872303077/2000000000 : ℝ)*X 2 1+(2180757883/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1938447689/10000000000 : ℝ)*X 0 0+(642025961/1250000000 : ℝ)*X 0 1+(541918397/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5256970067/10000000000 : ℝ)*X 1 0+(-888116953/5000000000 : ℝ)*X 1 1+(5419184053/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2628485041/5000000000 : ℝ)*X 2 0+(1354796003/2500000000 : ℝ)*X 2 1+(-888116971/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2253342571/5000000000 : ℝ)*X 0 0+(103302321/250000000 : ℝ)*X 0 1+(4132092619/10000000000 : ℝ)*X 0 2+(2253342571/5000000000 : ℝ)*X 1 0+(103302321/250000000 : ℝ)*X 1 1+(4132092619/10000000000 : ℝ)*X 1 2+(2253342571/5000000000 : ℝ)*X 2 0+(103302321/250000000 : ℝ)*X 2 1+(4132092619/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-848070453/5000000000 : ℝ)*X 0 0+(2751952769/5000000000 : ℝ)*X 0 1+(5229588923/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5388604213/10000000000 : ℝ)*X 1 0+(-1855156467/10000000000 : ℝ)*X 1 1+(326849271/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((538860387/1000000000 : ℝ)*X 2 0+(5229588681/10000000000 : ℝ)*X 2 1+(-1855156469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2004162111/5000000000 : ℝ)*X 0 0+(4381265039/10000000000 : ℝ)*X 0 1+(2190632687/5000000000 : ℝ)*X 0 2+(2004162111/5000000000 : ℝ)*X 1 0+(4381265039/10000000000 : ℝ)*X 1 1+(2190632687/5000000000 : ℝ)*X 1 2+(2004162111/5000000000 : ℝ)*X 2 0+(4381265039/10000000000 : ℝ)*X 2 1+(2190632687/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1549_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63793/100000 : ℝ) ≤ (-14731693633792940794596161080107/23093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (187447151/50000000000000 : ℝ)*(upper0) + (689254911/100000000000000 : ℝ)*(lower2) + (31349639/50000000000000 : ℝ)*(upper5) + (569370728935107/25000000000000 : ℝ)*(major0) + (569370728935107/25000000000000 : ℝ)*(major1) + (569370728935107/25000000000000 : ℝ)*(major2) + (1926871709/25000000000000 : ℝ)*(sp3) + (320705926826881/10000000000000 : ℝ)*(sp4) + (100218686827289/3125000000000 : ℝ)*(sp5) + (3206973654131693/100000000000000 : ℝ)*(sp6) + (54766135610747/4000000000000 : ℝ)*(sp7) + (9073768721/100000000000000 : ℝ)*(sp8) + (17590891071/25000000000000 : ℝ)*(sp13) + (47343952919/50000000000000 : ℝ)*(sp14) + (136916109775551/10000000000000 : ℝ)*(f.failure) + (3207068342037531/100000000000000 : ℝ)*(f.sum) + (1673163545209/923750000000000000000000000 : ℝ)*base66 + (751875191486162373/46187500000000000000000000000000 : ℝ)*base68 + (623447537986099873/46187500000000000000000000000000 : ℝ)*base70 + (667660305972662373/46187500000000000000000000000000 : ℝ)*base72 + (10255038077591/3695000000000000000000000000 : ℝ)*base74 + (798293844266099873/46187500000000000000000000000000 : ℝ)*base76 + (265032925406849873/46187500000000000000000000000000 : ℝ)*base78 + (468039564855474873/46187500000000000000000000000000 : ℝ)*base80 + (928840577787/461875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (95607/500000000000000000000 : ℝ)*base90 + (95607/500000000000000000000 : ℝ)*base92 + (95607/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (58803/100000 : ℝ) ≤ (10864227547702690138727957853587/18475000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5550541/25000000000000 : ℝ)*(upper2) + (37419913/50000000000000 : ℝ)*(upper3) + (78178519/100000000000000 : ℝ)*(upper4) + (95825077/100000000000000 : ℝ)*(upper5) + (471254621080489/20000000000000 : ℝ)*(major0) + (471254621080489/20000000000000 : ℝ)*(major1) + (471254621080489/20000000000000 : ℝ)*(major2) + (3276410862892657/100000000000000 : ℝ)*(sp0) + (3276416783239963/100000000000000 : ℝ)*(sp1) + (204775485011903/6250000000000 : ℝ)*(sp2) + (22133244181739/1562500000000 : ℝ)*(sp3) + (63207493/50000000000000 : ℝ)*(sp5) + (9149464501/100000000000000 : ℝ)*(sp6) + (604676229/10000000000000 : ℝ)*(sp12) + (22133244181739/1562500000000 : ℝ)*(f.failure) + (819104227413737/25000000000000 : ℝ)*(f.sum) + (41099978547593/4434000000000000000000000000 : ℝ)*base66 + (133356624337997029/36950000000000000000000000000000 : ℝ)*base67 + (291893341138847029/36950000000000000000000000000000 : ℝ)*base69 + (1040298089568002971/36950000000000000000000000000000 : ℝ)*base72 + (8543156147687/4434000000000000000000000000 : ℝ)*base74 + (66017564495552971/36950000000000000000000000000000 : ℝ)*base76 + (171963300884852971/36950000000000000000000000000000 : ℝ)*base78 + (85187968077352971/36950000000000000000000000000000 : ℝ)*base80 + (10885303199779/4434000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (494173/78125000000000000000 : ℝ)*base90 + (494173/78125000000000000000 : ℝ)*base92 + (494173/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (20177/25000 : ℝ) ≤ (149111904593000674434427219/184750000000000000000000000 : ℝ) := by norm_num
    linear_combination (24263441/100000000000000 : ℝ)*(upper0) + (23921201/50000000000000 : ℝ)*(upper1) + (793913/4000000000000 : ℝ)*(upper3) + (60671/25000000000000 : ℝ)*(upper4) + (254553899204869/10000000000000 : ℝ)*(major0) + (254553899204869/10000000000000 : ℝ)*(major1) + (254553899204869/10000000000000 : ℝ)*(major2) + (5637067843/20000000000000 : ℝ)*(sp1) + (24604527727/100000000000000 : ℝ)*(sp2) + (4420205847/100000000000000 : ℝ)*(sp3) + (1766932730710387/50000000000000 : ℝ)*(sp8) + (88345931902039/2500000000000 : ℝ)*(sp9) + (3533840856893047/100000000000000 : ℝ)*(sp10) + (1530304736734527/100000000000000 : ℝ)*(sp11) + (1530309156940373/100000000000000 : ℝ)*(f.failure) + (1766932730710387/50000000000000 : ℝ)*(f.sum) + (11185731859919/2217000000000000000000000000 : ℝ)*base66 + (23846309746416791/18475000000000000000000000000000 : ℝ)*base68 + (82581804052433209/18475000000000000000000000000000 : ℝ)*base69 + (38365028629291791/18475000000000000000000000000000 : ℝ)*base72 + (10910816482513/2217000000000000000000000000 : ℝ)*base73 + (128284521810941791/18475000000000000000000000000000 : ℝ)*base76 + (18749069935358209/18475000000000000000000000000000 : ℝ)*base77 + (151348600181608209/18475000000000000000000000000000 : ℝ)*base79 + (3062600494483/1108500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (70892861/5000000000000000000000 : ℝ)*base90 + (70892861/5000000000000000000000 : ℝ)*base92 + (70892861/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-21559/25000 : ℝ) ≤ (-9957308393693467585433421238627/11546875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3836921/2000000000000 : ℝ)*(upper3) + (482681/625000000000 : ℝ)*(lower4) + (8616203/4000000000000 : ℝ)*(upper5) + (161594597043061/6250000000000 : ℝ)*(major0) + (161594597043061/6250000000000 : ℝ)*(major1) + (161594597043061/6250000000000 : ℝ)*(major2) + (7060629369/100000000000000 : ℝ)*(sp4) + (276757720457/100000000000000 : ℝ)*(sp5) + (14440796883/6250000000000 : ℝ)*(sp6) + (63580676771/100000000000000 : ℝ)*(sp7) + (1822711930842921/50000000000000 : ℝ)*(sp12) + (1822577082297377/50000000000000 : ℝ)*(sp13) + (3645199869565083/100000000000000 : ℝ)*(sp14) + (388569300091263/25000000000000 : ℝ)*(sp15) + (48573149407557/3125000000000 : ℝ)*(f.failure) + (3645430922315211/100000000000000 : ℝ)*(f.sum) + (578873008903/86601562500000000000000000 : ℝ)*base65 + (21269771712464229/11546875000000000000000000000000 : ℝ)*base68 + (10103328126764237/1443359375000000000000000000000 : ℝ)*base69 + (80749345671035771/11546875000000000000000000000000 : ℝ)*base71 + (2095057061429/11085000000000000000000000000 : ℝ)*base73 + (32099050922760073/5773437500000000000000000000000 : ℝ)*base75 + (2367264862312153/360839843750000000000000000000 : ℝ)*base77 + (26194996304035771/11546875000000000000000000000000 : ℝ)*base79 + (1188723654271/11085000000000000000000000000 : ℝ)*base82 + (504851/156250000000000000000 : ℝ)*base89 + (504851/156250000000000000000 : ℝ)*base91 + (504851/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1549_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83170743/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11051/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63793/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58803/100000 : ℝ) else (20177/25000 : ℝ) ≤ X j i ∧ X j i ≤ (21559/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1549_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1549_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83170743/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11051/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63793/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58803/100000 : ℝ) else (20177/25000 : ℝ) ≤ X j i ∧ X j i ≤ (21559/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1549_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4593/1024 : ℝ) ≤ p) (hpb : p ≤ (4595/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83170743/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11051/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63793/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58803/100000 : ℝ) else (20177/25000 : ℝ) ≤ X j i ∧ X j i ≤ (21559/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1549_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
