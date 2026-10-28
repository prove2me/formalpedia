-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1100_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:00:27.723194+00:00
-- url     : https://prove2.me/submissions/4b23986f-d516-402c-b8a8-4ddc887760cc

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
theorem support_rectangle_w1100_s9_0 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344884063/10000000000 : ℝ)*x 0 + (5265085919/10000000000 : ℝ)*x 1 + (-1126199489/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344884063/10000000000 : ℝ)^8293 ≤ (21761445293481/50000000000000 : ℝ)^6245 := by
    have hnat : (5344884063 : ℕ)^8293*50000000000000^6245 ≤ 21761445293481^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344884063 10000000000 21761445293481 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265085919/10000000000 : ℝ)^8293 ≤ (21331063996329/50000000000000 : ℝ)^6245 := by
    have hnat : (5265085919 : ℕ)^8293*50000000000000^6245 ≤ 21331063996329^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265085919 10000000000 21331063996329 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126199489/5000000000 : ℝ)^8293 ≤ (13814981401627/100000000000000 : ℝ)^6245 := by
    have hnat : (1126199489 : ℕ)^8293*100000000000000^6245 ≤ 13814981401627^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126199489 5000000000 13814981401627 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344884063/10000000000 : ℝ), (5265085919/10000000000 : ℝ), (-1126199489/5000000000 : ℝ)] ![(21761445293481/50000000000000 : ℝ), (21331063996329/50000000000000 : ℝ), (13814981401627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344884063/10000000000 : ℝ)|^8293 ≤ (21761445293481/50000000000000 : ℝ)^6245
        have hw : |(5344884063/10000000000 : ℝ)|=(5344884063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265085919/10000000000 : ℝ)|^8293 ≤ (21331063996329/50000000000000 : ℝ)^6245
        have hw : |(5265085919/10000000000 : ℝ)|=(5265085919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1126199489/5000000000 : ℝ)|^8293 ≤ (13814981401627/100000000000000 : ℝ)^6245
        have hw : |(-1126199489/5000000000 : ℝ)|=(1126199489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s9_1 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4370626317/10000000000 : ℝ)*x 0 + (4245561669/10000000000 : ℝ)*x 1 + (14060609/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370626317/10000000000 : ℝ)^8293 ≤ (33316757178549/100000000000000 : ℝ)^6245 := by
    have hnat : (4370626317 : ℕ)^8293*100000000000000^6245 ≤ 33316757178549^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370626317 10000000000 33316757178549 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4245561669/10000000000 : ℝ)^8293 ≤ (3205673832241/10000000000000 : ℝ)^6245 := by
    have hnat : (4245561669 : ℕ)^8293*10000000000000^6245 ≤ 3205673832241^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245561669 10000000000 3205673832241 10000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14060609/31250000 : ℝ)^8293 ≤ (34626504484789/100000000000000 : ℝ)^6245 := by
    have hnat : (14060609 : ℕ)^8293*100000000000000^6245 ≤ 34626504484789^6245*31250000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14060609 31250000 34626504484789 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370626317/10000000000 : ℝ), (4245561669/10000000000 : ℝ), (14060609/31250000 : ℝ)] ![(33316757178549/100000000000000 : ℝ), (3205673832241/10000000000000 : ℝ), (34626504484789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370626317/10000000000 : ℝ)|^8293 ≤ (33316757178549/100000000000000 : ℝ)^6245
        have hw : |(4370626317/10000000000 : ℝ)|=(4370626317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4245561669/10000000000 : ℝ)|^8293 ≤ (3205673832241/10000000000000 : ℝ)^6245
        have hw : |(4245561669/10000000000 : ℝ)|=(4245561669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(14060609/31250000 : ℝ)|^8293 ≤ (34626504484789/100000000000000 : ℝ)^6245
        have hw : |(14060609/31250000 : ℝ)|=(14060609/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s9_2 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-54678553/250000000 : ℝ)*x 0 + (5265408889/10000000000 : ℝ)*x 1 + (2696704369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54678553/250000000 : ℝ)^8293 ≤ (13286014291061/100000000000000 : ℝ)^6245 := by
    have hnat : (54678553 : ℕ)^8293*100000000000000^6245 ≤ 13286014291061^6245*250000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54678553 250000000 13286014291061 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265408889/10000000000 : ℝ)^8293 ≤ (10666400804211/25000000000000 : ℝ)^6245 := by
    have hnat : (5265408889 : ℕ)^8293*25000000000000^6245 ≤ 10666400804211^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265408889 10000000000 10666400804211 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696704369/5000000000 : ℝ)^8293 ≤ (44048382482983/100000000000000 : ℝ)^6245 := by
    have hnat : (2696704369 : ℕ)^8293*100000000000000^6245 ≤ 44048382482983^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696704369 5000000000 44048382482983 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-54678553/250000000 : ℝ), (5265408889/10000000000 : ℝ), (2696704369/5000000000 : ℝ)] ![(13286014291061/100000000000000 : ℝ), (10666400804211/25000000000000 : ℝ), (44048382482983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-54678553/250000000 : ℝ)|^8293 ≤ (13286014291061/100000000000000 : ℝ)^6245
        have hw : |(-54678553/250000000 : ℝ)|=(54678553/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265408889/10000000000 : ℝ)|^8293 ≤ (10666400804211/25000000000000 : ℝ)^6245
        have hw : |(5265408889/10000000000 : ℝ)|=(5265408889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696704369/5000000000 : ℝ)|^8293 ≤ (44048382482983/100000000000000 : ℝ)^6245
        have hw : |(2696704369/5000000000 : ℝ)|=(2696704369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s9_3 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531239423/1000000000 : ℝ)*x 0 + (-106203779/500000000 : ℝ)*x 1 + (5393409067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531239423/1000000000 : ℝ)^8293 ≤ (43171918593063/100000000000000 : ℝ)^6245 := by
    have hnat : (531239423 : ℕ)^8293*100000000000000^6245 ≤ 43171918593063^6245*1000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531239423 1000000000 43171918593063 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106203779/500000000 : ℝ)^8293 ≤ (12779695346793/100000000000000 : ℝ)^6245 := by
    have hnat : (106203779 : ℕ)^8293*100000000000000^6245 ≤ 12779695346793^6245*500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106203779 500000000 12779695346793 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393409067/10000000000 : ℝ)^8293 ≤ (22024193025561/50000000000000 : ℝ)^6245 := by
    have hnat : (5393409067 : ℕ)^8293*50000000000000^6245 ≤ 22024193025561^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393409067 10000000000 22024193025561 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531239423/1000000000 : ℝ), (-106203779/500000000 : ℝ), (5393409067/10000000000 : ℝ)] ![(43171918593063/100000000000000 : ℝ), (12779695346793/100000000000000 : ℝ), (22024193025561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531239423/1000000000 : ℝ)|^8293 ≤ (43171918593063/100000000000000 : ℝ)^6245
        have hw : |(531239423/1000000000 : ℝ)|=(531239423/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-106203779/500000000 : ℝ)|^8293 ≤ (12779695346793/100000000000000 : ℝ)^6245
        have hw : |(-106203779/500000000 : ℝ)|=(106203779/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393409067/10000000000 : ℝ)|^8293 ≤ (22024193025561/50000000000000 : ℝ)^6245
        have hw : |(5393409067/10000000000 : ℝ)|=(5393409067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s9_4 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328098533/2500000000 : ℝ)*x 0 + (674176221/1250000000 : ℝ)*x 1 + (-2124074761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328098533/2500000000 : ℝ)^8293 ≤ (1726876701419/4000000000000 : ℝ)^6245 := by
    have hnat : (1328098533 : ℕ)^8293*4000000000000^6245 ≤ 1726876701419^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328098533 2500000000 1726876701419 4000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674176221/1250000000 : ℝ)^8293 ≤ (5506049206719/12500000000000 : ℝ)^6245 := by
    have hnat : (674176221 : ℕ)^8293*12500000000000^6245 ≤ 5506049206719^6245*1250000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674176221 1250000000 5506049206719 12500000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124074761/10000000000 : ℝ)^8293 ≤ (319492220081/2500000000000 : ℝ)^6245 := by
    have hnat : (2124074761 : ℕ)^8293*2500000000000^6245 ≤ 319492220081^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124074761 10000000000 319492220081 2500000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328098533/2500000000 : ℝ), (674176221/1250000000 : ℝ), (-2124074761/10000000000 : ℝ)] ![(1726876701419/4000000000000 : ℝ), (5506049206719/12500000000000 : ℝ), (319492220081/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328098533/2500000000 : ℝ)|^8293 ≤ (1726876701419/4000000000000 : ℝ)^6245
        have hw : |(1328098533/2500000000 : ℝ)|=(1328098533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674176221/1250000000 : ℝ)|^8293 ≤ (5506049206719/12500000000000 : ℝ)^6245
        have hw : |(674176221/1250000000 : ℝ)|=(674176221/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2124074761/10000000000 : ℝ)|^8293 ≤ (319492220081/2500000000000 : ℝ)^6245
        have hw : |(-2124074761/10000000000 : ℝ)|=(2124074761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s9_5 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (874127403/2000000000 : ℝ)*x 0 + (281172383/625000000 : ℝ)*x 1 + (4246199831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874127403/2000000000 : ℝ)^8293 ≤ (1041152045991/3125000000000 : ℝ)^6245 := by
    have hnat : (874127403 : ℕ)^8293*3125000000000^6245 ≤ 1041152045991^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874127403 2000000000 1041152045991 3125000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281172383/625000000 : ℝ)^8293 ≤ (6923999457409/20000000000000 : ℝ)^6245 := by
    have hnat : (281172383 : ℕ)^8293*20000000000000^6245 ≤ 6923999457409^6245*625000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281172383 625000000 6923999457409 20000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4246199831/10000000000 : ℝ)^8293 ≤ (8015784304577/25000000000000 : ℝ)^6245 := by
    have hnat : (4246199831 : ℕ)^8293*25000000000000^6245 ≤ 8015784304577^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246199831 10000000000 8015784304577 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874127403/2000000000 : ℝ), (281172383/625000000 : ℝ), (4246199831/10000000000 : ℝ)] ![(1041152045991/3125000000000 : ℝ), (6923999457409/20000000000000 : ℝ), (8015784304577/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874127403/2000000000 : ℝ)|^8293 ≤ (1041152045991/3125000000000 : ℝ)^6245
        have hw : |(874127403/2000000000 : ℝ)|=(874127403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281172383/625000000 : ℝ)|^8293 ≤ (6923999457409/20000000000000 : ℝ)^6245
        have hw : |(281172383/625000000 : ℝ)|=(281172383/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4246199831/10000000000 : ℝ)|^8293 ≤ (8015784304577/25000000000000 : ℝ)^6245
        have hw : |(4246199831/10000000000 : ℝ)|=(4246199831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_s9_6 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-17403029/2500000000 : ℝ)*x 0 + (1141140727/2000000000 : ℝ)*x 1 + (3073203369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17403029/2500000000 : ℝ)^8293 ≤ (68262128553/50000000000000 : ℝ)^6245 := by
    have hnat : (17403029 : ℕ)^8293*50000000000000^6245 ≤ 68262128553^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17403029 2500000000 68262128553 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1141140727/2000000000 : ℝ)^8293 ≤ (23733548860901/50000000000000 : ℝ)^6245 := by
    have hnat : (1141140727 : ℕ)^8293*50000000000000^6245 ≤ 23733548860901^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141140727 2000000000 23733548860901 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3073203369/5000000000 : ℝ)^8293 ≤ (52396378003899/100000000000000 : ℝ)^6245 := by
    have hnat : (3073203369 : ℕ)^8293*100000000000000^6245 ≤ 52396378003899^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3073203369 5000000000 52396378003899 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17403029/2500000000 : ℝ), (1141140727/2000000000 : ℝ), (3073203369/5000000000 : ℝ)] ![(68262128553/50000000000000 : ℝ), (23733548860901/50000000000000 : ℝ), (52396378003899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17403029/2500000000 : ℝ)|^8293 ≤ (68262128553/50000000000000 : ℝ)^6245
        have hw : |(-17403029/2500000000 : ℝ)|=(17403029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1141140727/2000000000 : ℝ)|^8293 ≤ (23733548860901/50000000000000 : ℝ)^6245
        have hw : |(1141140727/2000000000 : ℝ)|=(1141140727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3073203369/5000000000 : ℝ)|^8293 ≤ (52396378003899/100000000000000 : ℝ)^6245
        have hw : |(3073203369/5000000000 : ℝ)|=(3073203369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1100_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5649/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14023/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1753/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5649/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1753/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5649/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1753/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5649/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1753/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5649/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1753/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5649/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1753/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5649/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5649/50000 : ℝ) ^ (2073/512 : ℝ) ≤ (2929517654352307/20000000000000000000 : ℝ) := by
    have hpowers : (5649/50000 : ℝ)^2073 ≤ (2929517654352307/20000000000000000000 : ℝ)^512 := by
      have hnat : (5649 : ℕ)^2073*20000000000000000000^512 ≤ 2929517654352307^512*50000^2073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5649 50000 2929517654352307 20000000000000000000 2073 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5649/50000 : ℝ)) (X := (2929517654352307/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1753/12500 : ℝ) ^ (2073/512 : ℝ) ≤ (3514236352950823/10000000000000000000 : ℝ) := by
    have hpowers : (1753/12500 : ℝ)^2073 ≤ (3514236352950823/10000000000000000000 : ℝ)^512 := by
      have hnat : (1753 : ℕ)^2073*10000000000000000000^512 ≤ 3514236352950823^512*12500^2073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1753 12500 3514236352950823 10000000000000000000 2073 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1753/12500 : ℝ)) (X := (3514236352950823/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002929517654352307/10000000000000000000 : ℝ) ≤ (2000144693451919/2000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (10002929517654352307/10000000000000000000 : ℝ)^512 ≤ (2000144693451919/2000000000000000 : ℝ)^2073 := by
      have hnat : (10002929517654352307 : ℕ)^512*2000000000000000^2073 ≤ 2000144693451919^2073*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002929517654352307 10000000000000000000 2000144693451919 2000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000144693451919/2000000000000000 : ℝ)) (X := (10002929517654352307/10000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009957990360253953/20000000000000000000 : ℝ) ≤ (5000614753444833/5000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (20009957990360253953/20000000000000000000 : ℝ)^512 ≤ (5000614753444833/5000000000000000 : ℝ)^2073 := by
      have hnat : (20009957990360253953 : ℕ)^512*5000000000000000^2073 ≤ 5000614753444833^2073*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009957990360253953 20000000000000000000 5000614753444833 5000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000614753444833/5000000000000000 : ℝ)) (X := (20009957990360253953/20000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003514236352950823/5000000000000000000 : ℝ) ≤ (10001735546519737/10000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (5003514236352950823/5000000000000000000 : ℝ)^512 ≤ (10001735546519737/10000000000000000 : ℝ)^2073 := by
      have hnat : (5003514236352950823 : ℕ)^512*10000000000000000^2073 ≤ 10001735546519737^2073*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003514236352950823 5000000000000000000 10001735546519737 10000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001735546519737/10000000000000000 : ℝ)) (X := (5003514236352950823/5000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2929517654352307/20000000000000000000 : ℝ) ≤ ((13625268850134285827/13630000000000000000 : ℝ)+2*(506039630071/272600000000000 : ℝ)*(5649/50000 : ℝ))^(2073/512 : ℝ) := by
    rw [show (13625268850134285827/13630000000000000000 : ℝ)+2*(506039630071/272600000000000 : ℝ)*(5649/50000 : ℝ)=(2000144693451919/2000000000000000 : ℝ) by norm_num, show 1+2*(2929517654352307/20000000000000000000 : ℝ)=(10002929517654352307/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3514236352950823/10000000000000000000 : ℝ)+(2929517654352307/20000000000000000000 : ℝ) ≤ ((13625268850134285827/13630000000000000000 : ℝ)+(506039630071/272600000000000 : ℝ)*((1753/12500 : ℝ)+(5649/50000 : ℝ)))^(2073/512 : ℝ) := by
    rw [show (13625268850134285827/13630000000000000000 : ℝ)+(506039630071/272600000000000 : ℝ)*((1753/12500 : ℝ)+(5649/50000 : ℝ))=(5000614753444833/5000000000000000 : ℝ) by norm_num, show 1+(3514236352950823/10000000000000000000 : ℝ)+(2929517654352307/20000000000000000000 : ℝ)=(20009957990360253953/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3514236352950823/10000000000000000000 : ℝ) ≤ ((13625268850134285827/13630000000000000000 : ℝ)+2*(506039630071/272600000000000 : ℝ)*(1753/12500 : ℝ))^(2073/512 : ℝ) := by
    rw [show (13625268850134285827/13630000000000000000 : ℝ)+2*(506039630071/272600000000000 : ℝ)*(1753/12500 : ℝ)=(10001735546519737/10000000000000000 : ℝ) by norm_num, show 1+2*(3514236352950823/10000000000000000000 : ℝ)=(5003514236352950823/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13625268850134285827/13630000000000000000 : ℝ)*(X 1 0+X 2 0)+(506039630071/272600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (5649/50000 : ℝ)) (hi := (1753/12500 : ℝ)) (c := (13625268850134285827/13630000000000000000 : ℝ)) (alpha := (506039630071/272600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13625268850134285827/13630000000000000000 : ℝ)*(X 0 1+X 2 1)+(506039630071/272600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (5649/50000 : ℝ)) (hi := (1753/12500 : ℝ)) (c := (13625268850134285827/13630000000000000000 : ℝ)) (alpha := (506039630071/272600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13625268850134285827/13630000000000000000 : ℝ)*(X 0 2+X 1 2)+(506039630071/272600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (5649/50000 : ℝ)) (hi := (1753/12500 : ℝ)) (c := (13625268850134285827/13630000000000000000 : ℝ)) (alpha := (506039630071/272600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5344884063/10000000000 : ℝ)*X 2 0+(5265085919/10000000000 : ℝ)*X 2 1+(-1126199489/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s9_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((4370626317/10000000000 : ℝ)*X 0 0+(4245561669/10000000000 : ℝ)*X 0 1+(14060609/31250000 : ℝ)*X 0 2+(4370626317/10000000000 : ℝ)*X 1 0+(4245561669/10000000000 : ℝ)*X 1 1+(14060609/31250000 : ℝ)*X 1 2+(4370626317/10000000000 : ℝ)*X 2 0+(4245561669/10000000000 : ℝ)*X 2 1+(14060609/31250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s9_1 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-54678553/250000000 : ℝ)*X 0 0+(5265408889/10000000000 : ℝ)*X 0 1+(2696704369/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s9_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((531239423/1000000000 : ℝ)*X 1 0+(-106203779/500000000 : ℝ)*X 1 1+(5393409067/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s9_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((1328098533/2500000000 : ℝ)*X 2 0+(674176221/1250000000 : ℝ)*X 2 1+(-2124074761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s9_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((874127403/2000000000 : ℝ)*X 0 0+(281172383/625000000 : ℝ)*X 0 1+(4246199831/10000000000 : ℝ)*X 0 2+(874127403/2000000000 : ℝ)*X 1 0+(281172383/625000000 : ℝ)*X 1 1+(4246199831/10000000000 : ℝ)*X 1 2+(874127403/2000000000 : ℝ)*X 2 0+(281172383/625000000 : ℝ)*X 2 1+(4246199831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((-17403029/2500000000 : ℝ)*X 0 0+(1141140727/2000000000 : ℝ)*X 0 1+(3073203369/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_s9_6 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1558080313170780925826516067/681500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (162948353/20000000000000 : ℝ)*(lower2) + (6169651/2500000000000 : ℝ)*(lower3) + (744661151/100000000000000 : ℝ)*(lower4) + (205030431/100000000000000 : ℝ)*(lower5) + (5886003680082293/100000000000000 : ℝ)*(major0) + (5886003680082293/100000000000000 : ℝ)*(major1) + (5886003680082293/100000000000000 : ℝ)*(major2) + (22567468609/50000000000000 : ℝ)*(sp0) + (12998102719/100000000000000 : ℝ)*(sp1) + (1953122976377993/25000000000000 : ℝ)*(sp2) + (244140581135307/3125000000000 : ℝ)*(sp3) + (3906226730696303/50000000000000 : ℝ)*(sp4) + (79189913790473/2000000000000 : ℝ)*(sp5) + (1672704463/25000000000000 : ℝ)*(sp6) + (395950868762637/10000000000000 : ℝ)*(f.failure) + (244140581135307/3125000000000 : ℝ)*(f.sum) + (176562262543173/13630000000000000000000000000 : ℝ)*base65 + (1063833854273288689/1363000000000000000000000000000000 : ℝ)*base68 + (8163514999682288689/1363000000000000000000000000000000 : ℝ)*base70 + (17877422964724711311/1363000000000000000000000000000000 : ℝ)*base71 + (80499357056473/13630000000000000000000000000 : ℝ)*base73 + (22814454461469711311/1363000000000000000000000000000000 : ℝ)*base75 + (26788949756946711311/1363000000000000000000000000000000 : ℝ)*base77 + (27858756786940711311/1363000000000000000000000000000000 : ℝ)*base79 + (96357940987803/13630000000000000000000000000 : ℝ)*base81 + (30287/10000000000000000000 : ℝ)*base90 + (30287/10000000000000000000 : ℝ)*base92 + (30287/10000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1100_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14023/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1100_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1100_box_0 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1029421463/5000000000 : ℝ)*x 0 + (2688449797/5000000000 : ℝ)*x 1 + (2688449899/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1029421463/5000000000 : ℝ)^8293 ≤ (2452229945399/20000000000000 : ℝ)^6245 := by
    have hnat : (1029421463 : ℕ)^8293*20000000000000^6245 ≤ 2452229945399^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029421463 5000000000 2452229945399 20000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688449797/5000000000 : ℝ)^8293 ≤ (43869424026051/100000000000000 : ℝ)^6245 := by
    have hnat : (2688449797 : ℕ)^8293*100000000000000^6245 ≤ 43869424026051^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688449797 5000000000 43869424026051 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688449899/5000000000 : ℝ)^8293 ≤ (43869426236291/100000000000000 : ℝ)^6245 := by
    have hnat : (2688449899 : ℕ)^8293*100000000000000^6245 ≤ 43869426236291^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688449899 5000000000 43869426236291 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1029421463/5000000000 : ℝ), (2688449797/5000000000 : ℝ), (2688449899/5000000000 : ℝ)] ![(2452229945399/20000000000000 : ℝ), (43869424026051/100000000000000 : ℝ), (43869426236291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1029421463/5000000000 : ℝ)|^8293 ≤ (2452229945399/20000000000000 : ℝ)^6245
        have hw : |(-1029421463/5000000000 : ℝ)|=(1029421463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688449797/5000000000 : ℝ)|^8293 ≤ (43869424026051/100000000000000 : ℝ)^6245
        have hw : |(2688449797/5000000000 : ℝ)|=(2688449797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688449899/5000000000 : ℝ)|^8293 ≤ (43869426236291/100000000000000 : ℝ)^6245
        have hw : |(2688449899/5000000000 : ℝ)|=(2688449899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_box_1 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295570719/10000000000 : ℝ)*x 0 + (-27112889/125000000 : ℝ)*x 1 + (1344224917/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295570719/10000000000 : ℝ)^8293 ≤ (2149522924003/5000000000000 : ℝ)^6245 := by
    have hnat : (5295570719 : ℕ)^8293*5000000000000^6245 ≤ 2149522924003^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295570719 10000000000 2149522924003 5000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27112889/125000000 : ℝ)^8293 ≤ (16425145849/125000000000 : ℝ)^6245 := by
    have hnat : (27112889 : ℕ)^8293*125000000000^6245 ≤ 16425145849^6245*125000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27112889 125000000 16425145849 125000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344224917/2500000000 : ℝ)^8293 ≤ (8773884965561/20000000000000 : ℝ)^6245 := by
    have hnat : (1344224917 : ℕ)^8293*20000000000000^6245 ≤ 8773884965561^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344224917 2500000000 8773884965561 20000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295570719/10000000000 : ℝ), (-27112889/125000000 : ℝ), (1344224917/2500000000 : ℝ)] ![(2149522924003/5000000000000 : ℝ), (16425145849/125000000000 : ℝ), (8773884965561/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295570719/10000000000 : ℝ)|^8293 ≤ (2149522924003/5000000000000 : ℝ)^6245
        have hw : |(5295570719/10000000000 : ℝ)|=(5295570719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-27112889/125000000 : ℝ)|^8293 ≤ (16425145849/125000000000 : ℝ)^6245
        have hw : |(-27112889/125000000 : ℝ)|=(27112889/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1344224917/2500000000 : ℝ)|^8293 ≤ (8773884965561/20000000000000 : ℝ)^6245
        have hw : |(1344224917/2500000000 : ℝ)|=(1344224917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_box_2 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2647785377/5000000000 : ℝ)*x 0 + (672112469/1250000000 : ℝ)*x 1 + (-27112887/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647785377/5000000000 : ℝ)^8293 ≤ (42990458857377/100000000000000 : ℝ)^6245 := by
    have hnat : (2647785377 : ℕ)^8293*100000000000000^6245 ≤ 42990458857377^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647785377 5000000000 42990458857377 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (672112469/1250000000 : ℝ)^8293 ≤ (2741839108619/6250000000000 : ℝ)^6245 := by
    have hnat : (672112469 : ℕ)^8293*6250000000000^6245 ≤ 2741839108619^6245*1250000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672112469 1250000000 2741839108619 6250000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27112887/125000000 : ℝ)^8293 ≤ (328502884801/2500000000000 : ℝ)^6245 := by
    have hnat : (27112887 : ℕ)^8293*2500000000000^6245 ≤ 328502884801^6245*125000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27112887 125000000 328502884801 2500000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647785377/5000000000 : ℝ), (672112469/1250000000 : ℝ), (-27112887/125000000 : ℝ)] ![(42990458857377/100000000000000 : ℝ), (2741839108619/6250000000000 : ℝ), (328502884801/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647785377/5000000000 : ℝ)|^8293 ≤ (42990458857377/100000000000000 : ℝ)^6245
        have hw : |(2647785377/5000000000 : ℝ)|=(2647785377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(672112469/1250000000 : ℝ)|^8293 ≤ (2741839108619/6250000000000 : ℝ)^6245
        have hw : |(672112469/1250000000 : ℝ)|=(672112469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-27112887/125000000 : ℝ)|^8293 ≤ (328502884801/2500000000000 : ℝ)^6245
        have hw : |(-27112887/125000000 : ℝ)|=(27112887/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_box_3 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4478627979/10000000000 : ℝ)*x 0 + (2159381509/5000000000 : ℝ)*x 1 + (2159381463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4478627979/10000000000 : ℝ)^8293 ≤ (6882887182237/20000000000000 : ℝ)^6245 := by
    have hnat : (4478627979 : ℕ)^8293*20000000000000^6245 ≤ 6882887182237^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478627979 10000000000 6882887182237 20000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2159381509/5000000000 : ℝ)^8293 ≤ (8198195624739/25000000000000 : ℝ)^6245 := by
    have hnat : (2159381509 : ℕ)^8293*25000000000000^6245 ≤ 8198195624739^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159381509 5000000000 8198195624739 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2159381463/5000000000 : ℝ)^8293 ≤ (32792781571303/100000000000000 : ℝ)^6245 := by
    have hnat : (2159381463 : ℕ)^8293*100000000000000^6245 ≤ 32792781571303^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159381463 5000000000 32792781571303 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4478627979/10000000000 : ℝ), (2159381509/5000000000 : ℝ), (2159381463/5000000000 : ℝ)] ![(6882887182237/20000000000000 : ℝ), (8198195624739/25000000000000 : ℝ), (32792781571303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4478627979/10000000000 : ℝ)|^8293 ≤ (6882887182237/20000000000000 : ℝ)^6245
        have hw : |(4478627979/10000000000 : ℝ)|=(4478627979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2159381509/5000000000 : ℝ)|^8293 ≤ (8198195624739/25000000000000 : ℝ)^6245
        have hw : |(2159381509/5000000000 : ℝ)|=(2159381509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2159381463/5000000000 : ℝ)|^8293 ≤ (32792781571303/100000000000000 : ℝ)^6245
        have hw : |(2159381463/5000000000 : ℝ)|=(2159381463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_box_4 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-579205683/2500000000 : ℝ)*x 0 + (2640289977/5000000000 : ℝ)*x 1 + (211223193/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (579205683/2500000000 : ℝ)^8293 ≤ (7171074952277/50000000000000 : ℝ)^6245 := by
    have hnat : (579205683 : ℕ)^8293*50000000000000^6245 ≤ 7171074952277^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579205683 2500000000 7171074952277 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640289977/5000000000 : ℝ)^8293 ≤ (21414462869749/50000000000000 : ℝ)^6245 := by
    have hnat : (2640289977 : ℕ)^8293*50000000000000^6245 ≤ 21414462869749^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640289977 5000000000 21414462869749 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211223193/400000000 : ℝ)^8293 ≤ (42828924350107/100000000000000 : ℝ)^6245 := by
    have hnat : (211223193 : ℕ)^8293*100000000000000^6245 ≤ 42828924350107^6245*400000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211223193 400000000 42828924350107 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-579205683/2500000000 : ℝ), (2640289977/5000000000 : ℝ), (211223193/400000000 : ℝ)] ![(7171074952277/50000000000000 : ℝ), (21414462869749/50000000000000 : ℝ), (42828924350107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-579205683/2500000000 : ℝ)|^8293 ≤ (7171074952277/50000000000000 : ℝ)^6245
        have hw : |(-579205683/2500000000 : ℝ)|=(579205683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640289977/5000000000 : ℝ)|^8293 ≤ (21414462869749/50000000000000 : ℝ)^6245
        have hw : |(2640289977/5000000000 : ℝ)|=(2640289977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(211223193/400000000 : ℝ)|^8293 ≤ (42828924350107/100000000000000 : ℝ)^6245
        have hw : |(211223193/400000000 : ℝ)|=(211223193/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_box_5 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5363685167/10000000000 : ℝ)*x 0 + (-1724057/7812500 : ℝ)*x 1 + (1320144969/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363685167/10000000000 : ℝ)^8293 ≤ (2732894370443/6250000000000 : ℝ)^6245 := by
    have hnat : (5363685167 : ℕ)^8293*6250000000000^6245 ≤ 2732894370443^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363685167 10000000000 2732894370443 6250000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1724057/7812500 : ℝ)^8293 ≤ (13444765162697/100000000000000 : ℝ)^6245 := by
    have hnat : (1724057 : ℕ)^8293*100000000000000^6245 ≤ 13444765162697^6245*7812500^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1724057 7812500 13444765162697 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320144969/2500000000 : ℝ)^8293 ≤ (42828924899401/100000000000000 : ℝ)^6245 := by
    have hnat : (1320144969 : ℕ)^8293*100000000000000^6245 ≤ 42828924899401^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320144969 2500000000 42828924899401 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363685167/10000000000 : ℝ), (-1724057/7812500 : ℝ), (1320144969/2500000000 : ℝ)] ![(2732894370443/6250000000000 : ℝ), (13444765162697/100000000000000 : ℝ), (42828924899401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363685167/10000000000 : ℝ)|^8293 ≤ (2732894370443/6250000000000 : ℝ)^6245
        have hw : |(5363685167/10000000000 : ℝ)|=(5363685167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1724057/7812500 : ℝ)|^8293 ≤ (13444765162697/100000000000000 : ℝ)^6245
        have hw : |(-1724057/7812500 : ℝ)|=(1724057/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1320144969/2500000000 : ℝ)|^8293 ≤ (42828924899401/100000000000000 : ℝ)^6245
        have hw : |(1320144969/2500000000 : ℝ)|=(1320144969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_box_6 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1072737031/2000000000 : ℝ)*x 0 + (5280579873/10000000000 : ℝ)*x 1 + (-1103396489/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072737031/2000000000 : ℝ)^8293 ≤ (43726309797179/100000000000000 : ℝ)^6245 := by
    have hnat : (1072737031 : ℕ)^8293*100000000000000^6245 ≤ 43726309797179^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072737031 2000000000 43726309797179 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280579873/10000000000 : ℝ)^8293 ≤ (4282892486709/10000000000000 : ℝ)^6245 := by
    have hnat : (5280579873 : ℕ)^8293*10000000000000^6245 ≤ 4282892486709^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280579873 10000000000 4282892486709 10000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103396489/5000000000 : ℝ)^8293 ≤ (3361191327081/25000000000000 : ℝ)^6245 := by
    have hnat : (1103396489 : ℕ)^8293*25000000000000^6245 ≤ 3361191327081^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103396489 5000000000 3361191327081 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072737031/2000000000 : ℝ), (5280579873/10000000000 : ℝ), (-1103396489/5000000000 : ℝ)] ![(43726309797179/100000000000000 : ℝ), (4282892486709/10000000000000 : ℝ), (3361191327081/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072737031/2000000000 : ℝ)|^8293 ≤ (43726309797179/100000000000000 : ℝ)^6245
        have hw : |(1072737031/2000000000 : ℝ)|=(1072737031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280579873/10000000000 : ℝ)|^8293 ≤ (4282892486709/10000000000000 : ℝ)^6245
        have hw : |(5280579873/10000000000 : ℝ)|=(5280579873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1103396489/5000000000 : ℝ)|^8293 ≤ (3361191327081/25000000000000 : ℝ)^6245
        have hw : |(-1103396489/5000000000 : ℝ)|=(1103396489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_box_7 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1065570213/2500000000 : ℝ)*x 0 + (4426915317/10000000000 : ℝ)*x 1 + (4426915401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065570213/2500000000 : ℝ)^8293 ≤ (32224486785507/100000000000000 : ℝ)^6245 := by
    have hnat : (1065570213 : ℕ)^8293*100000000000000^6245 ≤ 32224486785507^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065570213 2500000000 32224486785507 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4426915317/10000000000 : ℝ)^8293 ≤ (1355510246811/4000000000000 : ℝ)^6245 := by
    have hnat : (4426915317 : ℕ)^8293*4000000000000^6245 ≤ 1355510246811^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4426915317 10000000000 1355510246811 4000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4426915401/10000000000 : ℝ)^8293 ≤ (33887757024161/100000000000000 : ℝ)^6245 := by
    have hnat : (4426915401 : ℕ)^8293*100000000000000^6245 ≤ 33887757024161^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4426915401 10000000000 33887757024161 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1065570213/2500000000 : ℝ), (4426915317/10000000000 : ℝ), (4426915401/10000000000 : ℝ)] ![(32224486785507/100000000000000 : ℝ), (1355510246811/4000000000000 : ℝ), (33887757024161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1065570213/2500000000 : ℝ)|^8293 ≤ (32224486785507/100000000000000 : ℝ)^6245
        have hw : |(1065570213/2500000000 : ℝ)|=(1065570213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4426915317/10000000000 : ℝ)|^8293 ≤ (1355510246811/4000000000000 : ℝ)^6245
        have hw : |(4426915317/10000000000 : ℝ)|=(4426915317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4426915401/10000000000 : ℝ)|^8293 ≤ (33887757024161/100000000000000 : ℝ)^6245
        have hw : |(4426915401/10000000000 : ℝ)|=(4426915401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_box_8 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-565731311/2500000000 : ℝ)*x 0 + (5215154799/10000000000 : ℝ)*x 1 + (5386504271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (565731311/2500000000 : ℝ)^8293 ≤ (6950391054597/50000000000000 : ℝ)^6245 := by
    have hnat : (565731311 : ℕ)^8293*50000000000000^6245 ≤ 6950391054597^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565731311 2500000000 6950391054597 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215154799/10000000000 : ℝ)^8293 ≤ (21062850711141/50000000000000 : ℝ)^6245 := by
    have hnat : (5215154799 : ℕ)^8293*50000000000000^6245 ≤ 21062850711141^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215154799 10000000000 21062850711141 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386504271/10000000000 : ℝ)^8293 ≤ (549668955643/1250000000000 : ℝ)^6245 := by
    have hnat : (5386504271 : ℕ)^8293*1250000000000^6245 ≤ 549668955643^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386504271 10000000000 549668955643 1250000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-565731311/2500000000 : ℝ), (5215154799/10000000000 : ℝ), (5386504271/10000000000 : ℝ)] ![(6950391054597/50000000000000 : ℝ), (21062850711141/50000000000000 : ℝ), (549668955643/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-565731311/2500000000 : ℝ)|^8293 ≤ (6950391054597/50000000000000 : ℝ)^6245
        have hw : |(-565731311/2500000000 : ℝ)|=(565731311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215154799/10000000000 : ℝ)|^8293 ≤ (21062850711141/50000000000000 : ℝ)^6245
        have hw : |(5215154799/10000000000 : ℝ)|=(5215154799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386504271/10000000000 : ℝ)|^8293 ≤ (549668955643/1250000000000 : ℝ)^6245
        have hw : |(5386504271/10000000000 : ℝ)|=(5386504271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_box_9 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322193733/2500000000 : ℝ)*x 0 + (-1082597619/5000000000 : ℝ)*x 1 + (5386504699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322193733/2500000000 : ℝ)^8293 ≤ (5364651497789/12500000000000 : ℝ)^6245 := by
    have hnat : (1322193733 : ℕ)^8293*12500000000000^6245 ≤ 5364651497789^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322193733 2500000000 5364651497789 12500000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082597619/5000000000 : ℝ)^8293 ≤ (1638658363961/12500000000000 : ℝ)^6245 := by
    have hnat : (1082597619 : ℕ)^8293*12500000000000^6245 ≤ 1638658363961^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082597619 5000000000 1638658363961 12500000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386504699/10000000000 : ℝ)^8293 ≤ (1758940843653/4000000000000 : ℝ)^6245 := by
    have hnat : (5386504699 : ℕ)^8293*4000000000000^6245 ≤ 1758940843653^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386504699 10000000000 1758940843653 4000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322193733/2500000000 : ℝ), (-1082597619/5000000000 : ℝ), (5386504699/10000000000 : ℝ)] ![(5364651497789/12500000000000 : ℝ), (1638658363961/12500000000000 : ℝ), (1758940843653/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322193733/2500000000 : ℝ)|^8293 ≤ (5364651497789/12500000000000 : ℝ)^6245
        have hw : |(1322193733/2500000000 : ℝ)|=(1322193733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1082597619/5000000000 : ℝ)|^8293 ≤ (1638658363961/12500000000000 : ℝ)^6245
        have hw : |(-1082597619/5000000000 : ℝ)|=(1082597619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386504699/10000000000 : ℝ)|^8293 ≤ (1758940843653/4000000000000 : ℝ)^6245
        have hw : |(5386504699/10000000000 : ℝ)|=(5386504699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_box_10 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322193761/2500000000 : ℝ)*x 0 + (2693252083/5000000000 : ℝ)*x 1 + (-1082597903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322193761/2500000000 : ℝ)^8293 ≤ (42917213189219/100000000000000 : ℝ)^6245 := by
    have hnat : (1322193761 : ℕ)^8293*100000000000000^6245 ≤ 42917213189219^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322193761 2500000000 42917213189219 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693252083/5000000000 : ℝ)^8293 ≤ (879470306263/2000000000000 : ℝ)^6245 := by
    have hnat : (2693252083 : ℕ)^8293*2000000000000^6245 ≤ 879470306263^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693252083 5000000000 879470306263 2000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082597903/5000000000 : ℝ)^8293 ≤ (1638658934807/12500000000000 : ℝ)^6245 := by
    have hnat : (1082597903 : ℕ)^8293*12500000000000^6245 ≤ 1638658934807^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082597903 5000000000 1638658934807 12500000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322193761/2500000000 : ℝ), (2693252083/5000000000 : ℝ), (-1082597903/5000000000 : ℝ)] ![(42917213189219/100000000000000 : ℝ), (879470306263/2000000000000 : ℝ), (1638658934807/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322193761/2500000000 : ℝ)|^8293 ≤ (42917213189219/100000000000000 : ℝ)^6245
        have hw : |(1322193761/2500000000 : ℝ)|=(1322193761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693252083/5000000000 : ℝ)|^8293 ≤ (879470306263/2000000000000 : ℝ)^6245
        have hw : |(2693252083/5000000000 : ℝ)|=(2693252083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1082597903/5000000000 : ℝ)|^8293 ≤ (1638658934807/12500000000000 : ℝ)^6245
        have hw : |(-1082597903/5000000000 : ℝ)|=(1082597903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_box_11 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (899985719/2000000000 : ℝ)*x 0 + (2153986087/5000000000 : ℝ)*x 1 + (4307972093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (899985719/2000000000 : ℝ)^8293 ≤ (17315979471511/50000000000000 : ℝ)^6245 := by
    have hnat : (899985719 : ℕ)^8293*50000000000000^6245 ≤ 17315979471511^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899985719 2000000000 17315979471511 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2153986087/5000000000 : ℝ)^8293 ≤ (408550261619/1250000000000 : ℝ)^6245 := by
    have hnat : (2153986087 : ℕ)^8293*1250000000000^6245 ≤ 408550261619^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153986087 5000000000 408550261619 1250000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4307972093/10000000000 : ℝ)^8293 ≤ (32684020113451/100000000000000 : ℝ)^6245 := by
    have hnat : (4307972093 : ℕ)^8293*100000000000000^6245 ≤ 32684020113451^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307972093 10000000000 32684020113451 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(899985719/2000000000 : ℝ), (2153986087/5000000000 : ℝ), (4307972093/10000000000 : ℝ)] ![(17315979471511/50000000000000 : ℝ), (408550261619/1250000000000 : ℝ), (32684020113451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(899985719/2000000000 : ℝ)|^8293 ≤ (17315979471511/50000000000000 : ℝ)^6245
        have hw : |(899985719/2000000000 : ℝ)|=(899985719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2153986087/5000000000 : ℝ)|^8293 ≤ (408550261619/1250000000000 : ℝ)^6245
        have hw : |(2153986087/5000000000 : ℝ)|=(2153986087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4307972093/10000000000 : ℝ)|^8293 ≤ (32684020113451/100000000000000 : ℝ)^6245
        have hw : |(4307972093/10000000000 : ℝ)|=(4307972093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_box_12 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-13206791/62500000 : ℝ)*x 0 + (5441015693/10000000000 : ℝ)*x 1 + (1054512283/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13206791/62500000 : ℝ)^8293 ≤ (3172992771429/25000000000000 : ℝ)^6245 := by
    have hnat : (13206791 : ℕ)^8293*25000000000000^6245 ≤ 3172992771429^6245*62500000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13206791 62500000 3172992771429 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441015693/10000000000 : ℝ)^8293 ≤ (44565445105173/100000000000000 : ℝ)^6245 := by
    have hnat : (5441015693 : ℕ)^8293*100000000000000^6245 ≤ 44565445105173^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441015693 10000000000 44565445105173 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054512283/2000000000 : ℝ)^8293 ≤ (10685645947911/25000000000000 : ℝ)^6245 := by
    have hnat : (1054512283 : ℕ)^8293*25000000000000^6245 ≤ 10685645947911^6245*2000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054512283 2000000000 10685645947911 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13206791/62500000 : ℝ), (5441015693/10000000000 : ℝ), (1054512283/2000000000 : ℝ)] ![(3172992771429/25000000000000 : ℝ), (44565445105173/100000000000000 : ℝ), (10685645947911/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13206791/62500000 : ℝ)|^8293 ≤ (3172992771429/25000000000000 : ℝ)^6245
        have hw : |(-13206791/62500000 : ℝ)|=(13206791/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441015693/10000000000 : ℝ)|^8293 ≤ (44565445105173/100000000000000 : ℝ)^6245
        have hw : |(5441015693/10000000000 : ℝ)|=(5441015693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054512283/2000000000 : ℝ)|^8293 ≤ (10685645947911/25000000000000 : ℝ)^6245
        have hw : |(1054512283/2000000000 : ℝ)|=(1054512283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_box_13 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684676609/5000000000 : ℝ)*x 0 + (-1104939283/5000000000 : ℝ)*x 1 + (2636280703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684676609/5000000000 : ℝ)^8293 ≤ (8757536314043/20000000000000 : ℝ)^6245 := by
    have hnat : (2684676609 : ℕ)^8293*20000000000000^6245 ≤ 8757536314043^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684676609 5000000000 8757536314043 20000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1104939283/5000000000 : ℝ)^8293 ≤ (673486736027/5000000000000 : ℝ)^6245 := by
    have hnat : (1104939283 : ℕ)^8293*5000000000000^6245 ≤ 673486736027^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104939283 5000000000 673486736027 5000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636280703/5000000000 : ℝ)^8293 ≤ (21371291847379/50000000000000 : ℝ)^6245 := by
    have hnat : (2636280703 : ℕ)^8293*50000000000000^6245 ≤ 21371291847379^6245*5000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636280703 5000000000 21371291847379 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684676609/5000000000 : ℝ), (-1104939283/5000000000 : ℝ), (2636280703/5000000000 : ℝ)] ![(8757536314043/20000000000000 : ℝ), (673486736027/5000000000000 : ℝ), (21371291847379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684676609/5000000000 : ℝ)|^8293 ≤ (8757536314043/20000000000000 : ℝ)^6245
        have hw : |(2684676609/5000000000 : ℝ)|=(2684676609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1104939283/5000000000 : ℝ)|^8293 ≤ (673486736027/5000000000000 : ℝ)^6245
        have hw : |(-1104939283/5000000000 : ℝ)|=(1104939283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636280703/5000000000 : ℝ)|^8293 ≤ (21371291847379/50000000000000 : ℝ)^6245
        have hw : |(2636280703/5000000000 : ℝ)|=(2636280703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_box_14 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369353343/10000000000 : ℝ)*x 0 + (659070169/1250000000 : ℝ)*x 1 + (-2209878471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369353343/10000000000 : ℝ)^8293 ≤ (8757536584781/20000000000000 : ℝ)^6245 := by
    have hnat : (5369353343 : ℕ)^8293*20000000000000^6245 ≤ 8757536584781^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369353343 10000000000 8757536584781 20000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (659070169/1250000000 : ℝ)^8293 ≤ (21371291556721/50000000000000 : ℝ)^6245 := by
    have hnat : (659070169 : ℕ)^8293*50000000000000^6245 ≤ 21371291556721^6245*1250000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659070169 1250000000 21371291556721 50000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2209878471/10000000000 : ℝ)^8293 ≤ (13469733951599/100000000000000 : ℝ)^6245 := by
    have hnat : (2209878471 : ℕ)^8293*100000000000000^6245 ≤ 13469733951599^6245*10000000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209878471 10000000000 13469733951599 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369353343/10000000000 : ℝ), (659070169/1250000000 : ℝ), (-2209878471/10000000000 : ℝ)] ![(8757536584781/20000000000000 : ℝ), (21371291556721/50000000000000 : ℝ), (13469733951599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369353343/10000000000 : ℝ)|^8293 ≤ (8757536584781/20000000000000 : ℝ)^6245
        have hw : |(5369353343/10000000000 : ℝ)|=(5369353343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(659070169/1250000000 : ℝ)|^8293 ≤ (21371291556721/50000000000000 : ℝ)^6245
        have hw : |(659070169/1250000000 : ℝ)|=(659070169/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2209878471/10000000000 : ℝ)|^8293 ≤ (13469733951599/100000000000000 : ℝ)^6245
        have hw : |(-2209878471/10000000000 : ℝ)|=(2209878471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1100_box_15 (p : ℝ) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1061009867/2500000000 : ℝ)*x 0 + (277244623/625000000 : ℝ)*x 1 + (1108978543/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061009867/2500000000 : ℝ)^8293 ≤ (1602073818897/5000000000000 : ℝ)^6245 := by
    have hnat : (1061009867 : ℕ)^8293*5000000000000^6245 ≤ 1602073818897^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061009867 2500000000 1602073818897 5000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (277244623/625000000 : ℝ)^8293 ≤ (33979260763283/100000000000000 : ℝ)^6245 := by
    have hnat : (277244623 : ℕ)^8293*100000000000000^6245 ≤ 33979260763283^6245*625000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277244623 625000000 33979260763283 100000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1108978543/2500000000 : ℝ)^8293 ≤ (8494815709597/25000000000000 : ℝ)^6245 := by
    have hnat : (1108978543 : ℕ)^8293*25000000000000^6245 ≤ 8494815709597^6245*2500000000^8293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108978543 2500000000 8494815709597 25000000000000 8293 6245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8293/2048 : ℝ)) 8293 6245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061009867/2500000000 : ℝ), (277244623/625000000 : ℝ), (1108978543/2500000000 : ℝ)] ![(1602073818897/5000000000000 : ℝ), (33979260763283/100000000000000 : ℝ), (8494815709597/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061009867/2500000000 : ℝ)|^8293 ≤ (1602073818897/5000000000000 : ℝ)^6245
        have hw : |(1061009867/2500000000 : ℝ)|=(1061009867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(277244623/625000000 : ℝ)|^8293 ≤ (33979260763283/100000000000000 : ℝ)^6245
        have hw : |(277244623/625000000 : ℝ)|=(277244623/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1108978543/2500000000 : ℝ)|^8293 ≤ (8494815709597/25000000000000 : ℝ)^6245
        have hw : |(1108978543/2500000000 : ℝ)|=(1108978543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1100_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14023/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62227/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29633/50000 : ℝ) ∧ (79679/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (8303/10000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14023/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5649/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14023/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5649/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14023/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5649/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14023/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5649/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14023/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5649/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14023/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5649/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5649/50000 : ℝ) ^ (2073/512 : ℝ) ≤ (2929517654352307/20000000000000000000 : ℝ) := by
    have hpowers : (5649/50000 : ℝ)^2073 ≤ (2929517654352307/20000000000000000000 : ℝ)^512 := by
      have hnat : (5649 : ℕ)^2073*20000000000000000000^512 ≤ 2929517654352307^512*50000^2073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5649 50000 2929517654352307 20000000000000000000 2073 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5649/50000 : ℝ)) (X := (2929517654352307/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14023/100000 : ℝ) ^ (2073/512 : ℝ) ≤ (4391527347883167/12500000000000000000 : ℝ) := by
    have hpowers : (14023/100000 : ℝ)^2073 ≤ (4391527347883167/12500000000000000000 : ℝ)^512 := by
      have hnat : (14023 : ℕ)^2073*12500000000000000000^512 ≤ 4391527347883167^512*100000^2073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14023 100000 4391527347883167 12500000000000000000 2073 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14023/100000 : ℝ)) (X := (4391527347883167/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002929517654352307/10000000000000000000 : ℝ) ≤ (2000144693451919/2000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (10002929517654352307/10000000000000000000 : ℝ)^512 ≤ (2000144693451919/2000000000000000 : ℝ)^2073 := by
      have hnat : (10002929517654352307 : ℕ)^512*2000000000000000^2073 ≤ 2000144693451919^2073*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002929517654352307 10000000000000000000 2000144693451919 2000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000144693451919/2000000000000000 : ℝ)) (X := (10002929517654352307/10000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049779807054826871/100000000000000000000 : ℝ) ≤ (10001229256423491/10000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (100049779807054826871/100000000000000000000 : ℝ)^512 ≤ (10001229256423491/10000000000000000 : ℝ)^2073 := by
      have hnat : (100049779807054826871 : ℕ)^512*10000000000000000^2073 ≤ 10001229256423491^2073*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049779807054826871 100000000000000000000 10001229256423491 10000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001229256423491/10000000000000000 : ℝ)) (X := (100049779807054826871/100000000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254391527347883167/6250000000000000000 : ℝ) ≤ (10001735045587387/10000000000000000 : ℝ) ^ (2073/512 : ℝ) := by
    have hpowers : (6254391527347883167/6250000000000000000 : ℝ)^512 ≤ (10001735045587387/10000000000000000 : ℝ)^2073 := by
      have hnat : (6254391527347883167 : ℕ)^512*10000000000000000^2073 ≤ 10001735045587387^2073*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254391527347883167 6250000000000000000 10001735045587387 10000000000000000 512 2073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001735045587387/10000000000000000 : ℝ)) (X := (6254391527347883167/6250000000000000000 : ℝ)) (by norm_num) 2073 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2929517654352307/20000000000000000000 : ℝ) ≤ ((27240542636335002359/27250000000000000000 : ℝ)+2*(63223645487/34062500000000 : ℝ)*(5649/50000 : ℝ))^(2073/512 : ℝ) := by
    rw [show (27240542636335002359/27250000000000000000 : ℝ)+2*(63223645487/34062500000000 : ℝ)*(5649/50000 : ℝ)=(2000144693451919/2000000000000000 : ℝ) by norm_num, show 1+2*(2929517654352307/20000000000000000000 : ℝ)=(10002929517654352307/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4391527347883167/12500000000000000000 : ℝ)+(2929517654352307/20000000000000000000 : ℝ) ≤ ((27240542636335002359/27250000000000000000 : ℝ)+(63223645487/34062500000000 : ℝ)*((14023/100000 : ℝ)+(5649/50000 : ℝ)))^(2073/512 : ℝ) := by
    rw [show (27240542636335002359/27250000000000000000 : ℝ)+(63223645487/34062500000000 : ℝ)*((14023/100000 : ℝ)+(5649/50000 : ℝ))=(10001229256423491/10000000000000000 : ℝ) by norm_num, show 1+(4391527347883167/12500000000000000000 : ℝ)+(2929517654352307/20000000000000000000 : ℝ)=(100049779807054826871/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4391527347883167/12500000000000000000 : ℝ) ≤ ((27240542636335002359/27250000000000000000 : ℝ)+2*(63223645487/34062500000000 : ℝ)*(14023/100000 : ℝ))^(2073/512 : ℝ) := by
    rw [show (27240542636335002359/27250000000000000000 : ℝ)+2*(63223645487/34062500000000 : ℝ)*(14023/100000 : ℝ)=(10001735045587387/10000000000000000 : ℝ) by norm_num, show 1+2*(4391527347883167/12500000000000000000 : ℝ)=(6254391527347883167/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27240542636335002359/27250000000000000000 : ℝ)*(X 1 0+X 2 0)+(63223645487/34062500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (5649/50000 : ℝ)) (hi := (14023/100000 : ℝ)) (c := (27240542636335002359/27250000000000000000 : ℝ)) (alpha := (63223645487/34062500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27240542636335002359/27250000000000000000 : ℝ)*(X 0 1+X 2 1)+(63223645487/34062500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (5649/50000 : ℝ)) (hi := (14023/100000 : ℝ)) (c := (27240542636335002359/27250000000000000000 : ℝ)) (alpha := (63223645487/34062500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27240542636335002359/27250000000000000000 : ℝ)*(X 0 2+X 1 2)+(63223645487/34062500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2073/512 : ℝ)) (lo := (5649/50000 : ℝ)) (hi := (14023/100000 : ℝ)) (c := (27240542636335002359/27250000000000000000 : ℝ)) (alpha := (63223645487/34062500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1029421463/5000000000 : ℝ)*X 0 0+(2688449797/5000000000 : ℝ)*X 0 1+(2688449899/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295570719/10000000000 : ℝ)*X 1 0+(-27112889/125000000 : ℝ)*X 1 1+(1344224917/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647785377/5000000000 : ℝ)*X 2 0+(672112469/1250000000 : ℝ)*X 2 1+(-27112887/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4478627979/10000000000 : ℝ)*X 0 0+(2159381509/5000000000 : ℝ)*X 0 1+(2159381463/5000000000 : ℝ)*X 0 2+(4478627979/10000000000 : ℝ)*X 1 0+(2159381509/5000000000 : ℝ)*X 1 1+(2159381463/5000000000 : ℝ)*X 1 2+(4478627979/10000000000 : ℝ)*X 2 0+(2159381509/5000000000 : ℝ)*X 2 1+(2159381463/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-579205683/2500000000 : ℝ)*X 0 0+(2640289977/5000000000 : ℝ)*X 0 1+(211223193/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5363685167/10000000000 : ℝ)*X 1 0+(-1724057/7812500 : ℝ)*X 1 1+(1320144969/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1072737031/2000000000 : ℝ)*X 2 0+(5280579873/10000000000 : ℝ)*X 2 1+(-1103396489/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1065570213/2500000000 : ℝ)*X 0 0+(4426915317/10000000000 : ℝ)*X 0 1+(4426915401/10000000000 : ℝ)*X 0 2+(1065570213/2500000000 : ℝ)*X 1 0+(4426915317/10000000000 : ℝ)*X 1 1+(4426915401/10000000000 : ℝ)*X 1 2+(1065570213/2500000000 : ℝ)*X 2 0+(4426915317/10000000000 : ℝ)*X 2 1+(4426915401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-565731311/2500000000 : ℝ)*X 0 0+(5215154799/10000000000 : ℝ)*X 0 1+(5386504271/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1322193733/2500000000 : ℝ)*X 1 0+(-1082597619/5000000000 : ℝ)*X 1 1+(5386504699/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322193761/2500000000 : ℝ)*X 2 0+(2693252083/5000000000 : ℝ)*X 2 1+(-1082597903/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((899985719/2000000000 : ℝ)*X 0 0+(2153986087/5000000000 : ℝ)*X 0 1+(4307972093/10000000000 : ℝ)*X 0 2+(899985719/2000000000 : ℝ)*X 1 0+(2153986087/5000000000 : ℝ)*X 1 1+(4307972093/10000000000 : ℝ)*X 1 2+(899985719/2000000000 : ℝ)*X 2 0+(2153986087/5000000000 : ℝ)*X 2 1+(4307972093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-13206791/62500000 : ℝ)*X 0 0+(5441015693/10000000000 : ℝ)*X 0 1+(1054512283/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2684676609/5000000000 : ℝ)*X 1 0+(-1104939283/5000000000 : ℝ)*X 1 1+(2636280703/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369353343/10000000000 : ℝ)*X 2 0+(659070169/1250000000 : ℝ)*X 2 1+(-2209878471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1061009867/2500000000 : ℝ)*X 0 0+(277244623/625000000 : ℝ)*X 0 1+(1108978543/2500000000 : ℝ)*X 0 2+(1061009867/2500000000 : ℝ)*X 1 0+(277244623/625000000 : ℝ)*X 1 1+(1108978543/2500000000 : ℝ)*X 1 2+(1061009867/2500000000 : ℝ)*X 2 0+(277244623/625000000 : ℝ)*X 2 1+(1108978543/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1100_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62227/100000 : ℝ) ≤ (-42390364318703790199680932956227/68125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18109859/50000000000000 : ℝ)*(upper0) + (31481/20000000000000 : ℝ)*(upper1) + (1074887/4000000000000 : ℝ)*(upper3) + (388531507911049/10000000000000 : ℝ)*(major0) + (388531507911049/10000000000000 : ℝ)*(major1) + (388531507911049/10000000000000 : ℝ)*(major2) + (943211671/100000000000000 : ℝ)*(sp1) + (1551547/5000000000000 : ℝ)*(sp2) + (1897006253/100000000000000 : ℝ)*(sp3) + (1035544658242431/20000000000000 : ℝ)*(sp4) + (5177723176574373/100000000000000 : ℝ)*(sp5) + (161803877773597/3125000000000 : ℝ)*(sp6) + (1306822802046129/50000000000000 : ℝ)*(sp7) + (12946467/1562500000000 : ℝ)*(sp8) + (2613647501098511/100000000000000 : ℝ)*(f.failure) + (5177724119786043/100000000000000 : ℝ)*(f.sum) + (5855378937167/2725000000000000000000000000 : ℝ)*base66 + (333755614522564591/272500000000000000000000000000000 : ℝ)*base67 + (13530252374309935409/272500000000000000000000000000000 : ℝ)*base70 + (1323422212449935409/272500000000000000000000000000000 : ℝ)*base72 + (2713586145577/681250000000000000000000000 : ℝ)*base73 + (1893383612752435409/272500000000000000000000000000000 : ℝ)*base76 + (1048012768099935409/272500000000000000000000000000000 : ℝ)*base78 + (487918892002435409/272500000000000000000000000000000 : ℝ)*base80 + (7080974550199/340625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (428539/100000000000000000000 : ℝ)*base89 + (428539/100000000000000000000 : ℝ)*base91 + (428539/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29633/50000 : ℝ) ≤ (403769018710821801144637448021037/681250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7918063/25000000000000 : ℝ)*(lower0) + (2132017/100000000000000 : ℝ)*(lower1) + (47315129/100000000000000 : ℝ)*(lower2) + (8751387/12500000000000 : ℝ)*(lower3) + (525403/6250000000000 : ℝ)*(upper4) + (425141/20000000000000 : ℝ)*(lower5) + (1974391357721481/50000000000000 : ℝ)*(major0) + (1974391357721481/50000000000000 : ℝ)*(major1) + (1974391357721481/50000000000000 : ℝ)*(major2) + (2610733516566263/50000000000000 : ℝ)*(sp0) + (2610733516566263/50000000000000 : ℝ)*(sp1) + (1305365383887907/25000000000000 : ℝ)*(sp2) + (26563421154923/1000000000000 : ℝ)*(sp3) + (2748790449/50000000000000 : ℝ)*(sp6) + (26563421154923/1000000000000 : ℝ)*(f.failure) + (2610733516566263/50000000000000 : ℝ)*(f.sum) + (8333734815753/851562500000000000000000000 : ℝ)*base66 + (6944557127452426321/1362500000000000000000000000000000 : ℝ)*base68 + (19477937075847573679/1362500000000000000000000000000000 : ℝ)*base69 + (9779936045577426321/1362500000000000000000000000000000 : ℝ)*base72 + (7746674014381/1703125000000000000000000000 : ℝ)*base74 + (83653464256402426321/1362500000000000000000000000000000 : ℝ)*base76 + (17922168612727426321/1362500000000000000000000000000000 : ℝ)*base78 + (757835541372573679/1362500000000000000000000000000000 : ℝ)*base79 + (182582881247363/3406250000000000000000000000 : ℝ)*base81 + (10727/1000000000000000000 : ℝ)*base89 + (10727/1000000000000000000 : ℝ)*base91 + (10727/1000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79679/100000 : ℝ) ≤ (135706902227536285452454548215871/170312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (75739029/100000000000000 : ℝ)*(upper0) + (61121339/50000000000000 : ℝ)*(upper2) + (81349377/25000000000000 : ℝ)*(lower5) + (1104227955602823/25000000000000 : ℝ)*(major0) + (1104227955602823/25000000000000 : ℝ)*(major1) + (1104227955602823/25000000000000 : ℝ)*(major2) + (1851929521/50000000000000 : ℝ)*(sp0) + (276062217749/100000000000000 : ℝ)*(sp1) + (24915836253/25000000000000 : ℝ)*(sp3) + (5836006441790591/100000000000000 : ℝ)*(sp8) + (583573512079187/10000000000000 : ℝ)*(sp9) + (5836011183009619/100000000000000 : ℝ)*(sp10) + (297115242616653/10000000000000 : ℝ)*(sp11) + (1037359987/100000000000000 : ℝ)*(sp12) + (1485626044755771/50000000000000 : ℝ)*(f.failure) + (5836011183009619/100000000000000 : ℝ)*(f.sum) + (26421936426809/6812500000000000000000000000 : ℝ)*base66 + (2703261782212859457/681250000000000000000000000000000 : ℝ)*base67 + (11469502798412140543/681250000000000000000000000000000 : ℝ)*base70 + (3863516033193390543/681250000000000000000000000000000 : ℝ)*base72 + (2146754446963/212890625000000000000000000 : ℝ)*base73 + (8279423764787140543/681250000000000000000000000000000 : ℝ)*base76 + (5176457728724640543/681250000000000000000000000000000 : ℝ)*base78 + (3179040124374640543/681250000000000000000000000000000 : ℝ)*base80 + (7430629785671/1703125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (624279/50000000000000000000 : ℝ)*base89 + (624279/50000000000000000000 : ℝ)*base91 + (624279/50000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-8303/10000 : ℝ) ≤ (-1131247258393989880332790580933541/1362500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1177059/20000000000000 : ℝ)*(lower1) + (28264267/100000000000000 : ℝ)*(lower2) + (2864959/100000000000000 : ℝ)*(lower3) + (133741461/100000000000000 : ℝ)*(upper5) + (4451625705800033/100000000000000 : ℝ)*(major0) + (4451625705800033/100000000000000 : ℝ)*(major1) + (4451625705800033/100000000000000 : ℝ)*(major2) + (10429705751/100000000000000 : ℝ)*(sp5) + (22869470053/25000000000000 : ℝ)*(sp6) + (21882616411/50000000000000 : ℝ)*(sp7) + (5936323101953787/100000000000000 : ℝ)*(sp12) + (1484078168062009/25000000000000 : ℝ)*(sp13) + (237449264962943/4000000000000 : ℝ)*(sp14) + (5848750621717/195312500000 : ℝ)*(sp15) + (1497302041775963/50000000000000 : ℝ)*(f.failure) + (5936323101953787/100000000000000 : ℝ)*(f.sum) + (2267397732049/425781250000000000000000000 : ℝ)*base65 + (1543058325930922153/2725000000000000000000000000000000 : ℝ)*base68 + (38396984696519077847/2725000000000000000000000000000000 : ℝ)*base69 + (7281479094169077847/2725000000000000000000000000000000 : ℝ)*base71 + (14128530842409/6812500000000000000000000000 : ℝ)*base73 + (1812125820555922153/2725000000000000000000000000000000 : ℝ)*base76 + (10080629559669077847/2725000000000000000000000000000000 : ℝ)*base77 + (18856653867444077847/2725000000000000000000000000000000 : ℝ)*base79 + (1086814534203443/13625000000000000000000000000 : ℝ)*base81 + (478313/50000000000000000000 : ℝ)*base90 + (478313/50000000000000000000 : ℝ)*base92 + (478313/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1100_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14023/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29633/50000 : ℝ) else (79679/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8303/10000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1100_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1100_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29633/50000 : ℝ) else (79679/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8303/10000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1100_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1100_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2073/512 : ℝ) ≤ p) (hpb : p ≤ (8293/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1486549/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29633/50000 : ℝ) else (79679/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8303/10000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1100_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
