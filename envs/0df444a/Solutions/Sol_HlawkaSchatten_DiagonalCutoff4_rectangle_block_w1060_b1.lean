-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1060_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:02:53.12936+00:00
-- url     : https://prove2.me/submissions/5f075ac9-52cd-48c2-8a8c-fa22b85e0bf6

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
theorem support_rectangle_w1060_s3_0 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1100951369/5000000000 : ℝ)*x 0 + (5438246153/10000000000 : ℝ)*x 1 + (5223711169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1100951369/5000000000 : ℝ)^8253 ≤ (2672479855811/20000000000000 : ℝ)^6205 := by
    have hnat : (1100951369 : ℕ)^8253*20000000000000^6205 ≤ 2672479855811^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100951369 5000000000 2672479855811 20000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438246153/10000000000 : ℝ)^8253 ≤ (44478011601901/100000000000000 : ℝ)^6205 := by
    have hnat : (5438246153 : ℕ)^8253*100000000000000^6205 ≤ 44478011601901^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438246153 10000000000 44478011601901 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5223711169/10000000000 : ℝ)^8253 ≤ (42159589103669/100000000000000 : ℝ)^6205 := by
    have hnat : (5223711169 : ℕ)^8253*100000000000000^6205 ≤ 42159589103669^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223711169 10000000000 42159589103669 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1100951369/5000000000 : ℝ), (5438246153/10000000000 : ℝ), (5223711169/10000000000 : ℝ)] ![(2672479855811/20000000000000 : ℝ), (44478011601901/100000000000000 : ℝ), (42159589103669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1100951369/5000000000 : ℝ)|^8253 ≤ (2672479855811/20000000000000 : ℝ)^6205
        have hw : |(-1100951369/5000000000 : ℝ)|=(1100951369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438246153/10000000000 : ℝ)|^8253 ≤ (44478011601901/100000000000000 : ℝ)^6205
        have hw : |(5438246153/10000000000 : ℝ)|=(5438246153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5223711169/10000000000 : ℝ)|^8253 ≤ (42159589103669/100000000000000 : ℝ)^6205
        have hw : |(5223711169/10000000000 : ℝ)|=(5223711169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s3_1 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5355848271/10000000000 : ℝ)*x 0 + (-72243079/312500000 : ℝ)*x 1 + (5223711209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355848271/10000000000 : ℝ)^8253 ≤ (871678416341/2000000000000 : ℝ)^6205 := by
    have hnat : (5355848271 : ℕ)^8253*2000000000000^6205 ≤ 871678416341^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355848271 10000000000 871678416341 2000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (72243079/312500000 : ℝ)^8253 ≤ (7128244819471/50000000000000 : ℝ)^6205 := by
    have hnat : (72243079 : ℕ)^8253*50000000000000^6205 ≤ 7128244819471^6205*312500000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72243079 312500000 7128244819471 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5223711209/10000000000 : ℝ)^8253 ≤ (8431917906611/20000000000000 : ℝ)^6205 := by
    have hnat : (5223711209 : ℕ)^8253*20000000000000^6205 ≤ 8431917906611^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223711209 10000000000 8431917906611 20000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355848271/10000000000 : ℝ), (-72243079/312500000 : ℝ), (5223711209/10000000000 : ℝ)] ![(871678416341/2000000000000 : ℝ), (7128244819471/50000000000000 : ℝ), (8431917906611/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355848271/10000000000 : ℝ)|^8253 ≤ (871678416341/2000000000000 : ℝ)^6205
        have hw : |(5355848271/10000000000 : ℝ)|=(5355848271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-72243079/312500000 : ℝ)|^8253 ≤ (7128244819471/50000000000000 : ℝ)^6205
        have hw : |(-72243079/312500000 : ℝ)|=(72243079/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5223711209/10000000000 : ℝ)|^8253 ≤ (8431917906611/20000000000000 : ℝ)^6205
        have hw : |(5223711209/10000000000 : ℝ)|=(5223711209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s3_2 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5355848249/10000000000 : ℝ)*x 0 + (652963913/1250000000 : ℝ)*x 1 + (-18060769/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355848249/10000000000 : ℝ)^8253 ≤ (43583920578933/100000000000000 : ℝ)^6205 := by
    have hnat : (5355848249 : ℕ)^8253*100000000000000^6205 ≤ 43583920578933^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355848249 10000000000 43583920578933 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652963913/1250000000 : ℝ)^8253 ≤ (8431918110569/20000000000000 : ℝ)^6205 := by
    have hnat : (652963913 : ℕ)^8253*20000000000000^6205 ≤ 8431918110569^6205*1250000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652963913 1250000000 8431918110569 20000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18060769/78125000 : ℝ)^8253 ≤ (44551527661/312500000000 : ℝ)^6205 := by
    have hnat : (18060769 : ℕ)^8253*312500000000^6205 ≤ 44551527661^6205*78125000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18060769 78125000 44551527661 312500000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355848249/10000000000 : ℝ), (652963913/1250000000 : ℝ), (-18060769/78125000 : ℝ)] ![(43583920578933/100000000000000 : ℝ), (8431918110569/20000000000000 : ℝ), (44551527661/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355848249/10000000000 : ℝ)|^8253 ≤ (43583920578933/100000000000000 : ℝ)^6205
        have hw : |(5355848249/10000000000 : ℝ)|=(5355848249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652963913/1250000000 : ℝ)|^8253 ≤ (8431918110569/20000000000000 : ℝ)^6205
        have hw : |(652963913/1250000000 : ℝ)|=(652963913/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-18060769/78125000 : ℝ)|^8253 ≤ (44551527661/312500000000 : ℝ)^6205
        have hw : |(-18060769/78125000 : ℝ)|=(18060769/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s3_3 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2186752301/5000000000 : ℝ)*x 0 + (104215789/250000000 : ℝ)*x 1 + (2294294579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186752301/5000000000 : ℝ)^8253 ≤ (16643823312437/50000000000000 : ℝ)^6205 := by
    have hnat : (2186752301 : ℕ)^8253*50000000000000^6205 ≤ 16643823312437^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186752301 5000000000 16643823312437 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104215789/250000000 : ℝ)^8253 ≤ (15614926374227/50000000000000 : ℝ)^6205 := by
    have hnat : (104215789 : ℕ)^8253*50000000000000^6205 ≤ 15614926374227^6205*250000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104215789 250000000 15614926374227 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2294294579/5000000000 : ℝ)^8253 ≤ (17741250304181/50000000000000 : ℝ)^6205 := by
    have hnat : (2294294579 : ℕ)^8253*50000000000000^6205 ≤ 17741250304181^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2294294579 5000000000 17741250304181 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186752301/5000000000 : ℝ), (104215789/250000000 : ℝ), (2294294579/5000000000 : ℝ)] ![(16643823312437/50000000000000 : ℝ), (15614926374227/50000000000000 : ℝ), (17741250304181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186752301/5000000000 : ℝ)|^8253 ≤ (16643823312437/50000000000000 : ℝ)^6205
        have hw : |(2186752301/5000000000 : ℝ)|=(2186752301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104215789/250000000 : ℝ)|^8253 ≤ (15614926374227/50000000000000 : ℝ)^6205
        have hw : |(104215789/250000000 : ℝ)|=(104215789/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2294294579/5000000000 : ℝ)|^8253 ≤ (17741250304181/50000000000000 : ℝ)^6205
        have hw : |(2294294579/5000000000 : ℝ)|=(2294294579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s3_4 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-550481407/2500000000 : ℝ)*x 0 + (5224594801/10000000000 : ℝ)*x 1 + (5437357149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (550481407/2500000000 : ℝ)^8253 ≤ (13362584036909/100000000000000 : ℝ)^6205 := by
    have hnat : (550481407 : ℕ)^8253*100000000000000^6205 ≤ 13362584036909^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550481407 2500000000 13362584036909 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5224594801/10000000000 : ℝ)^8253 ≤ (42169074835249/100000000000000 : ℝ)^6205 := by
    have hnat : (5224594801 : ℕ)^8253*100000000000000^6205 ≤ 42169074835249^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224594801 10000000000 42169074835249 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437357149/10000000000 : ℝ)^8253 ≤ (44468341110123/100000000000000 : ℝ)^6205 := by
    have hnat : (5437357149 : ℕ)^8253*100000000000000^6205 ≤ 44468341110123^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437357149 10000000000 44468341110123 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-550481407/2500000000 : ℝ), (5224594801/10000000000 : ℝ), (5437357149/10000000000 : ℝ)] ![(13362584036909/100000000000000 : ℝ), (42169074835249/100000000000000 : ℝ), (44468341110123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-550481407/2500000000 : ℝ)|^8253 ≤ (13362584036909/100000000000000 : ℝ)^6205
        have hw : |(-550481407/2500000000 : ℝ)|=(550481407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5224594801/10000000000 : ℝ)|^8253 ≤ (42169074835249/100000000000000 : ℝ)^6205
        have hw : |(5224594801/10000000000 : ℝ)|=(5224594801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437357149/10000000000 : ℝ)|^8253 ≤ (44468341110123/100000000000000 : ℝ)^6205
        have hw : |(5437357149/10000000000 : ℝ)|=(5437357149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s3_5 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212073319/400000000 : ℝ)*x 0 + (-2098131653/10000000000 : ℝ)*x 1 + (679669721/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212073319/400000000 : ℝ)^8253 ≤ (43000261005931/100000000000000 : ℝ)^6205 := by
    have hnat : (212073319 : ℕ)^8253*100000000000000^6205 ≤ 43000261005931^6205*400000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212073319 400000000 43000261005931 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2098131653/10000000000 : ℝ)^8253 ≤ (3132847784653/25000000000000 : ℝ)^6205 := by
    have hnat : (2098131653 : ℕ)^8253*25000000000000^6205 ≤ 3132847784653^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098131653 10000000000 3132847784653 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679669721/1250000000 : ℝ)^8253 ≤ (44468347843359/100000000000000 : ℝ)^6205 := by
    have hnat : (679669721 : ℕ)^8253*100000000000000^6205 ≤ 44468347843359^6205*1250000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679669721 1250000000 44468347843359 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212073319/400000000 : ℝ), (-2098131653/10000000000 : ℝ), (679669721/1250000000 : ℝ)] ![(43000261005931/100000000000000 : ℝ), (3132847784653/25000000000000 : ℝ), (44468347843359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212073319/400000000 : ℝ)|^8253 ≤ (43000261005931/100000000000000 : ℝ)^6205
        have hw : |(212073319/400000000 : ℝ)|=(212073319/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2098131653/10000000000 : ℝ)|^8253 ≤ (3132847784653/25000000000000 : ℝ)^6205
        have hw : |(-2098131653/10000000000 : ℝ)|=(2098131653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679669721/1250000000 : ℝ)|^8253 ≤ (44468347843359/100000000000000 : ℝ)^6205
        have hw : |(679669721/1250000000 : ℝ)|=(679669721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s3_6 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5301832613/10000000000 : ℝ)*x 0 + (2718678813/5000000000 : ℝ)*x 1 + (-2098132339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301832613/10000000000 : ℝ)^8253 ≤ (10750064275227/25000000000000 : ℝ)^6205 := by
    have hnat : (5301832613 : ℕ)^8253*25000000000000^6205 ≤ 10750064275227^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301832613 10000000000 10750064275227 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718678813/5000000000 : ℝ)^8253 ≤ (44468346298739/100000000000000 : ℝ)^6205 := by
    have hnat : (2718678813 : ℕ)^8253*100000000000000^6205 ≤ 44468346298739^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718678813 5000000000 44468346298739 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2098132339/10000000000 : ℝ)^8253 ≤ (3132849147041/25000000000000 : ℝ)^6205 := by
    have hnat : (2098132339 : ℕ)^8253*25000000000000^6205 ≤ 3132849147041^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098132339 10000000000 3132849147041 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301832613/10000000000 : ℝ), (2718678813/5000000000 : ℝ), (-2098132339/10000000000 : ℝ)] ![(10750064275227/25000000000000 : ℝ), (44468346298739/100000000000000 : ℝ), (3132849147041/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301832613/10000000000 : ℝ)|^8253 ≤ (10750064275227/25000000000000 : ℝ)^6205
        have hw : |(5301832613/10000000000 : ℝ)|=(5301832613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718678813/5000000000 : ℝ)|^8253 ≤ (44468346298739/100000000000000 : ℝ)^6205
        have hw : |(2718678813/5000000000 : ℝ)|=(2718678813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2098132339/10000000000 : ℝ)|^8253 ≤ (3132849147041/25000000000000 : ℝ)^6205
        have hw : |(-2098132339/10000000000 : ℝ)|=(2098132339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s3_7 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4373548883/10000000000 : ℝ)*x 0 + (1146715129/2500000000 : ℝ)*x 1 + (65162041/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373548883/10000000000 : ℝ)^8253 ≤ (33288094896973/100000000000000 : ℝ)^6205 := by
    have hnat : (4373548883 : ℕ)^8253*100000000000000^6205 ≤ 33288094896973^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373548883 10000000000 33288094896973 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1146715129/2500000000 : ℝ)^8253 ≤ (35464722597763/100000000000000 : ℝ)^6205 := by
    have hnat : (1146715129 : ℕ)^8253*100000000000000^6205 ≤ 35464722597763^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146715129 2500000000 35464722597763 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65162041/156250000 : ℝ)^8253 ≤ (6249436496871/20000000000000 : ℝ)^6205 := by
    have hnat : (65162041 : ℕ)^8253*20000000000000^6205 ≤ 6249436496871^6205*156250000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65162041 156250000 6249436496871 20000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373548883/10000000000 : ℝ), (1146715129/2500000000 : ℝ), (65162041/156250000 : ℝ)] ![(33288094896973/100000000000000 : ℝ), (35464722597763/100000000000000 : ℝ), (6249436496871/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373548883/10000000000 : ℝ)|^8253 ≤ (33288094896973/100000000000000 : ℝ)^6205
        have hw : |(4373548883/10000000000 : ℝ)|=(4373548883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1146715129/2500000000 : ℝ)|^8253 ≤ (35464722597763/100000000000000 : ℝ)^6205
        have hw : |(1146715129/2500000000 : ℝ)|=(1146715129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65162041/156250000 : ℝ)|^8253 ≤ (6249436496871/20000000000000 : ℝ)^6205
        have hw : |(65162041/156250000 : ℝ)|=(65162041/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1060_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4341/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1297/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2983/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16761/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4341/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16761/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4341/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16761/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4341/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16761/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4341/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16761/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4341/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16761/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4341/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4341/50000 : ℝ) ^ (2063/512 : ℝ) ≤ (2644563543875887/50000000000000000000 : ℝ) := by
    have hpowers : (4341/50000 : ℝ)^2063 ≤ (2644563543875887/50000000000000000000 : ℝ)^512 := by
      have hnat : (4341 : ℕ)^2063*50000000000000000000^512 ≤ 2644563543875887^512*50000^2063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4341 50000 2644563543875887 50000000000000000000 2063 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4341/50000 : ℝ)) (X := (2644563543875887/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hpowhi : (16761/100000 : ℝ) ^ (2063/512 : ℝ) ≤ (74898671786062769/100000000000000000000 : ℝ) := by
    have hpowers : (16761/100000 : ℝ)^2063 ≤ (74898671786062769/100000000000000000000 : ℝ)^512 := by
      have hnat : (16761 : ℕ)^2063*100000000000000000000^512 ≤ 74898671786062769^512*100000^2063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16761 100000 74898671786062769 100000000000000000000 2063 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16761/100000 : ℝ)) (X := (74898671786062769/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002644563543875887/25000000000000000000 : ℝ) ≤ (10000262523062699/10000000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (25002644563543875887/25000000000000000000 : ℝ)^512 ≤ (10000262523062699/10000000000000000 : ℝ)^2063 := by
      have hnat : (25002644563543875887 : ℕ)^512*10000000000000000^2063 ≤ 10000262523062699^2063*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002644563543875887 25000000000000000000 10000262523062699 10000000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000262523062699/10000000000000000 : ℝ)) (X := (25002644563543875887/25000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100080187798873814543/100000000000000000000 : ℝ) ≤ (5000994759649387/5000000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (100080187798873814543/100000000000000000000 : ℝ)^512 ≤ (5000994759649387/5000000000000000 : ℝ)^2063 := by
      have hnat : (100080187798873814543 : ℕ)^512*5000000000000000^2063 ≤ 5000994759649387^2063*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100080187798873814543 100000000000000000000 5000994759649387 5000000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000994759649387/5000000000000000 : ℝ)) (X := (100080187798873814543/100000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50074898671786062769/50000000000000000000 : ℝ) ≤ (10003716515534849/10000000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (50074898671786062769/50000000000000000000 : ℝ)^512 ≤ (10003716515534849/10000000000000000 : ℝ)^2063 := by
      have hnat : (50074898671786062769 : ℕ)^512*10000000000000000^2063 ≤ 10003716515534849^2063*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50074898671786062769 50000000000000000000 10003716515534849 10000000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003716515534849/10000000000000000 : ℝ)) (X := (50074898671786062769/50000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2644563543875887/50000000000000000000 : ℝ) ≤ ((26920711120393446307/26930000000000000000 : ℝ)+2*(23026616481/10772000000000 : ℝ)*(4341/50000 : ℝ))^(2063/512 : ℝ) := by
    rw [show (26920711120393446307/26930000000000000000 : ℝ)+2*(23026616481/10772000000000 : ℝ)*(4341/50000 : ℝ)=(10000262523062699/10000000000000000 : ℝ) by norm_num, show 1+2*(2644563543875887/50000000000000000000 : ℝ)=(25002644563543875887/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(74898671786062769/100000000000000000000 : ℝ)+(2644563543875887/50000000000000000000 : ℝ) ≤ ((26920711120393446307/26930000000000000000 : ℝ)+(23026616481/10772000000000 : ℝ)*((16761/100000 : ℝ)+(4341/50000 : ℝ)))^(2063/512 : ℝ) := by
    rw [show (26920711120393446307/26930000000000000000 : ℝ)+(23026616481/10772000000000 : ℝ)*((16761/100000 : ℝ)+(4341/50000 : ℝ))=(5000994759649387/5000000000000000 : ℝ) by norm_num, show 1+(74898671786062769/100000000000000000000 : ℝ)+(2644563543875887/50000000000000000000 : ℝ)=(100080187798873814543/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(74898671786062769/100000000000000000000 : ℝ) ≤ ((26920711120393446307/26930000000000000000 : ℝ)+2*(23026616481/10772000000000 : ℝ)*(16761/100000 : ℝ))^(2063/512 : ℝ) := by
    rw [show (26920711120393446307/26930000000000000000 : ℝ)+2*(23026616481/10772000000000 : ℝ)*(16761/100000 : ℝ)=(10003716515534849/10000000000000000 : ℝ) by norm_num, show 1+2*(74898671786062769/100000000000000000000 : ℝ)=(50074898671786062769/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26920711120393446307/26930000000000000000 : ℝ)*(X 1 0+X 2 0)+(23026616481/10772000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (4341/50000 : ℝ)) (hi := (16761/100000 : ℝ)) (c := (26920711120393446307/26930000000000000000 : ℝ)) (alpha := (23026616481/10772000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26920711120393446307/26930000000000000000 : ℝ)*(X 0 1+X 2 1)+(23026616481/10772000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (4341/50000 : ℝ)) (hi := (16761/100000 : ℝ)) (c := (26920711120393446307/26930000000000000000 : ℝ)) (alpha := (23026616481/10772000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26920711120393446307/26930000000000000000 : ℝ)*(X 0 2+X 1 2)+(23026616481/10772000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (4341/50000 : ℝ)) (hi := (16761/100000 : ℝ)) (c := (26920711120393446307/26930000000000000000 : ℝ)) (alpha := (23026616481/10772000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1100951369/5000000000 : ℝ)*X 0 0+(5438246153/10000000000 : ℝ)*X 0 1+(5223711169/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355848271/10000000000 : ℝ)*X 1 0+(-72243079/312500000 : ℝ)*X 1 1+(5223711209/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355848249/10000000000 : ℝ)*X 2 0+(652963913/1250000000 : ℝ)*X 2 1+(-18060769/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2186752301/5000000000 : ℝ)*X 0 0+(104215789/250000000 : ℝ)*X 0 1+(2294294579/5000000000 : ℝ)*X 0 2+(2186752301/5000000000 : ℝ)*X 1 0+(104215789/250000000 : ℝ)*X 1 1+(2294294579/5000000000 : ℝ)*X 1 2+(2186752301/5000000000 : ℝ)*X 2 0+(104215789/250000000 : ℝ)*X 2 1+(2294294579/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-550481407/2500000000 : ℝ)*X 0 0+(5224594801/10000000000 : ℝ)*X 0 1+(5437357149/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212073319/400000000 : ℝ)*X 1 0+(-2098131653/10000000000 : ℝ)*X 1 1+(679669721/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301832613/10000000000 : ℝ)*X 2 0+(2718678813/5000000000 : ℝ)*X 2 1+(-2098132339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4373548883/10000000000 : ℝ)*X 0 0+(1146715129/2500000000 : ℝ)*X 0 1+(65162041/156250000 : ℝ)*X 0 2+(4373548883/10000000000 : ℝ)*X 1 0+(1146715129/2500000000 : ℝ)*X 1 1+(65162041/156250000 : ℝ)*X 1 2+(4373548883/10000000000 : ℝ)*X 2 0+(1146715129/2500000000 : ℝ)*X 2 1+(65162041/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (557181768630008877810896211/134650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1043026401/100000000000000 : ℝ)*(base19) + (434707997/50000000000000 : ℝ)*(base23) + (82728281/100000000000000 : ℝ)*(lower2) + (108417361/100000000000000 : ℝ)*(upper3) + (19042229/25000000000000 : ℝ)*(upper5) + (352124627233509/10000000000000 : ℝ)*(major0) + (352124627233509/10000000000000 : ℝ)*(major1) + (352124627233509/10000000000000 : ℝ)*(major2) + (4661263093921107/100000000000000 : ℝ)*(sp0) + (582660145871463/12500000000000 : ℝ)*(sp1) + (4661281340582111/100000000000000 : ℝ)*(sp2) + (1190600505627891/50000000000000 : ℝ)*(sp3) + (19116076999/100000000000000 : ℝ)*(sp4) + (9185482931/100000000000000 : ℝ)*(sp7) + (297651274592339/12500000000000 : ℝ)*(f.failure) + (932256441999621/20000000000000 : ℝ)*(f.sum) + (8491549668643/2693000000000000000000000000 : ℝ)*base65 + (1854145302784598737/269300000000000000000000000000000 : ℝ)*base68 + (2403820143560998737/269300000000000000000000000000000 : ℝ)*base70 + (716031616679901263/269300000000000000000000000000000 : ℝ)*base71 + (2614315607561/1346500000000000000000000000 : ℝ)*base74 + (3848579841040401263/269300000000000000000000000000000 : ℝ)*base75 + (1075345180728401263/269300000000000000000000000000000 : ℝ)*base77 + (2225332504657201263/269300000000000000000000000000000 : ℝ)*base79 + (6422540692157/1346500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (12971791/1250000000000000000000 : ℝ)*base90 + (12971791/1250000000000000000000 : ℝ)*base92 + (12971791/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2733383487814812443910323127/336625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (535924979/25000000000000 : ℝ)*(base19) + (443900977/25000000000000 : ℝ)*(base23) + (14088567/100000000000000 : ℝ)*(upper2) + (78653853/20000000000000 : ℝ)*(upper3) + (887635961347087/25000000000000 : ℝ)*(major0) + (887635961347087/25000000000000 : ℝ)*(major1) + (887635961347087/25000000000000 : ℝ)*(major2) + (20495493581/50000000000000 : ℝ)*(sp1) + (8437806707/25000000000000 : ℝ)*(sp2) + (24219329/25000000000000 : ℝ)*(sp3) + (4700065010792429/100000000000000 : ℝ)*(sp4) + (4700021876105351/100000000000000 : ℝ)*(sp5) + (4700029483961693/100000000000000 : ℝ)*(sp6) + (120051115622071/5000000000000 : ℝ)*(sp7) + (150063900582421/6250000000000 : ℝ)*(f.failure) + (4700065010792429/100000000000000 : ℝ)*(f.sum) + (143737716173/26930000000000000000000000 : ℝ)*base66 + (327956562458607709/673250000000000000000000000000000 : ℝ)*base67 + (1291737259706392291/673250000000000000000000000000000 : ℝ)*base70 + (2771207129801107709/673250000000000000000000000000000 : ℝ)*base71 + (6725008693173/2693000000000000000000000000 : ℝ)*base74 + (3972948992197642291/673250000000000000000000000000000 : ℝ)*base76 + (3994330495904392291/673250000000000000000000000000000 : ℝ)*base78 + (5040217730639642291/673250000000000000000000000000000 : ℝ)*base80 + (186620766827/538600000000000000000000000 : ℝ)*base81 + (5577351/625000000000000000000 : ℝ)*base89 + (5577351/625000000000000000000 : ℝ)*base91 + (5577351/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1060_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4341/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1297/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2983/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1060_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1060_s4_0 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-110281953/500000000 : ℝ)*x 0 + (5406153299/10000000000 : ℝ)*x 1 + (1050672711/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110281953/500000000 : ℝ)^8253 ≤ (13392565591293/100000000000000 : ℝ)^6205 := by
    have hnat : (110281953 : ℕ)^8253*100000000000000^6205 ≤ 13392565591293^6205*500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110281953 500000000 13392565591293 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406153299/10000000000 : ℝ)^8253 ≤ (44129239945521/100000000000000 : ℝ)^6205 := by
    have hnat : (5406153299 : ℕ)^8253*100000000000000^6205 ≤ 44129239945521^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406153299 10000000000 44129239945521 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050672711/2000000000 : ℝ)^8253 ≤ (21239097222663/50000000000000 : ℝ)^6205 := by
    have hnat : (1050672711 : ℕ)^8253*50000000000000^6205 ≤ 21239097222663^6205*2000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050672711 2000000000 21239097222663 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-110281953/500000000 : ℝ), (5406153299/10000000000 : ℝ), (1050672711/2000000000 : ℝ)] ![(13392565591293/100000000000000 : ℝ), (44129239945521/100000000000000 : ℝ), (21239097222663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-110281953/500000000 : ℝ)|^8253 ≤ (13392565591293/100000000000000 : ℝ)^6205
        have hw : |(-110281953/500000000 : ℝ)|=(110281953/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406153299/10000000000 : ℝ)|^8253 ≤ (44129239945521/100000000000000 : ℝ)^6205
        have hw : |(5406153299/10000000000 : ℝ)|=(5406153299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050672711/2000000000 : ℝ)|^8253 ≤ (21239097222663/50000000000000 : ℝ)^6205
        have hw : |(1050672711/2000000000 : ℝ)|=(1050672711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s4_1 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (83560999/156250000 : ℝ)*x 0 + (-142709873/625000000 : ℝ)*x 1 + (5253363531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83560999/156250000 : ℝ)^8253 ≤ (43497956289099/100000000000000 : ℝ)^6205 := by
    have hnat : (83560999 : ℕ)^8253*100000000000000^6205 ≤ 43497956289099^6205*156250000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83560999 156250000 43497956289099 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142709873/625000000 : ℝ)^8253 ≤ (14023849510733/100000000000000 : ℝ)^6205 := by
    have hnat : (142709873 : ℕ)^8253*100000000000000^6205 ≤ 14023849510733^6205*625000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142709873 625000000 14023849510733 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253363531/10000000000 : ℝ)^8253 ≤ (42478194187213/100000000000000 : ℝ)^6205 := by
    have hnat : (5253363531 : ℕ)^8253*100000000000000^6205 ≤ 42478194187213^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253363531 10000000000 42478194187213 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83560999/156250000 : ℝ), (-142709873/625000000 : ℝ), (5253363531/10000000000 : ℝ)] ![(43497956289099/100000000000000 : ℝ), (14023849510733/100000000000000 : ℝ), (42478194187213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83560999/156250000 : ℝ)|^8253 ≤ (43497956289099/100000000000000 : ℝ)^6205
        have hw : |(83560999/156250000 : ℝ)|=(83560999/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-142709873/625000000 : ℝ)|^8253 ≤ (14023849510733/100000000000000 : ℝ)^6205
        have hw : |(-142709873/625000000 : ℝ)|=(142709873/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253363531/10000000000 : ℝ)|^8253 ≤ (42478194187213/100000000000000 : ℝ)^6205
        have hw : |(5253363531/10000000000 : ℝ)|=(5253363531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s4_2 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347904023/10000000000 : ℝ)*x 0 + (328335219/625000000 : ℝ)*x 1 + (-2283357889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347904023/10000000000 : ℝ)^8253 ≤ (43497957230283/100000000000000 : ℝ)^6205 := by
    have hnat : (5347904023 : ℕ)^8253*100000000000000^6205 ≤ 43497957230283^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347904023 10000000000 43497957230283 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328335219/625000000 : ℝ)^8253 ≤ (10619548474209/25000000000000 : ℝ)^6205 := by
    have hnat : (328335219 : ℕ)^8253*25000000000000^6205 ≤ 10619548474209^6205*625000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328335219 625000000 10619548474209 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2283357889/10000000000 : ℝ)^8253 ≤ (1402384886539/10000000000000 : ℝ)^6205 := by
    have hnat : (2283357889 : ℕ)^8253*10000000000000^6205 ≤ 1402384886539^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283357889 10000000000 1402384886539 10000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347904023/10000000000 : ℝ), (328335219/625000000 : ℝ), (-2283357889/10000000000 : ℝ)] ![(43497957230283/100000000000000 : ℝ), (10619548474209/25000000000000 : ℝ), (1402384886539/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347904023/10000000000 : ℝ)|^8253 ≤ (43497957230283/100000000000000 : ℝ)^6205
        have hw : |(5347904023/10000000000 : ℝ)|=(5347904023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328335219/625000000 : ℝ)|^8253 ≤ (10619548474209/25000000000000 : ℝ)^6205
        have hw : |(328335219/625000000 : ℝ)|=(328335219/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2283357889/10000000000 : ℝ)|^8253 ≤ (1402384886539/10000000000000 : ℝ)^6205
        have hw : |(-2283357889/10000000000 : ℝ)|=(2283357889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s4_3 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4375727079/10000000000 : ℝ)*x 0 + (2114386777/5000000000 : ℝ)*x 1 + (4527863599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375727079/10000000000 : ℝ)^8253 ≤ (33310147388341/100000000000000 : ℝ)^6205 := by
    have hnat : (4375727079 : ℕ)^8253*100000000000000^6205 ≤ 33310147388341^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375727079 10000000000 33310147388341 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114386777/5000000000 : ℝ)^8253 ≤ (31830547432819/100000000000000 : ℝ)^6205 := by
    have hnat : (2114386777 : ℕ)^8253*100000000000000^6205 ≤ 31830547432819^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114386777 5000000000 31830547432819 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4527863599/10000000000 : ℝ)^8253 ≤ (34859305166533/100000000000000 : ℝ)^6205 := by
    have hnat : (4527863599 : ℕ)^8253*100000000000000^6205 ≤ 34859305166533^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527863599 10000000000 34859305166533 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375727079/10000000000 : ℝ), (2114386777/5000000000 : ℝ), (4527863599/10000000000 : ℝ)] ![(33310147388341/100000000000000 : ℝ), (31830547432819/100000000000000 : ℝ), (34859305166533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375727079/10000000000 : ℝ)|^8253 ≤ (33310147388341/100000000000000 : ℝ)^6205
        have hw : |(4375727079/10000000000 : ℝ)|=(4375727079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2114386777/5000000000 : ℝ)|^8253 ≤ (31830547432819/100000000000000 : ℝ)^6205
        have hw : |(2114386777/5000000000 : ℝ)|=(2114386777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4527863599/10000000000 : ℝ)|^8253 ≤ (34859305166533/100000000000000 : ℝ)^6205
        have hw : |(4527863599/10000000000 : ℝ)|=(4527863599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s4_4 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-551411723/2500000000 : ℝ)*x 0 + (5253812697/10000000000 : ℝ)*x 1 + (5405702549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (551411723/2500000000 : ℝ)^8253 ≤ (3348157210753/25000000000000 : ℝ)^6205 := by
    have hnat : (551411723 : ℕ)^8253*25000000000000^6205 ≤ 3348157210753^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551411723 2500000000 3348157210753 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253812697/10000000000 : ℝ)^8253 ≤ (21241512452423/50000000000000 : ℝ)^6205 := by
    have hnat : (5253812697 : ℕ)^8253*50000000000000^6205 ≤ 21241512452423^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253812697 10000000000 21241512452423 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405702549/10000000000 : ℝ)^8253 ≤ (352994769913/800000000000 : ℝ)^6205 := by
    have hnat : (5405702549 : ℕ)^8253*800000000000^6205 ≤ 352994769913^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405702549 10000000000 352994769913 800000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-551411723/2500000000 : ℝ), (5253812697/10000000000 : ℝ), (5405702549/10000000000 : ℝ)] ![(3348157210753/25000000000000 : ℝ), (21241512452423/50000000000000 : ℝ), (352994769913/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-551411723/2500000000 : ℝ)|^8253 ≤ (3348157210753/25000000000000 : ℝ)^6205
        have hw : |(-551411723/2500000000 : ℝ)|=(551411723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253812697/10000000000 : ℝ)|^8253 ≤ (21241512452423/50000000000000 : ℝ)^6205
        have hw : |(5253812697/10000000000 : ℝ)|=(5253812697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405702549/10000000000 : ℝ)|^8253 ≤ (352994769913/800000000000 : ℝ)^6205
        have hw : |(5405702549/10000000000 : ℝ)|=(5405702549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s4_5 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327359959/2500000000 : ℝ)*x 0 + (-532754519/2500000000 : ℝ)*x 1 + (2702851397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327359959/2500000000 : ℝ)^8253 ≤ (1077058459129/2500000000000 : ℝ)^6205 := by
    have hnat : (1327359959 : ℕ)^8253*2500000000000^6205 ≤ 1077058459129^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327359959 2500000000 1077058459129 2500000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (532754519/2500000000 : ℝ)^8253 ≤ (1599164089693/12500000000000 : ℝ)^6205 := by
    have hnat : (532754519 : ℕ)^8253*12500000000000^6205 ≤ 1599164089693^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532754519 2500000000 1599164089693 12500000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702851397/5000000000 : ℝ)^8253 ≤ (22062174449503/50000000000000 : ℝ)^6205 := by
    have hnat : (2702851397 : ℕ)^8253*50000000000000^6205 ≤ 22062174449503^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702851397 5000000000 22062174449503 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327359959/2500000000 : ℝ), (-532754519/2500000000 : ℝ), (2702851397/5000000000 : ℝ)] ![(1077058459129/2500000000000 : ℝ), (1599164089693/12500000000000 : ℝ), (22062174449503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327359959/2500000000 : ℝ)|^8253 ≤ (1077058459129/2500000000000 : ℝ)^6205
        have hw : |(1327359959/2500000000 : ℝ)|=(1327359959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-532754519/2500000000 : ℝ)|^8253 ≤ (1599164089693/12500000000000 : ℝ)^6205
        have hw : |(-532754519/2500000000 : ℝ)|=(532754519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702851397/5000000000 : ℝ)|^8253 ≤ (22062174449503/50000000000000 : ℝ)^6205
        have hw : |(2702851397/5000000000 : ℝ)|=(2702851397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s4_6 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1061887903/2000000000 : ℝ)*x 0 + (5405702599/10000000000 : ℝ)*x 1 + (-85240751/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061887903/2000000000 : ℝ)^8253 ≤ (43082334900779/100000000000000 : ℝ)^6205 := by
    have hnat : (1061887903 : ℕ)^8253*100000000000000^6205 ≤ 43082334900779^6205*2000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061887903 2000000000 43082334900779 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405702599/10000000000 : ℝ)^8253 ≤ (22062173390979/50000000000000 : ℝ)^6205 := by
    have hnat : (5405702599 : ℕ)^8253*50000000000000^6205 ≤ 22062173390979^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405702599 10000000000 22062173390979 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85240751/400000000 : ℝ)^8253 ≤ (199895598421/1562500000000 : ℝ)^6205 := by
    have hnat : (85240751 : ℕ)^8253*1562500000000^6205 ≤ 199895598421^6205*400000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85240751 400000000 199895598421 1562500000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061887903/2000000000 : ℝ), (5405702599/10000000000 : ℝ), (-85240751/400000000 : ℝ)] ![(43082334900779/100000000000000 : ℝ), (22062173390979/50000000000000 : ℝ), (199895598421/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061887903/2000000000 : ℝ)|^8253 ≤ (43082334900779/100000000000000 : ℝ)^6205
        have hw : |(1061887903/2000000000 : ℝ)|=(1061887903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405702599/10000000000 : ℝ)|^8253 ≤ (22062173390979/50000000000000 : ℝ)^6205
        have hw : |(5405702599/10000000000 : ℝ)|=(5405702599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85240751/400000000 : ℝ)|^8253 ≤ (199895598421/1562500000000 : ℝ)^6205
        have hw : |(-85240751/400000000 : ℝ)|=(85240751/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s4_7 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (546967887/1250000000 : ℝ)*x 0 + (905396853/2000000000 : ℝ)*x 1 + (4229656689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546967887/1250000000 : ℝ)^8253 ≤ (3331030956107/10000000000000 : ℝ)^6205 := by
    have hnat : (546967887 : ℕ)^8253*10000000000000^6205 ≤ 3331030956107^6205*1250000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546967887 1250000000 3331030956107 10000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (905396853/2000000000 : ℝ)^8253 ≤ (87125752921/250000000000 : ℝ)^6205 := by
    have hnat : (905396853 : ℕ)^8253*250000000000^6205 ≤ 87125752921^6205*2000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905396853 2000000000 87125752921 250000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4229656689/10000000000 : ℝ)^8253 ≤ (31839389255497/100000000000000 : ℝ)^6205 := by
    have hnat : (4229656689 : ℕ)^8253*100000000000000^6205 ≤ 31839389255497^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229656689 10000000000 31839389255497 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546967887/1250000000 : ℝ), (905396853/2000000000 : ℝ), (4229656689/10000000000 : ℝ)] ![(3331030956107/10000000000000 : ℝ), (87125752921/250000000000 : ℝ), (31839389255497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546967887/1250000000 : ℝ)|^8253 ≤ (3331030956107/10000000000000 : ℝ)^6205
        have hw : |(546967887/1250000000 : ℝ)|=(546967887/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(905396853/2000000000 : ℝ)|^8253 ≤ (87125752921/250000000000 : ℝ)^6205
        have hw : |(905396853/2000000000 : ℝ)|=(905396853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4229656689/10000000000 : ℝ)|^8253 ≤ (31839389255497/100000000000000 : ℝ)^6205
        have hw : |(4229656689/10000000000 : ℝ)|=(4229656689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1060_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2983/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1297/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11009/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3561/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2983/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1297/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2983/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1297/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2983/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1297/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2983/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1297/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2983/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1297/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2983/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1297/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1297/12500 : ℝ) ^ (2063/512 : ℝ) ≤ (10846574539086169/100000000000000000000 : ℝ) := by
    have hpowers : (1297/12500 : ℝ)^2063 ≤ (10846574539086169/100000000000000000000 : ℝ)^512 := by
      have hnat : (1297 : ℕ)^2063*100000000000000000000^512 ≤ 10846574539086169^512*12500^2063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1297 12500 10846574539086169 100000000000000000000 2063 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1297/12500 : ℝ)) (X := (10846574539086169/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2983/20000 : ℝ) ^ (2063/512 : ℝ) ≤ (46803978876593033/100000000000000000000 : ℝ) := by
    have hpowers : (2983/20000 : ℝ)^2063 ≤ (46803978876593033/100000000000000000000 : ℝ)^512 := by
      have hnat : (2983 : ℕ)^2063*100000000000000000000^512 ≤ 46803978876593033^512*20000^2063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2983 20000 46803978876593033 100000000000000000000 2063 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2983/20000 : ℝ)) (X := (46803978876593033/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010846574539086169/50000000000000000000 : ℝ) ≤ (312516823174253/312500000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (50010846574539086169/50000000000000000000 : ℝ)^512 ≤ (312516823174253/312500000000000 : ℝ)^2063 := by
      have hnat : (50010846574539086169 : ℕ)^512*312500000000000^2063 ≤ 312516823174253^2063*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010846574539086169 50000000000000000000 312516823174253 312500000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312516823174253/312500000000000 : ℝ)) (X := (50010846574539086169/50000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50028825276707839601/50000000000000000000 : ℝ) ≤ (1250178809311377/1250000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (50028825276707839601/50000000000000000000 : ℝ)^512 ≤ (1250178809311377/1250000000000000 : ℝ)^2063 := by
      have hnat : (50028825276707839601 : ℕ)^512*1250000000000000^2063 ≤ 1250178809311377^2063*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028825276707839601 50000000000000000000 1250178809311377 1250000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250178809311377/1250000000000000 : ℝ)) (X := (50028825276707839601/50000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50046803978876593033/50000000000000000000 : ℝ) ≤ (625145162962871/625000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (50046803978876593033/50000000000000000000 : ℝ)^512 ≤ (625145162962871/625000000000000 : ℝ)^2063 := by
      have hnat : (50046803978876593033 : ℕ)^512*625000000000000^2063 ≤ 625145162962871^2063*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50046803978876593033 50000000000000000000 625145162962871 625000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625145162962871/625000000000000 : ℝ)) (X := (50046803978876593033/50000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10846574539086169/100000000000000000000 : ℝ) ≤ ((83407959540741691/83437500000000000 : ℝ)+2*(1311960169/667500000000 : ℝ)*(1297/12500 : ℝ))^(2063/512 : ℝ) := by
    rw [show (83407959540741691/83437500000000000 : ℝ)+2*(1311960169/667500000000 : ℝ)*(1297/12500 : ℝ)=(312516823174253/312500000000000 : ℝ) by norm_num, show 1+2*(10846574539086169/100000000000000000000 : ℝ)=(50010846574539086169/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(46803978876593033/100000000000000000000 : ℝ)+(10846574539086169/100000000000000000000 : ℝ) ≤ ((83407959540741691/83437500000000000 : ℝ)+(1311960169/667500000000 : ℝ)*((2983/20000 : ℝ)+(1297/12500 : ℝ)))^(2063/512 : ℝ) := by
    rw [show (83407959540741691/83437500000000000 : ℝ)+(1311960169/667500000000 : ℝ)*((2983/20000 : ℝ)+(1297/12500 : ℝ))=(1250178809311377/1250000000000000 : ℝ) by norm_num, show 1+(46803978876593033/100000000000000000000 : ℝ)+(10846574539086169/100000000000000000000 : ℝ)=(50028825276707839601/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(46803978876593033/100000000000000000000 : ℝ) ≤ ((83407959540741691/83437500000000000 : ℝ)+2*(1311960169/667500000000 : ℝ)*(2983/20000 : ℝ))^(2063/512 : ℝ) := by
    rw [show (83407959540741691/83437500000000000 : ℝ)+2*(1311960169/667500000000 : ℝ)*(2983/20000 : ℝ)=(625145162962871/625000000000000 : ℝ) by norm_num, show 1+2*(46803978876593033/100000000000000000000 : ℝ)=(50046803978876593033/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (83407959540741691/83437500000000000 : ℝ)*(X 1 0+X 2 0)+(1311960169/667500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (1297/12500 : ℝ)) (hi := (2983/20000 : ℝ)) (c := (83407959540741691/83437500000000000 : ℝ)) (alpha := (1311960169/667500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (83407959540741691/83437500000000000 : ℝ)*(X 0 1+X 2 1)+(1311960169/667500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (1297/12500 : ℝ)) (hi := (2983/20000 : ℝ)) (c := (83407959540741691/83437500000000000 : ℝ)) (alpha := (1311960169/667500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (83407959540741691/83437500000000000 : ℝ)*(X 0 2+X 1 2)+(1311960169/667500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (1297/12500 : ℝ)) (hi := (2983/20000 : ℝ)) (c := (83407959540741691/83437500000000000 : ℝ)) (alpha := (1311960169/667500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-110281953/500000000 : ℝ)*X 0 0+(5406153299/10000000000 : ℝ)*X 0 1+(1050672711/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((83560999/156250000 : ℝ)*X 1 0+(-142709873/625000000 : ℝ)*X 1 1+(5253363531/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347904023/10000000000 : ℝ)*X 2 0+(328335219/625000000 : ℝ)*X 2 1+(-2283357889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4375727079/10000000000 : ℝ)*X 0 0+(2114386777/5000000000 : ℝ)*X 0 1+(4527863599/10000000000 : ℝ)*X 0 2+(4375727079/10000000000 : ℝ)*X 1 0+(2114386777/5000000000 : ℝ)*X 1 1+(4527863599/10000000000 : ℝ)*X 1 2+(4375727079/10000000000 : ℝ)*X 2 0+(2114386777/5000000000 : ℝ)*X 2 1+(4527863599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-551411723/2500000000 : ℝ)*X 0 0+(5253812697/10000000000 : ℝ)*X 0 1+(5405702549/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327359959/2500000000 : ℝ)*X 1 0+(-532754519/2500000000 : ℝ)*X 1 1+(2702851397/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061887903/2000000000 : ℝ)*X 2 0+(5405702599/10000000000 : ℝ)*X 2 1+(-85240751/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((546967887/1250000000 : ℝ)*X 0 0+(905396853/2000000000 : ℝ)*X 0 1+(4229656689/10000000000 : ℝ)*X 0 2+(546967887/1250000000 : ℝ)*X 1 0+(905396853/2000000000 : ℝ)*X 1 1+(4229656689/10000000000 : ℝ)*X 1 2+(546967887/1250000000 : ℝ)*X 2 0+(905396853/2000000000 : ℝ)*X 2 1+(4229656689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (410688195000844571010509/55625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61586887/5000000000000 : ℝ)*(base19) + (276323187/25000000000000 : ℝ)*(base23) + (124563027/100000000000000 : ℝ)*(lower2) + (137606521/100000000000000 : ℝ)*(upper3) + (44161947/50000000000000 : ℝ)*(upper5) + (197770001881963/4000000000000 : ℝ)*(major0) + (197770001881963/4000000000000 : ℝ)*(major1) + (197770001881963/4000000000000 : ℝ)*(major2) + (1308993641185377/20000000000000 : ℝ)*(sp0) + (6544995289107329/100000000000000 : ℝ)*(sp1) + (3272497707776161/50000000000000 : ℝ)*(sp2) + (417935970583743/12500000000000 : ℝ)*(sp3) + (3539364773/12500000000000 : ℝ)*(sp4) + (3890619461/25000000000000 : ℝ)*(sp7) + (3343503327147787/100000000000000 : ℝ)*(f.failure) + (6544996520845069/100000000000000 : ℝ)*(f.sum) + (187164517981/66750000000000000000000000 : ℝ)*base66 + (744662995201061/111250000000000000000000000000 : ℝ)*base67 + (219097673831061/111250000000000000000000000000 : ℝ)*base69 + (889275307694811/111250000000000000000000000000 : ℝ)*base71 + (219569760097/66750000000000000000000000 : ℝ)*base74 + (320947993566061/111250000000000000000000000000 : ℝ)*base75 + (121066861297311/111250000000000000000000000000 : ℝ)*base77 + (599941264580189/111250000000000000000000000000 : ℝ)*base80 + (281859196381/133500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (63670503/10000000000000000000000 : ℝ)*base90 + (63670503/10000000000000000000000 : ℝ)*base92 + (63670503/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (624180176720174452959457/139062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (379220801/50000000000000 : ℝ)*(base19) + (814570863/100000000000000 : ℝ)*(base23) + (170091071/100000000000000 : ℝ)*(lower3) + (1337207/400000000000 : ℝ)*(lower4) + (248675155300601/5000000000000 : ℝ)*(major0) + (248675155300601/5000000000000 : ℝ)*(major1) + (248675155300601/5000000000000 : ℝ)*(major2) + (4313643221/100000000000000 : ℝ)*(sp0) + (24470265643/50000000000000 : ℝ)*(sp1) + (24719540971/100000000000000 : ℝ)*(sp2) + (6583716311278303/100000000000000 : ℝ)*(sp4) + (1316734185189727/20000000000000 : ℝ)*(sp5) + (658369509080969/10000000000000 : ℝ)*(sp6) + (210205339842893/6250000000000 : ℝ)*(sp7) + (210205339842893/6250000000000 : ℝ)*(f.failure) + (1645930156230381/25000000000000 : ℝ)*(f.sum) + (9695783017/33375000000000000000000000 : ℝ)*base65 + (105282864128639/69531250000000000000000000000 : ℝ)*base68 + (1705842355949/1086425781250000000000000000 : ℝ)*base69 + (583395852704153/139062500000000000000000000000 : ℝ)*base72 + (424193830141/66750000000000000000000000 : ℝ)*base74 + (1260313645302097/139062500000000000000000000000 : ℝ)*base75 + (2241956518855181/278125000000000000000000000000 : ℝ)*base78 + (272947560016139/69531250000000000000000000000 : ℝ)*base80 + (119856567419/267000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (8265583/625000000000000000000 : ℝ)*base89 + (8265583/625000000000000000000 : ℝ)*base91 + (8265583/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1060_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2983/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1297/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11009/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3561/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1060_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1060_s5_0 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-17651909/80000000 : ℝ)*x 0 + (5397171089/10000000000 : ℝ)*x 1 + (5261788441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17651909/80000000 : ℝ)^8253 ≤ (13399427163093/100000000000000 : ℝ)^6205 := by
    have hnat : (17651909 : ℕ)^8253*100000000000000^6205 ≤ 13399427163093^6205*80000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17651909 80000000 13399427163093 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397171089/10000000000 : ℝ)^8253 ≤ (44031747219381/100000000000000 : ℝ)^6205 := by
    have hnat : (5397171089 : ℕ)^8253*100000000000000^6205 ≤ 44031747219381^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397171089 10000000000 44031747219381 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261788441/10000000000 : ℝ)^8253 ≤ (42568825611269/100000000000000 : ℝ)^6205 := by
    have hnat : (5261788441 : ℕ)^8253*100000000000000^6205 ≤ 42568825611269^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261788441 10000000000 42568825611269 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17651909/80000000 : ℝ), (5397171089/10000000000 : ℝ), (5261788441/10000000000 : ℝ)] ![(13399427163093/100000000000000 : ℝ), (44031747219381/100000000000000 : ℝ), (42568825611269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17651909/80000000 : ℝ)|^8253 ≤ (13399427163093/100000000000000 : ℝ)^6205
        have hw : |(-17651909/80000000 : ℝ)|=(17651909/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397171089/10000000000 : ℝ)|^8253 ≤ (44031747219381/100000000000000 : ℝ)^6205
        have hw : |(5397171089/10000000000 : ℝ)|=(5397171089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261788441/10000000000 : ℝ)|^8253 ≤ (42568825611269/100000000000000 : ℝ)^6205
        have hw : |(5261788441/10000000000 : ℝ)|=(5261788441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s5_1 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672833933/5000000000 : ℝ)*x 0 + (-2275219563/10000000000 : ℝ)*x 1 + (5261788423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672833933/5000000000 : ℝ)^8253 ≤ (8694753537757/20000000000000 : ℝ)^6205 := by
    have hnat : (2672833933 : ℕ)^8253*20000000000000^6205 ≤ 8694753537757^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672833933 5000000000 8694753537757 20000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2275219563/10000000000 : ℝ)^8253 ≤ (13957406872597/100000000000000 : ℝ)^6205 := by
    have hnat : (2275219563 : ℕ)^8253*100000000000000^6205 ≤ 13957406872597^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2275219563 10000000000 13957406872597 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261788423/10000000000 : ℝ)^8253 ≤ (21284412708791/50000000000000 : ℝ)^6205 := by
    have hnat : (5261788423 : ℕ)^8253*50000000000000^6205 ≤ 21284412708791^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261788423 10000000000 21284412708791 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672833933/5000000000 : ℝ), (-2275219563/10000000000 : ℝ), (5261788423/10000000000 : ℝ)] ![(8694753537757/20000000000000 : ℝ), (13957406872597/100000000000000 : ℝ), (21284412708791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672833933/5000000000 : ℝ)|^8253 ≤ (8694753537757/20000000000000 : ℝ)^6205
        have hw : |(2672833933/5000000000 : ℝ)|=(2672833933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2275219563/10000000000 : ℝ)|^8253 ≤ (13957406872597/100000000000000 : ℝ)^6205
        have hw : |(-2275219563/10000000000 : ℝ)|=(2275219563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261788423/10000000000 : ℝ)|^8253 ≤ (21284412708791/50000000000000 : ℝ)^6205
        have hw : |(5261788423/10000000000 : ℝ)|=(5261788423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s5_2 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534566779/1000000000 : ℝ)*x 0 + (5261788457/10000000000 : ℝ)*x 1 + (-2275219619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534566779/1000000000 : ℝ)^8253 ≤ (8694753373343/20000000000000 : ℝ)^6205 := by
    have hnat : (534566779 : ℕ)^8253*20000000000000^6205 ≤ 8694753373343^6205*1000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534566779 1000000000 8694753373343 20000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261788457/10000000000 : ℝ)^8253 ≤ (8513765156687/20000000000000 : ℝ)^6205 := by
    have hnat : (5261788457 : ℕ)^8253*20000000000000^6205 ≤ 8513765156687^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261788457 10000000000 8513765156687 20000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2275219619/10000000000 : ℝ)^8253 ≤ (3489351832379/25000000000000 : ℝ)^6205 := by
    have hnat : (2275219619 : ℕ)^8253*25000000000000^6205 ≤ 3489351832379^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2275219619 10000000000 3489351832379 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534566779/1000000000 : ℝ), (5261788457/10000000000 : ℝ), (-2275219619/10000000000 : ℝ)] ![(8694753373343/20000000000000 : ℝ), (8513765156687/20000000000000 : ℝ), (3489351832379/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534566779/1000000000 : ℝ)|^8253 ≤ (8694753373343/20000000000000 : ℝ)^6205
        have hw : |(534566779/1000000000 : ℝ)|=(534566779/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261788457/10000000000 : ℝ)|^8253 ≤ (8513765156687/20000000000000 : ℝ)^6205
        have hw : |(5261788457/10000000000 : ℝ)|=(5261788457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2275219619/10000000000 : ℝ)|^8253 ≤ (3489351832379/25000000000000 : ℝ)^6205
        have hw : |(-2275219619/10000000000 : ℝ)|=(2275219619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s5_3 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (10940547/25000000 : ℝ)*x 0 + (21228731/50000000 : ℝ)*x 1 + (1127690407/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10940547/25000000 : ℝ)^8253 ≤ (33315126171329/100000000000000 : ℝ)^6205 := by
    have hnat : (10940547 : ℕ)^8253*100000000000000^6205 ≤ 33315126171329^6205*25000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10940547 25000000 33315126171329 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21228731/50000000 : ℝ)^8253 ≤ (32000581755911/100000000000000 : ℝ)^6205 := by
    have hnat : (21228731 : ℕ)^8253*100000000000000^6205 ≤ 32000581755911^6205*50000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21228731 50000000 32000581755911 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127690407/2500000000 : ℝ)^8253 ≤ (17342146025061/50000000000000 : ℝ)^6205 := by
    have hnat : (1127690407 : ℕ)^8253*50000000000000^6205 ≤ 17342146025061^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127690407 2500000000 17342146025061 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10940547/25000000 : ℝ), (21228731/50000000 : ℝ), (1127690407/2500000000 : ℝ)] ![(33315126171329/100000000000000 : ℝ), (32000581755911/100000000000000 : ℝ), (17342146025061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10940547/25000000 : ℝ)|^8253 ≤ (33315126171329/100000000000000 : ℝ)^6205
        have hw : |(10940547/25000000 : ℝ)|=(10940547/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21228731/50000000 : ℝ)|^8253 ≤ (32000581755911/100000000000000 : ℝ)^6205
        have hw : |(21228731/50000000 : ℝ)|=(21228731/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1127690407/2500000000 : ℝ)|^8253 ≤ (17342146025061/50000000000000 : ℝ)^6205
        have hw : |(1127690407/2500000000 : ℝ)|=(1127690407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s5_4 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1103247197/5000000000 : ℝ)*x 0 + (5262140999/10000000000 : ℝ)*x 1 + (1349204293/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103247197/5000000000 : ℝ)^8253 ≤ (13399473759811/100000000000000 : ℝ)^6205 := by
    have hnat : (1103247197 : ℕ)^8253*100000000000000^6205 ≤ 13399473759811^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103247197 5000000000 13399473759811 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262140999/10000000000 : ℝ)^8253 ≤ (10643154829427/25000000000000 : ℝ)^6205 := by
    have hnat : (5262140999 : ℕ)^8253*25000000000000^6205 ≤ 10643154829427^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262140999 10000000000 10643154829427 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349204293/2500000000 : ℝ)^8253 ≤ (44027906907313/100000000000000 : ℝ)^6205 := by
    have hnat : (1349204293 : ℕ)^8253*100000000000000^6205 ≤ 44027906907313^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349204293 2500000000 44027906907313 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1103247197/5000000000 : ℝ), (5262140999/10000000000 : ℝ), (1349204293/2500000000 : ℝ)] ![(13399473759811/100000000000000 : ℝ), (10643154829427/25000000000000 : ℝ), (44027906907313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1103247197/5000000000 : ℝ)|^8253 ≤ (13399473759811/100000000000000 : ℝ)^6205
        have hw : |(-1103247197/5000000000 : ℝ)|=(1103247197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262140999/10000000000 : ℝ)|^8253 ≤ (10643154829427/25000000000000 : ℝ)^6205
        have hw : |(5262140999/10000000000 : ℝ)|=(5262140999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349204293/2500000000 : ℝ)|^8253 ≤ (44027906907313/100000000000000 : ℝ)^6205
        have hw : |(1349204293/2500000000 : ℝ)|=(1349204293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s5_5 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062316877/2000000000 : ℝ)*x 0 + (-1070095419/5000000000 : ℝ)*x 1 + (269840861/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062316877/2000000000 : ℝ)^8253 ≤ (43105484876417/100000000000000 : ℝ)^6205 := by
    have hnat : (1062316877 : ℕ)^8253*100000000000000^6205 ≤ 43105484876417^6205*2000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062316877 2000000000 43105484876417 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1070095419/5000000000 : ℝ)^8253 ≤ (1286660768591/10000000000000 : ℝ)^6205 := by
    have hnat : (1070095419 : ℕ)^8253*10000000000000^6205 ≤ 1286660768591^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070095419 5000000000 1286660768591 10000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269840861/500000000 : ℝ)^8253 ≤ (44027907428149/100000000000000 : ℝ)^6205 := by
    have hnat : (269840861 : ℕ)^8253*100000000000000^6205 ≤ 44027907428149^6205*500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269840861 500000000 44027907428149 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062316877/2000000000 : ℝ), (-1070095419/5000000000 : ℝ), (269840861/500000000 : ℝ)] ![(43105484876417/100000000000000 : ℝ), (1286660768591/10000000000000 : ℝ), (44027907428149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062316877/2000000000 : ℝ)|^8253 ≤ (43105484876417/100000000000000 : ℝ)^6205
        have hw : |(1062316877/2000000000 : ℝ)|=(1062316877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1070095419/5000000000 : ℝ)|^8253 ≤ (1286660768591/10000000000000 : ℝ)^6205
        have hw : |(-1070095419/5000000000 : ℝ)|=(1070095419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269840861/500000000 : ℝ)|^8253 ≤ (44027907428149/100000000000000 : ℝ)^6205
        have hw : |(269840861/500000000 : ℝ)|=(269840861/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s5_6 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311584393/10000000000 : ℝ)*x 0 + (168650537/312500000 : ℝ)*x 1 + (-535047719/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311584393/10000000000 : ℝ)^8253 ≤ (2694092810173/6250000000000 : ℝ)^6205 := by
    have hnat : (5311584393 : ℕ)^8253*6250000000000^6205 ≤ 2694092810173^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311584393 10000000000 2694092810173 6250000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168650537/312500000 : ℝ)^8253 ≤ (22013953518761/50000000000000 : ℝ)^6205 := by
    have hnat : (168650537 : ℕ)^8253*50000000000000^6205 ≤ 22013953518761^6205*312500000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168650537 312500000 22013953518761 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (535047719/2500000000 : ℝ)^8253 ≤ (3216651997441/25000000000000 : ℝ)^6205 := by
    have hnat : (535047719 : ℕ)^8253*25000000000000^6205 ≤ 3216651997441^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535047719 2500000000 3216651997441 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311584393/10000000000 : ℝ), (168650537/312500000 : ℝ), (-535047719/2500000000 : ℝ)] ![(2694092810173/6250000000000 : ℝ), (22013953518761/50000000000000 : ℝ), (3216651997441/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311584393/10000000000 : ℝ)|^8253 ≤ (2694092810173/6250000000000 : ℝ)^6205
        have hw : |(5311584393/10000000000 : ℝ)|=(5311584393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168650537/312500000 : ℝ)|^8253 ≤ (22013953518761/50000000000000 : ℝ)^6205
        have hw : |(168650537/312500000 : ℝ)|=(168650537/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-535047719/2500000000 : ℝ)|^8253 ≤ (3216651997441/25000000000000 : ℝ)^6205
        have hw : |(-535047719/2500000000 : ℝ)|=(535047719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s5_7 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2188115023/5000000000 : ℝ)*x 0 + (2255035633/5000000000 : ℝ)*x 1 + (4246439103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188115023/5000000000 : ℝ)^8253 ≤ (6663048008341/20000000000000 : ℝ)^6205 := by
    have hnat : (2188115023 : ℕ)^8253*20000000000000^6205 ≤ 6663048008341^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188115023 5000000000 6663048008341 20000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255035633/5000000000 : ℝ)^8253 ≤ (34677231818889/100000000000000 : ℝ)^6205 := by
    have hnat : (2255035633 : ℕ)^8253*100000000000000^6205 ≤ 34677231818889^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255035633 5000000000 34677231818889 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4246439103/10000000000 : ℝ)^8253 ≤ (32007528127969/100000000000000 : ℝ)^6205 := by
    have hnat : (4246439103 : ℕ)^8253*100000000000000^6205 ≤ 32007528127969^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246439103 10000000000 32007528127969 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188115023/5000000000 : ℝ), (2255035633/5000000000 : ℝ), (4246439103/10000000000 : ℝ)] ![(6663048008341/20000000000000 : ℝ), (34677231818889/100000000000000 : ℝ), (32007528127969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188115023/5000000000 : ℝ)|^8253 ≤ (6663048008341/20000000000000 : ℝ)^6205
        have hw : |(2188115023/5000000000 : ℝ)|=(2188115023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2255035633/5000000000 : ℝ)|^8253 ≤ (34677231818889/100000000000000 : ℝ)^6205
        have hw : |(2255035633/5000000000 : ℝ)|=(2255035633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4246439103/10000000000 : ℝ)|^8253 ≤ (32007528127969/100000000000000 : ℝ)^6205
        have hw : |(4246439103/10000000000 : ℝ)|=(4246439103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1060_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3561/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11009/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11189/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1757/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3561/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11009/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3561/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11009/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3561/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11009/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3561/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11009/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3561/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11009/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3561/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11009/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11009/100000 : ℝ) ^ (2063/512 : ℝ) ≤ (215148201537739/1562500000000000000 : ℝ) := by
    have hpowers : (11009/100000 : ℝ)^2063 ≤ (215148201537739/1562500000000000000 : ℝ)^512 := by
      have hnat : (11009 : ℕ)^2063*1562500000000000000^512 ≤ 215148201537739^512*100000^2063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11009 100000 215148201537739 1562500000000000000 2063 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11009/100000 : ℝ)) (X := (215148201537739/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3561/25000 : ℝ) ^ (2063/512 : ℝ) ≤ (19440253590088137/50000000000000000000 : ℝ) := by
    have hpowers : (3561/25000 : ℝ)^2063 ≤ (19440253590088137/50000000000000000000 : ℝ)^512 := by
      have hnat : (3561 : ℕ)^2063*50000000000000000000^512 ≤ 19440253590088137^512*25000^2063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3561 25000 19440253590088137 50000000000000000000 2063 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3561/25000 : ℝ)) (X := (19440253590088137/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (781465148201537739/781250000000000000 : ℝ) ≤ (10000683397630801/10000000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (781465148201537739/781250000000000000 : ℝ)^512 ≤ (10000683397630801/10000000000000000 : ℝ)^2063 := by
      have hnat : (781465148201537739 : ℕ)^512*10000000000000000^2063 ≤ 10000683397630801^2063*781250000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781465148201537739 781250000000000000 10000683397630801 10000000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000683397630801/10000000000000000 : ℝ)) (X := (781465148201537739/781250000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10005264999207859157/10000000000000000000 : ℝ) ≤ (2500326605215741/2500000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (10005264999207859157/10000000000000000000 : ℝ)^512 ≤ (2500326605215741/2500000000000000 : ℝ)^2063 := by
      have hnat : (10005264999207859157 : ℕ)^512*2500000000000000^2063 ≤ 2500326605215741^2063*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005264999207859157 10000000000000000000 2500326605215741 2500000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500326605215741/2500000000000000 : ℝ)) (X := (10005264999207859157/10000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25019440253590088137/25000000000000000000 : ℝ) ≤ (10001929444095127/10000000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (25019440253590088137/25000000000000000000 : ℝ)^512 ≤ (10001929444095127/10000000000000000 : ℝ)^2063 := by
      have hnat : (25019440253590088137 : ℕ)^512*10000000000000000^2063 ≤ 10001929444095127^2063*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019440253590088137 25000000000000000000 10001929444095127 10000000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001929444095127/10000000000000000 : ℝ)) (X := (25019440253590088137/25000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(215148201537739/1562500000000000000 : ℝ) ≤ ((32338493065809876301/32350000000000000000 : ℝ)+2*(623023232163/323500000000000 : ℝ)*(11009/100000 : ℝ))^(2063/512 : ℝ) := by
    rw [show (32338493065809876301/32350000000000000000 : ℝ)+2*(623023232163/323500000000000 : ℝ)*(11009/100000 : ℝ)=(10000683397630801/10000000000000000 : ℝ) by norm_num, show 1+2*(215148201537739/1562500000000000000 : ℝ)=(781465148201537739/781250000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19440253590088137/50000000000000000000 : ℝ)+(215148201537739/1562500000000000000 : ℝ) ≤ ((32338493065809876301/32350000000000000000 : ℝ)+(623023232163/323500000000000 : ℝ)*((3561/25000 : ℝ)+(11009/100000 : ℝ)))^(2063/512 : ℝ) := by
    rw [show (32338493065809876301/32350000000000000000 : ℝ)+(623023232163/323500000000000 : ℝ)*((3561/25000 : ℝ)+(11009/100000 : ℝ))=(2500326605215741/2500000000000000 : ℝ) by norm_num, show 1+(19440253590088137/50000000000000000000 : ℝ)+(215148201537739/1562500000000000000 : ℝ)=(10005264999207859157/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19440253590088137/50000000000000000000 : ℝ) ≤ ((32338493065809876301/32350000000000000000 : ℝ)+2*(623023232163/323500000000000 : ℝ)*(3561/25000 : ℝ))^(2063/512 : ℝ) := by
    rw [show (32338493065809876301/32350000000000000000 : ℝ)+2*(623023232163/323500000000000 : ℝ)*(3561/25000 : ℝ)=(10001929444095127/10000000000000000 : ℝ) by norm_num, show 1+2*(19440253590088137/50000000000000000000 : ℝ)=(25019440253590088137/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (32338493065809876301/32350000000000000000 : ℝ)*(X 1 0+X 2 0)+(623023232163/323500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (11009/100000 : ℝ)) (hi := (3561/25000 : ℝ)) (c := (32338493065809876301/32350000000000000000 : ℝ)) (alpha := (623023232163/323500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (32338493065809876301/32350000000000000000 : ℝ)*(X 0 1+X 2 1)+(623023232163/323500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (11009/100000 : ℝ)) (hi := (3561/25000 : ℝ)) (c := (32338493065809876301/32350000000000000000 : ℝ)) (alpha := (623023232163/323500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (32338493065809876301/32350000000000000000 : ℝ)*(X 0 2+X 1 2)+(623023232163/323500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (11009/100000 : ℝ)) (hi := (3561/25000 : ℝ)) (c := (32338493065809876301/32350000000000000000 : ℝ)) (alpha := (623023232163/323500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-17651909/80000000 : ℝ)*X 0 0+(5397171089/10000000000 : ℝ)*X 0 1+(5261788441/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672833933/5000000000 : ℝ)*X 1 0+(-2275219563/10000000000 : ℝ)*X 1 1+(5261788423/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534566779/1000000000 : ℝ)*X 2 0+(5261788457/10000000000 : ℝ)*X 2 1+(-2275219619/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((10940547/25000000 : ℝ)*X 0 0+(21228731/50000000 : ℝ)*X 0 1+(1127690407/2500000000 : ℝ)*X 0 2+(10940547/25000000 : ℝ)*X 1 0+(21228731/50000000 : ℝ)*X 1 1+(1127690407/2500000000 : ℝ)*X 1 2+(10940547/25000000 : ℝ)*X 2 0+(21228731/50000000 : ℝ)*X 2 1+(1127690407/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1103247197/5000000000 : ℝ)*X 0 0+(5262140999/10000000000 : ℝ)*X 0 1+(1349204293/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062316877/2000000000 : ℝ)*X 1 0+(-1070095419/5000000000 : ℝ)*X 1 1+(269840861/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311584393/10000000000 : ℝ)*X 2 0+(168650537/312500000 : ℝ)*X 2 1+(-535047719/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2188115023/5000000000 : ℝ)*X 0 0+(2255035633/5000000000 : ℝ)*X 0 1+(4246439103/10000000000 : ℝ)*X 0 2+(2188115023/5000000000 : ℝ)*X 1 0+(2255035633/5000000000 : ℝ)*X 1 1+(4246439103/10000000000 : ℝ)*X 1 2+(2188115023/5000000000 : ℝ)*X 2 0+(2255035633/5000000000 : ℝ)*X 2 1+(4246439103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (729729827561840121484023687/202187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (652505901/100000000000000 : ℝ)*(base19) + (554245439/100000000000000 : ℝ)*(base23) + (4934349/20000000000000 : ℝ)*(lower2) + (997739/1000000000000 : ℝ)*(upper3) + (14141203/50000000000000 : ℝ)*(lower4) + (1394986628871471/25000000000000 : ℝ)*(major0) + (1394986628871471/25000000000000 : ℝ)*(major1) + (1394986628871471/25000000000000 : ℝ)*(major2) + (3693245604104501/50000000000000 : ℝ)*(sp0) + (3693252539324319/50000000000000 : ℝ)*(sp1) + (73865051769091/1000000000000 : ℝ)*(sp2) + (3773375491349727/100000000000000 : ℝ)*(sp3) + (14522945537/100000000000000 : ℝ)*(sp4) + (11688161701/100000000000000 : ℝ)*(sp7) + (943346794877857/25000000000000 : ℝ)*(f.failure) + (7386505731154539/100000000000000 : ℝ)*(f.sum) + (15496296022971/8087500000000000000000000000 : ℝ)*base65 + (5044500880128958771/808750000000000000000000000000000 : ℝ)*base67 + (5928067131121458771/808750000000000000000000000000000 : ℝ)*base69 + (5718256880117708771/808750000000000000000000000000000 : ℝ)*base71 + (709387885623/4043750000000000000000000000 : ℝ)*base73 + (2066277285726458771/808750000000000000000000000000000 : ℝ)*base75 + (2989249060287291229/808750000000000000000000000000000 : ℝ)*base78 + (10089043372412708771/808750000000000000000000000000000 : ℝ)*base79 + (129787505092767/16175000000000000000000000000 : ℝ)*base81 + (13697333/2500000000000000000000 : ℝ)*base90 + (13697333/2500000000000000000000 : ℝ)*base92 + (13697333/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3901725735828011549823/647000000000000000000000000 : ℝ) := by norm_num
    linear_combination (266119051/25000000000000 : ℝ)*(base19) + (1176449973/100000000000000 : ℝ)*(base23) + (119832017/100000000000000 : ℝ)*(upper3) + (26539831/50000000000000 : ℝ)*(lower4) + (132779453/100000000000000 : ℝ)*(upper5) + (28045952590061/500000000000 : ℝ)*(major0) + (28045952590061/500000000000 : ℝ)*(major1) + (28045952590061/500000000000 : ℝ)*(major2) + (30053358081/100000000000000 : ℝ)*(sp1) + (1886700943/6250000000000 : ℝ)*(sp2) + (3712608834744819/50000000000000 : ℝ)*(sp4) + (928148318956919/12500000000000 : ℝ)*(sp5) + (7425186305824577/100000000000000 : ℝ)*(sp6) + (379316316551849/10000000000000 : ℝ)*(sp7) + (379316316551849/10000000000000 : ℝ)*(f.failure) + (3712608834744819/50000000000000 : ℝ)*(f.sum) + (147423715019/80875000000000000000000000 : ℝ)*base66 + (48440459988505639/16175000000000000000000000000000 : ℝ)*base68 + (132214855684294361/16175000000000000000000000000000 : ℝ)*base69 + (187177893884294361/16175000000000000000000000000000 : ℝ)*base71 + (1116529524823/647000000000000000000000000 : ℝ)*base74 + (146376776731930639/16175000000000000000000000000000 : ℝ)*base76 + (3840114286669361/16175000000000000000000000000000 : ℝ)*base77 + (47345445194355639/16175000000000000000000000000000 : ℝ)*base80 + (1142750390641/323500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1386019/1000000000000000000000 : ℝ)*base89 + (1386019/1000000000000000000000 : ℝ)*base91 + (1386019/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1060_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3561/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11009/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11189/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1060_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1060_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4341/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11189/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1060_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1060_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1060_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4341/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11189/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1060_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
