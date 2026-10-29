-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1610_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:51:05.947355+00:00
-- url     : https://prove2.me/submissions/0fd93bcc-c628-42a0-be99-a084b3a2cc05

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
theorem support_rectangle_w1610_s0_0 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-48922463/312500000 : ℝ)*x 0 + (5837121717/10000000000 : ℝ)*x 1 + (4893011073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (48922463/312500000 : ℝ)^4759 ≤ (588495508667/6250000000000 : ℝ)^3735 := by
    have hnat : (48922463 : ℕ)^4759*6250000000000^3735 ≤ 588495508667^3735*312500000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48922463 312500000 588495508667 6250000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5837121717/10000000000 : ℝ)^4759 ≤ (10072308474559/20000000000000 : ℝ)^3735 := by
    have hnat : (5837121717 : ℕ)^4759*20000000000000^3735 ≤ 10072308474559^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5837121717 10000000000 10072308474559 20000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4893011073/10000000000 : ℝ)^4759 ≤ (40222529473783/100000000000000 : ℝ)^3735 := by
    have hnat : (4893011073 : ℕ)^4759*100000000000000^3735 ≤ 40222529473783^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4893011073 10000000000 40222529473783 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-48922463/312500000 : ℝ), (5837121717/10000000000 : ℝ), (4893011073/10000000000 : ℝ)] ![(588495508667/6250000000000 : ℝ), (10072308474559/20000000000000 : ℝ), (40222529473783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-48922463/312500000 : ℝ)|^4759 ≤ (588495508667/6250000000000 : ℝ)^3735
        have hw : |(-48922463/312500000 : ℝ)|=(48922463/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5837121717/10000000000 : ℝ)|^4759 ≤ (10072308474559/20000000000000 : ℝ)^3735
        have hw : |(5837121717/10000000000 : ℝ)|=(5837121717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4893011073/10000000000 : ℝ)|^4759 ≤ (40222529473783/100000000000000 : ℝ)^3735
        have hw : |(4893011073/10000000000 : ℝ)|=(4893011073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s0_1 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1363429453/2500000000 : ℝ)*x 0 + (-2088242679/10000000000 : ℝ)*x 1 + (2446505599/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1363429453/2500000000 : ℝ)^4759 ≤ (23092632989327/50000000000000 : ℝ)^3735 := by
    have hnat : (1363429453 : ℕ)^4759*50000000000000^3735 ≤ 23092632989327^3735*2500000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363429453 2500000000 23092632989327 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2088242679/10000000000 : ℝ)^4759 ≤ (13592203224601/100000000000000 : ℝ)^3735 := by
    have hnat : (2088242679 : ℕ)^4759*100000000000000^3735 ≤ 13592203224601^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088242679 10000000000 13592203224601 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2446505599/5000000000 : ℝ)^4759 ≤ (804450615661/2000000000000 : ℝ)^3735 := by
    have hnat : (2446505599 : ℕ)^4759*2000000000000^3735 ≤ 804450615661^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2446505599 5000000000 804450615661 2000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1363429453/2500000000 : ℝ), (-2088242679/10000000000 : ℝ), (2446505599/5000000000 : ℝ)] ![(23092632989327/50000000000000 : ℝ), (13592203224601/100000000000000 : ℝ), (804450615661/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1363429453/2500000000 : ℝ)|^4759 ≤ (23092632989327/50000000000000 : ℝ)^3735
        have hw : |(1363429453/2500000000 : ℝ)|=(1363429453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2088242679/10000000000 : ℝ)|^4759 ≤ (13592203224601/100000000000000 : ℝ)^3735
        have hw : |(-2088242679/10000000000 : ℝ)|=(2088242679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2446505599/5000000000 : ℝ)|^4759 ≤ (804450615661/2000000000000 : ℝ)^3735
        have hw : |(2446505599/5000000000 : ℝ)|=(2446505599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s0_2 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (681714747/1250000000 : ℝ)*x 0 + (4893011041/10000000000 : ℝ)*x 1 + (-2088242663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (681714747/1250000000 : ℝ)^4759 ≤ (2886579234267/6250000000000 : ℝ)^3735 := by
    have hnat : (681714747 : ℕ)^4759*6250000000000^3735 ≤ 2886579234267^3735*1250000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681714747 1250000000 2886579234267 6250000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4893011041/10000000000 : ℝ)^4759 ≤ (4022252913861/10000000000000 : ℝ)^3735 := by
    have hnat : (4893011041 : ℕ)^4759*10000000000000^3735 ≤ 4022252913861^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4893011041 10000000000 4022252913861 10000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2088242663/10000000000 : ℝ)^4759 ≤ (6796101545953/50000000000000 : ℝ)^3735 := by
    have hnat : (2088242663 : ℕ)^4759*50000000000000^3735 ≤ 6796101545953^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088242663 10000000000 6796101545953 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(681714747/1250000000 : ℝ), (4893011041/10000000000 : ℝ), (-2088242663/10000000000 : ℝ)] ![(2886579234267/6250000000000 : ℝ), (4022252913861/10000000000000 : ℝ), (6796101545953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(681714747/1250000000 : ℝ)|^4759 ≤ (2886579234267/6250000000000 : ℝ)^3735
        have hw : |(681714747/1250000000 : ℝ)|=(681714747/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4893011041/10000000000 : ℝ)|^4759 ≤ (4022252913861/10000000000000 : ℝ)^3735
        have hw : |(4893011041/10000000000 : ℝ)|=(4893011041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2088242663/10000000000 : ℝ)|^4759 ≤ (6796101545953/50000000000000 : ℝ)^3735
        have hw : |(-2088242663/10000000000 : ℝ)|=(2088242663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s0_3 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4109780869/10000000000 : ℝ)*x 0 + (307429001/1000000000 : ℝ)*x 1 + (5394291127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4109780869/10000000000 : ℝ)^4759 ≤ (16103189880279/50000000000000 : ℝ)^3735 := by
    have hnat : (4109780869 : ℕ)^4759*50000000000000^3735 ≤ 16103189880279^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4109780869 10000000000 16103189880279 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (307429001/1000000000 : ℝ)^4759 ≤ (22248629136137/100000000000000 : ℝ)^3735 := by
    have hnat : (307429001 : ℕ)^4759*100000000000000^3735 ≤ 22248629136137^3735*1000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307429001 1000000000 22248629136137 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394291127/10000000000 : ℝ)^4759 ≤ (45544991087719/100000000000000 : ℝ)^3735 := by
    have hnat : (5394291127 : ℕ)^4759*100000000000000^3735 ≤ 45544991087719^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394291127 10000000000 45544991087719 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4109780869/10000000000 : ℝ), (307429001/1000000000 : ℝ), (5394291127/10000000000 : ℝ)] ![(16103189880279/50000000000000 : ℝ), (22248629136137/100000000000000 : ℝ), (45544991087719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4109780869/10000000000 : ℝ)|^4759 ≤ (16103189880279/50000000000000 : ℝ)^3735
        have hw : |(4109780869/10000000000 : ℝ)|=(4109780869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(307429001/1000000000 : ℝ)|^4759 ≤ (22248629136137/100000000000000 : ℝ)^3735
        have hw : |(307429001/1000000000 : ℝ)|=(307429001/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394291127/10000000000 : ℝ)|^4759 ≤ (45544991087719/100000000000000 : ℝ)^3735
        have hw : |(5394291127/10000000000 : ℝ)|=(5394291127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s0_4 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-98019491/625000000 : ℝ)*x 0 + (4916908721/10000000000 : ℝ)*x 1 + (1453093833/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (98019491/625000000 : ℝ)^4759 ≤ (2359334492589/25000000000000 : ℝ)^3735 := by
    have hnat : (98019491 : ℕ)^4759*25000000000000^3735 ≤ 2359334492589^3735*625000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98019491 625000000 2359334492589 25000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4916908721/10000000000 : ℝ)^4759 ≤ (40473004115451/100000000000000 : ℝ)^3735 := by
    have hnat : (4916908721 : ℕ)^4759*100000000000000^3735 ≤ 40473004115451^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4916908721 10000000000 40473004115451 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1453093833/2500000000 : ℝ)^4759 ≤ (25044828948291/50000000000000 : ℝ)^3735 := by
    have hnat : (1453093833 : ℕ)^4759*50000000000000^3735 ≤ 25044828948291^3735*2500000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1453093833 2500000000 25044828948291 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-98019491/625000000 : ℝ), (4916908721/10000000000 : ℝ), (1453093833/2500000000 : ℝ)] ![(2359334492589/25000000000000 : ℝ), (40473004115451/100000000000000 : ℝ), (25044828948291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-98019491/625000000 : ℝ)|^4759 ≤ (2359334492589/25000000000000 : ℝ)^3735
        have hw : |(-98019491/625000000 : ℝ)|=(98019491/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4916908721/10000000000 : ℝ)|^4759 ≤ (40473004115451/100000000000000 : ℝ)^3735
        have hw : |(4916908721/10000000000 : ℝ)|=(4916908721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1453093833/2500000000 : ℝ)|^4759 ≤ (25044828948291/50000000000000 : ℝ)^3735
        have hw : |(1453093833/2500000000 : ℝ)|=(1453093833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s0_5 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5195868439/10000000000 : ℝ)*x 0 + (-584439079/5000000000 : ℝ)*x 1 + (726546927/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195868439/10000000000 : ℝ)^4759 ≤ (21710610889541/50000000000000 : ℝ)^3735 := by
    have hnat : (5195868439 : ℕ)^4759*50000000000000^3735 ≤ 21710610889541^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195868439 10000000000 21710610889541 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (584439079/5000000000 : ℝ)^4759 ≤ (6489119383457/100000000000000 : ℝ)^3735 := by
    have hnat : (584439079 : ℕ)^4759*100000000000000^3735 ≤ 6489119383457^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      584439079 5000000000 6489119383457 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (726546927/1250000000 : ℝ)^4759 ≤ (50089658818939/100000000000000 : ℝ)^3735 := by
    have hnat : (726546927 : ℕ)^4759*100000000000000^3735 ≤ 50089658818939^3735*1250000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      726546927 1250000000 50089658818939 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195868439/10000000000 : ℝ), (-584439079/5000000000 : ℝ), (726546927/1250000000 : ℝ)] ![(21710610889541/50000000000000 : ℝ), (6489119383457/100000000000000 : ℝ), (50089658818939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195868439/10000000000 : ℝ)|^4759 ≤ (21710610889541/50000000000000 : ℝ)^3735
        have hw : |(5195868439/10000000000 : ℝ)|=(5195868439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-584439079/5000000000 : ℝ)|^4759 ≤ (6489119383457/100000000000000 : ℝ)^3735
        have hw : |(-584439079/5000000000 : ℝ)|=(584439079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(726546927/1250000000 : ℝ)|^4759 ≤ (50089658818939/100000000000000 : ℝ)^3735
        have hw : |(726546927/1250000000 : ℝ)|=(726546927/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s0_6 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1298967129/2500000000 : ℝ)*x 0 + (363273443/625000000 : ℝ)*x 1 + (-1168878553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1298967129/2500000000 : ℝ)^4759 ≤ (2171061129949/5000000000000 : ℝ)^3735 := by
    have hnat : (1298967129 : ℕ)^4759*5000000000000^3735 ≤ 2171061129949^3735*2500000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298967129 2500000000 2171061129949 5000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (363273443/625000000 : ℝ)^4759 ≤ (12522413804339/25000000000000 : ℝ)^3735 := by
    have hnat : (363273443 : ℕ)^4759*25000000000000^3735 ≤ 12522413804339^3735*625000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363273443 625000000 12522413804339 25000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1168878553/10000000000 : ℝ)^4759 ≤ (6489122177537/100000000000000 : ℝ)^3735 := by
    have hnat : (1168878553 : ℕ)^4759*100000000000000^3735 ≤ 6489122177537^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1168878553 10000000000 6489122177537 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1298967129/2500000000 : ℝ), (363273443/625000000 : ℝ), (-1168878553/10000000000 : ℝ)] ![(2171061129949/5000000000000 : ℝ), (12522413804339/25000000000000 : ℝ), (6489122177537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1298967129/2500000000 : ℝ)|^4759 ≤ (2171061129949/5000000000000 : ℝ)^3735
        have hw : |(1298967129/2500000000 : ℝ)|=(1298967129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(363273443/625000000 : ℝ)|^4759 ≤ (12522413804339/25000000000000 : ℝ)^3735
        have hw : |(363273443/625000000 : ℝ)|=(363273443/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1168878553/10000000000 : ℝ)|^4759 ≤ (6489122177537/100000000000000 : ℝ)^3735
        have hw : |(-1168878553/10000000000 : ℝ)|=(1168878553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s0_7 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2058322599/5000000000 : ℝ)*x 0 + (2667783643/5000000000 : ℝ)*x 1 + (125404001/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2058322599/5000000000 : ℝ)^4759 ≤ (32274935815321/100000000000000 : ℝ)^3735 := by
    have hnat : (2058322599 : ℕ)^4759*100000000000000^3735 ≤ 32274935815321^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058322599 5000000000 32274935815321 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2667783643/5000000000 : ℝ)^4759 ≤ (4491418556273/10000000000000 : ℝ)^3735 := by
    have hnat : (2667783643 : ℕ)^4759*10000000000000^3735 ≤ 4491418556273^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2667783643 5000000000 4491418556273 10000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (125404001/400000000 : ℝ)^4759 ≤ (22810878606647/100000000000000 : ℝ)^3735 := by
    have hnat : (125404001 : ℕ)^4759*100000000000000^3735 ≤ 22810878606647^3735*400000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125404001 400000000 22810878606647 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2058322599/5000000000 : ℝ), (2667783643/5000000000 : ℝ), (125404001/400000000 : ℝ)] ![(32274935815321/100000000000000 : ℝ), (4491418556273/10000000000000 : ℝ), (22810878606647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2058322599/5000000000 : ℝ)|^4759 ≤ (32274935815321/100000000000000 : ℝ)^3735
        have hw : |(2058322599/5000000000 : ℝ)|=(2058322599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2667783643/5000000000 : ℝ)|^4759 ≤ (4491418556273/10000000000000 : ℝ)^3735
        have hw : |(2667783643/5000000000 : ℝ)|=(2667783643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(125404001/400000000 : ℝ)|^4759 ≤ (22810878606647/100000000000000 : ℝ)^3735
        have hw : |(125404001/400000000 : ℝ)|=(125404001/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1610_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34573411/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2011/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (12121/50000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4755/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4755 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4755*1^1024 ≤ 0^1024*1^4755 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4755 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4755/1024 : ℝ) ≤ (709763745116222179/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4755 ≤ (709763745116222179/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4755*50000000000000000000^1024 ≤ 709763745116222179^1024*5^4755 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 709763745116222179 50000000000000000000 4755 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (709763745116222179/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4755/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4755 := by
      have hnat : (1 : ℕ)^1024*1^4755 ≤ 1^4755*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4755 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50709763745116222179/50000000000000000000 : ℝ) ≤ (2507600255281087/2500000000000000 : ℝ) ^ (4755/1024 : ℝ) := by
    have hpowers : (50709763745116222179/50000000000000000000 : ℝ)^1024 ≤ (2507600255281087/2500000000000000 : ℝ)^4755 := by
      have hnat : (50709763745116222179 : ℕ)^1024*2500000000000000^4755 ≤ 2507600255281087^4755*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50709763745116222179 50000000000000000000 2507600255281087 2500000000000000 1024 4755 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2507600255281087/2500000000000000 : ℝ)) (X := (50709763745116222179/50000000000000000000 : ℝ)) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25709763745116222179/25000000000000000000 : ℝ) ≤ (1257600255281087/1250000000000000 : ℝ) ^ (4755/1024 : ℝ) := by
    have hpowers : (25709763745116222179/25000000000000000000 : ℝ)^1024 ≤ (1257600255281087/1250000000000000 : ℝ)^4755 := by
      have hnat : (25709763745116222179 : ℕ)^1024*1250000000000000^4755 ≤ 1257600255281087^4755*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25709763745116222179 25000000000000000000 1257600255281087 1250000000000000 1024 4755 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1257600255281087/1250000000000000 : ℝ)) (X := (25709763745116222179/25000000000000000000 : ℝ)) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(7600255281087/1000000000000000 : ℝ)*(0 : ℝ))^(4755/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7600255281087/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(709763745116222179/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(7600255281087/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4755/1024 : ℝ) := by
    rw [show (1 : ℝ)+(7600255281087/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2507600255281087/2500000000000000 : ℝ) by norm_num, show 1+(709763745116222179/50000000000000000000 : ℝ)+(0 : ℝ)=(50709763745116222179/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(709763745116222179/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(7600255281087/1000000000000000 : ℝ)*(2/5 : ℝ))^(4755/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7600255281087/1000000000000000 : ℝ)*(2/5 : ℝ)=(1257600255281087/1250000000000000 : ℝ) by norm_num, show 1+2*(709763745116222179/50000000000000000000 : ℝ)=(25709763745116222179/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(7600255281087/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4755/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7600255281087/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(7600255281087/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4755/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7600255281087/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(7600255281087/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4755/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7600255281087/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-48922463/312500000 : ℝ)*X 0 0+(5837121717/10000000000 : ℝ)*X 0 1+(4893011073/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1363429453/2500000000 : ℝ)*X 1 0+(-2088242679/10000000000 : ℝ)*X 1 1+(2446505599/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((681714747/1250000000 : ℝ)*X 2 0+(4893011041/10000000000 : ℝ)*X 2 1+(-2088242663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4109780869/10000000000 : ℝ)*X 0 0+(307429001/1000000000 : ℝ)*X 0 1+(5394291127/10000000000 : ℝ)*X 0 2+(4109780869/10000000000 : ℝ)*X 1 0+(307429001/1000000000 : ℝ)*X 1 1+(5394291127/10000000000 : ℝ)*X 1 2+(4109780869/10000000000 : ℝ)*X 2 0+(307429001/1000000000 : ℝ)*X 2 1+(5394291127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-98019491/625000000 : ℝ)*X 0 0+(4916908721/10000000000 : ℝ)*X 0 1+(1453093833/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5195868439/10000000000 : ℝ)*X 1 0+(-584439079/5000000000 : ℝ)*X 1 1+(726546927/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1298967129/2500000000 : ℝ)*X 2 0+(363273443/625000000 : ℝ)*X 2 1+(-1168878553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2058322599/5000000000 : ℝ)*X 0 0+(2667783643/5000000000 : ℝ)*X 0 1+(125404001/400000000 : ℝ)*X 0 2+(2058322599/5000000000 : ℝ)*X 1 0+(2667783643/5000000000 : ℝ)*X 1 1+(125404001/400000000 : ℝ)*X 1 2+(2058322599/5000000000 : ℝ)*X 2 0+(2667783643/5000000000 : ℝ)*X 2 1+(125404001/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53599713990651993/6250000000000000000000 : ℝ) := by norm_num
    linear_combination (21664257/20000000000000 : ℝ)*(base1) + (911253429/50000000000000 : ℝ)*(base19) + (1854358593/100000000000000 : ℝ)*(base23) + (119658921/50000000000000 : ℝ)*(upper3) + (15788949/6250000000000 : ℝ)*(upper5) + (9314071860459/1250000000000 : ℝ)*(major0) + (9314071860459/1250000000000 : ℝ)*(major1) + (9314071860459/1250000000000 : ℝ)*(major2) + (529602233068011/50000000000000 : ℝ)*(sp0) + (1059209623605927/100000000000000 : ℝ)*(sp1) + (66200599484637/6250000000000 : ℝ)*(sp2) + (26939806632087/6250000000000 : ℝ)*(sp3) + (110754657/1562500000000 : ℝ)*(sp4) + (2751260829/100000000000000 : ℝ)*(sp7) + (86207953139101/20000000000000 : ℝ)*(f.failure) + (66200715382049/6250000000000 : ℝ)*(f.sum) + (497710995183/625000000000000000000000000 : ℝ)*base65 + (9877314656067/1250000000000000000000000000 : ℝ)*base68 + (9578435474817/1250000000000000000000000000 : ℝ)*base70 + (7020062303567/1250000000000000000000000000 : ℝ)*base72 + (230847012601/78125000000000000000000000 : ℝ)*base73 + (5479744229817/1250000000000000000000000000 : ℝ)*base76 + (5188916888567/1250000000000000000000000000 : ℝ)*base78 + (9456524018567/1250000000000000000000000000 : ℝ)*base80 + (163169419113/39062500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (956489/400000000000000000000 : ℝ)*base90 + (956489/400000000000000000000 : ℝ)*base92 + (956489/400000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (68875410999575160791247/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (279129061/25000000000000 : ℝ)*(base19) + (1136919949/100000000000000 : ℝ)*(base23) + (52462521/25000000000000 : ℝ)*(base32) + (198519213/100000000000000 : ℝ)*(upper3) + (14591827/25000000000000 : ℝ)*(upper5) + (392795959588773/50000000000000 : ℝ)*(major0) + (392795959588773/50000000000000 : ℝ)*(major1) + (392795959588773/50000000000000 : ℝ)*(major2) + (757089637/25000000000000 : ℝ)*(sp1) + (124240991/4000000000000 : ℝ)*(sp2) + (558367525067687/50000000000000 : ℝ)*(sp4) + (558365452630291/50000000000000 : ℝ)*(sp5) + (22334616143813/2000000000000 : ℝ)*(sp6) + (227224197350931/50000000000000 : ℝ)*(sp7) + (227224302275973/50000000000000 : ℝ)*(f.failure) + (558367525067687/50000000000000 : ℝ)*(f.sum) + (22960931136251/25000000000000000000000000000 : ℝ)*base65 + (644745885136251/50000000000000000000000000000 : ℝ)*base67 + (118266991463749/50000000000000000000000000000 : ℝ)*base70 + (193900686936251/50000000000000000000000000000 : ℝ)*base71 + (163723832336251/25000000000000000000000000000 : ℝ)*base73 + (4040913863749/50000000000000000000000000000 : ℝ)*base76 + (62460570636251/50000000000000000000000000000 : ℝ)*base77 + (626252319086251/50000000000000000000000000000 : ℝ)*base79 + (66335987438749/25000000000000000000000000000 : ℝ)*base82 + (10046097/1000000000000000000000 : ℝ)*base90 + (10046097/1000000000000000000000 : ℝ)*base92 + (10046097/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1610_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34573411/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2011/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (12121/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1610_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1610_s1_0 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-168892657/1000000000 : ℝ)*x 0 + (138247521/250000000 : ℝ)*x 1 + (5120417407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168892657/1000000000 : ℝ)^4759 ≤ (10371700609481/100000000000000 : ℝ)^3735 := by
    have hnat : (168892657 : ℕ)^4759*100000000000000^3735 ≤ 10371700609481^3735*1000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168892657 1000000000 10371700609481 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138247521/250000000 : ℝ)^4759 ≤ (9401775403829/20000000000000 : ℝ)^3735 := by
    have hnat : (138247521 : ℕ)^4759*20000000000000^3735 ≤ 9401775403829^3735*250000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138247521 250000000 9401775403829 20000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5120417407/10000000000 : ℝ)^4759 ≤ (21309711176829/50000000000000 : ℝ)^3735 := by
    have hnat : (5120417407 : ℕ)^4759*50000000000000^3735 ≤ 21309711176829^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5120417407 10000000000 21309711176829 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-168892657/1000000000 : ℝ), (138247521/250000000 : ℝ), (5120417407/10000000000 : ℝ)] ![(10371700609481/100000000000000 : ℝ), (9401775403829/20000000000000 : ℝ), (21309711176829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-168892657/1000000000 : ℝ)|^4759 ≤ (10371700609481/100000000000000 : ℝ)^3735
        have hw : |(-168892657/1000000000 : ℝ)|=(168892657/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(138247521/250000000 : ℝ)|^4759 ≤ (9401775403829/20000000000000 : ℝ)^3735
        have hw : |(138247521/250000000 : ℝ)|=(138247521/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5120417407/10000000000 : ℝ)|^4759 ≤ (21309711176829/50000000000000 : ℝ)^3735
        have hw : |(5120417407/10000000000 : ℝ)|=(5120417407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s1_1 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537196313/1000000000 : ℝ)*x 0 + (-1903080487/10000000000 : ℝ)*x 1 + (256020863/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537196313/1000000000 : ℝ)^4759 ≤ (11326230759441/25000000000000 : ℝ)^3735 := by
    have hnat : (537196313 : ℕ)^4759*25000000000000^3735 ≤ 11326230759441^3735*1000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537196313 1000000000 11326230759441 25000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1903080487/10000000000 : ℝ)^4759 ≤ (3018914037191/25000000000000 : ℝ)^3735 := by
    have hnat : (1903080487 : ℕ)^4759*25000000000000^3735 ≤ 3018914037191^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1903080487 10000000000 3018914037191 25000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256020863/500000000 : ℝ)^4759 ≤ (42619420794663/100000000000000 : ℝ)^3735 := by
    have hnat : (256020863 : ℕ)^4759*100000000000000^3735 ≤ 42619420794663^3735*500000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256020863 500000000 42619420794663 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537196313/1000000000 : ℝ), (-1903080487/10000000000 : ℝ), (256020863/500000000 : ℝ)] ![(11326230759441/25000000000000 : ℝ), (3018914037191/25000000000000 : ℝ), (42619420794663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537196313/1000000000 : ℝ)|^4759 ≤ (11326230759441/25000000000000 : ℝ)^3735
        have hw : |(537196313/1000000000 : ℝ)|=(537196313/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1903080487/10000000000 : ℝ)|^4759 ≤ (3018914037191/25000000000000 : ℝ)^3735
        have hw : |(-1903080487/10000000000 : ℝ)|=(1903080487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(256020863/500000000 : ℝ)|^4759 ≤ (42619420794663/100000000000000 : ℝ)^3735
        have hw : |(256020863/500000000 : ℝ)|=(256020863/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s1_2 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5371962867/10000000000 : ℝ)*x 0 + (256020873/500000000 : ℝ)*x 1 + (-951540287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371962867/10000000000 : ℝ)^4759 ≤ (45304920211627/100000000000000 : ℝ)^3735 := by
    have hnat : (5371962867 : ℕ)^4759*100000000000000^3735 ≤ 45304920211627^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371962867 10000000000 45304920211627 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256020873/500000000 : ℝ)^4759 ≤ (1331856966117/3125000000000 : ℝ)^3735 := by
    have hnat : (256020873 : ℕ)^4759*3125000000000^3735 ≤ 1331856966117^3735*500000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256020873 500000000 1331856966117 3125000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (951540287/5000000000 : ℝ)^4759 ≤ (12075656852157/100000000000000 : ℝ)^3735 := by
    have hnat : (951540287 : ℕ)^4759*100000000000000^3735 ≤ 12075656852157^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      951540287 5000000000 12075656852157 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371962867/10000000000 : ℝ), (256020873/500000000 : ℝ), (-951540287/5000000000 : ℝ)] ![(45304920211627/100000000000000 : ℝ), (1331856966117/3125000000000 : ℝ), (12075656852157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371962867/10000000000 : ℝ)|^4759 ≤ (45304920211627/100000000000000 : ℝ)^3735
        have hw : |(5371962867/10000000000 : ℝ)|=(5371962867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(256020873/500000000 : ℝ)|^4759 ≤ (1331856966117/3125000000000 : ℝ)^3735
        have hw : |(256020873/500000000 : ℝ)|=(256020873/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-951540287/5000000000 : ℝ)|^4759 ≤ (12075656852157/100000000000000 : ℝ)^3735
        have hw : |(-951540287/5000000000 : ℝ)|=(951540287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s1_3 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4201317323/10000000000 : ℝ)*x 0 + (1860662981/5000000000 : ℝ)*x 1 + (4727566829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4201317323/10000000000 : ℝ)^4759 ≤ (16561573765129/50000000000000 : ℝ)^3735 := by
    have hnat : (4201317323 : ℕ)^4759*50000000000000^3735 ≤ 16561573765129^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4201317323 10000000000 16561573765129 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1860662981/5000000000 : ℝ)^4759 ≤ (28379110074327/100000000000000 : ℝ)^3735 := by
    have hnat : (1860662981 : ℕ)^4759*100000000000000^3735 ≤ 28379110074327^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1860662981 5000000000 28379110074327 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4727566829/10000000000 : ℝ)^4759 ≤ (76995484773/200000000000 : ℝ)^3735 := by
    have hnat : (4727566829 : ℕ)^4759*200000000000^3735 ≤ 76995484773^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4727566829 10000000000 76995484773 200000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4201317323/10000000000 : ℝ), (1860662981/5000000000 : ℝ), (4727566829/10000000000 : ℝ)] ![(16561573765129/50000000000000 : ℝ), (28379110074327/100000000000000 : ℝ), (76995484773/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4201317323/10000000000 : ℝ)|^4759 ≤ (16561573765129/50000000000000 : ℝ)^3735
        have hw : |(4201317323/10000000000 : ℝ)|=(4201317323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1860662981/5000000000 : ℝ)|^4759 ≤ (28379110074327/100000000000000 : ℝ)^3735
        have hw : |(1860662981/5000000000 : ℝ)|=(1860662981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4727566829/10000000000 : ℝ)|^4759 ≤ (76995484773/200000000000 : ℝ)^3735
        have hw : |(4727566829/10000000000 : ℝ)|=(4727566829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s1_4 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1689149347/10000000000 : ℝ)*x 0 + (1281218367/2500000000 : ℝ)*x 1 + (276268791/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1689149347/10000000000 : ℝ)^4759 ≤ (10373443790571/100000000000000 : ℝ)^3735 := by
    have hnat : (1689149347 : ℕ)^4759*100000000000000^3735 ≤ 10373443790571^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1689149347 10000000000 10373443790571 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1281218367/2500000000 : ℝ)^4759 ≤ (2666667895347/6250000000000 : ℝ)^3735 := by
    have hnat : (1281218367 : ℕ)^4759*6250000000000^3735 ≤ 2666667895347^3735*2500000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281218367 2500000000 2666667895347 6250000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276268791/500000000 : ℝ)^4759 ≤ (46959869873689/100000000000000 : ℝ)^3735 := by
    have hnat : (276268791 : ℕ)^4759*100000000000000^3735 ≤ 46959869873689^3735*500000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276268791 500000000 46959869873689 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1689149347/10000000000 : ℝ), (1281218367/2500000000 : ℝ), (276268791/500000000 : ℝ)] ![(10373443790571/100000000000000 : ℝ), (2666667895347/6250000000000 : ℝ), (46959869873689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1689149347/10000000000 : ℝ)|^4759 ≤ (10373443790571/100000000000000 : ℝ)^3735
        have hw : |(-1689149347/10000000000 : ℝ)|=(1689149347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1281218367/2500000000 : ℝ)|^4759 ≤ (2666667895347/6250000000000 : ℝ)^3735
        have hw : |(1281218367/2500000000 : ℝ)|=(1281218367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(276268791/500000000 : ℝ)|^4759 ≤ (46959869873689/100000000000000 : ℝ)^3735
        have hw : |(276268791/500000000 : ℝ)|=(276268791/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s1_5 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1052605941/2000000000 : ℝ)*x 0 + (-1498121611/10000000000 : ℝ)*x 1 + (5525376149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052605941/2000000000 : ℝ)^4759 ≤ (275860123199/625000000000 : ℝ)^3735 := by
    have hnat : (1052605941 : ℕ)^4759*625000000000^3735 ≤ 275860123199^3735*2000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052605941 2000000000 275860123199 625000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1498121611/10000000000 : ℝ)^4759 ≤ (2225626710957/25000000000000 : ℝ)^3735 := by
    have hnat : (1498121611 : ℕ)^4759*25000000000000^3735 ≤ 2225626710957^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1498121611 10000000000 2225626710957 25000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5525376149/10000000000 : ℝ)^4759 ≤ (11739968359111/25000000000000 : ℝ)^3735 := by
    have hnat : (5525376149 : ℕ)^4759*25000000000000^3735 ≤ 11739968359111^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5525376149 10000000000 11739968359111 25000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052605941/2000000000 : ℝ), (-1498121611/10000000000 : ℝ), (5525376149/10000000000 : ℝ)] ![(275860123199/625000000000 : ℝ), (2225626710957/25000000000000 : ℝ), (11739968359111/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052605941/2000000000 : ℝ)|^4759 ≤ (275860123199/625000000000 : ℝ)^3735
        have hw : |(1052605941/2000000000 : ℝ)|=(1052605941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1498121611/10000000000 : ℝ)|^4759 ≤ (2225626710957/25000000000000 : ℝ)^3735
        have hw : |(-1498121611/10000000000 : ℝ)|=(1498121611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5525376149/10000000000 : ℝ)|^4759 ≤ (11739968359111/25000000000000 : ℝ)^3735
        have hw : |(5525376149/10000000000 : ℝ)|=(5525376149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s1_6 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1315757267/2500000000 : ℝ)*x 0 + (552537639/1000000000 : ℝ)*x 1 + (-299624433/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1315757267/2500000000 : ℝ)^4759 ≤ (11034403226281/25000000000000 : ℝ)^3735 := by
    have hnat : (1315757267 : ℕ)^4759*25000000000000^3735 ≤ 11034403226281^3735*2500000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315757267 2500000000 11034403226281 25000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (552537639/1000000000 : ℝ)^4759 ≤ (11739969011561/25000000000000 : ℝ)^3735 := by
    have hnat : (552537639 : ℕ)^4759*25000000000000^3735 ≤ 11739969011561^3735*1000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552537639 1000000000 11739969011561 25000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (299624433/2000000000 : ℝ)^4759 ≤ (222562775963/2500000000000 : ℝ)^3735 := by
    have hnat : (299624433 : ℕ)^4759*2500000000000^3735 ≤ 222562775963^3735*2000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299624433 2000000000 222562775963 2500000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1315757267/2500000000 : ℝ), (552537639/1000000000 : ℝ), (-299624433/2000000000 : ℝ)] ![(11034403226281/25000000000000 : ℝ), (11739969011561/25000000000000 : ℝ), (222562775963/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1315757267/2500000000 : ℝ)|^4759 ≤ (11034403226281/25000000000000 : ℝ)^3735
        have hw : |(1315757267/2500000000 : ℝ)|=(1315757267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(552537639/1000000000 : ℝ)|^4759 ≤ (11739969011561/25000000000000 : ℝ)^3735
        have hw : |(552537639/1000000000 : ℝ)|=(552537639/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-299624433/2000000000 : ℝ)|^4759 ≤ (222562775963/2500000000000 : ℝ)^3735
        have hw : |(-299624433/2000000000 : ℝ)|=(299624433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s1_7 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050465873/2500000000 : ℝ)*x 0 + (2358308977/5000000000 : ℝ)*x 1 + (3732444433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050465873/2500000000 : ℝ)^4759 ≤ (8282158541089/25000000000000 : ℝ)^3735 := by
    have hnat : (1050465873 : ℕ)^4759*25000000000000^3735 ≤ 8282158541089^3735*2500000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050465873 2500000000 8282158541089 25000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2358308977/5000000000 : ℝ)^4759 ≤ (2399010928143/6250000000000 : ℝ)^3735 := by
    have hnat : (2358308977 : ℕ)^4759*6250000000000^3735 ≤ 2399010928143^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2358308977 5000000000 2399010928143 6250000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3732444433/10000000000 : ℝ)^4759 ≤ (2848719096989/10000000000000 : ℝ)^3735 := by
    have hnat : (3732444433 : ℕ)^4759*10000000000000^3735 ≤ 2848719096989^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3732444433 10000000000 2848719096989 10000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050465873/2500000000 : ℝ), (2358308977/5000000000 : ℝ), (3732444433/10000000000 : ℝ)] ![(8282158541089/25000000000000 : ℝ), (2399010928143/6250000000000 : ℝ), (2848719096989/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050465873/2500000000 : ℝ)|^4759 ≤ (8282158541089/25000000000000 : ℝ)^3735
        have hw : |(1050465873/2500000000 : ℝ)|=(1050465873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2358308977/5000000000 : ℝ)|^4759 ≤ (2399010928143/6250000000000 : ℝ)^3735
        have hw : |(2358308977/5000000000 : ℝ)|=(2358308977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3732444433/10000000000 : ℝ)|^4759 ≤ (2848719096989/10000000000000 : ℝ)^3735
        have hw : |(3732444433/10000000000 : ℝ)|=(3732444433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1610_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34573411/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12121/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2011/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9131/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1113/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (12121/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2011/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (12121/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2011/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (12121/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2011/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (12121/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2011/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (12121/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2011/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (12121/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2011/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2011/50000 : ℝ) ^ (4755/1024 : ℝ) ≤ (33086468507799/100000000000000000000 : ℝ) := by
    have hpowers : (2011/50000 : ℝ)^4755 ≤ (33086468507799/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2011 : ℕ)^4755*100000000000000000000^1024 ≤ 33086468507799^1024*50000^4755 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2011 50000 33086468507799 100000000000000000000 4755 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2011/50000 : ℝ)) (X := (33086468507799/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (12121/50000 : ℝ) ^ (4755/1024 : ℝ) ≤ (138742631287010203/100000000000000000000 : ℝ) := by
    have hpowers : (12121/50000 : ℝ)^4755 ≤ (138742631287010203/100000000000000000000 : ℝ)^1024 := by
      have hnat : (12121 : ℕ)^4755*100000000000000000000^1024 ≤ 138742631287010203^1024*50000^4755 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12121 50000 138742631287010203 100000000000000000000 4755 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12121/50000 : ℝ)) (X := (138742631287010203/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000033086468507799/50000000000000000000 : ℝ) ≤ (10000001425048789/10000000000000000 : ℝ) ^ (4755/1024 : ℝ) := by
    have hpowers : (50000033086468507799/50000000000000000000 : ℝ)^1024 ≤ (10000001425048789/10000000000000000 : ℝ)^4755 := by
      have hnat : (50000033086468507799 : ℕ)^1024*10000000000000000^4755 ≤ 10000001425048789^4755*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000033086468507799 50000000000000000000 10000001425048789 10000000000000000 1024 4755 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001425048789/10000000000000000 : ℝ)) (X := (50000033086468507799/50000000000000000000 : ℝ)) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50069387858877759001/50000000000000000000 : ℝ) ≤ (2500746735168039/2500000000000000 : ℝ) ^ (4755/1024 : ℝ) := by
    have hpowers : (50069387858877759001/50000000000000000000 : ℝ)^1024 ≤ (2500746735168039/2500000000000000 : ℝ)^4755 := by
      have hnat : (50069387858877759001 : ℕ)^1024*2500000000000000^4755 ≤ 2500746735168039^4755*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50069387858877759001 50000000000000000000 2500746735168039 2500000000000000 1024 4755 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500746735168039/2500000000000000 : ℝ)) (X := (50069387858877759001/50000000000000000000 : ℝ)) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50138742631287010203/50000000000000000000 : ℝ) ≤ (10005972456295523/10000000000000000 : ℝ) ^ (4755/1024 : ℝ) := by
    have hpowers : (50138742631287010203/50000000000000000000 : ℝ)^1024 ≤ (10005972456295523/10000000000000000 : ℝ)^4755 := by
      have hnat : (50138742631287010203 : ℕ)^1024*10000000000000000^4755 ≤ 10005972456295523^4755*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50138742631287010203 50000000000000000000 10005972456295523 10000000000000000 1024 4755 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005972456295523/10000000000000000 : ℝ)) (X := (50138742631287010203/50000000000000000000 : ℝ)) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(33086468507799/100000000000000000000 : ℝ) ≤ ((25272001665851518679/25275000000000000000 : ℝ)+2*(2985515623367/2022000000000000 : ℝ)*(2011/50000 : ℝ))^(4755/1024 : ℝ) := by
    rw [show (25272001665851518679/25275000000000000000 : ℝ)+2*(2985515623367/2022000000000000 : ℝ)*(2011/50000 : ℝ)=(10000001425048789/10000000000000000 : ℝ) by norm_num, show 1+2*(33086468507799/100000000000000000000 : ℝ)=(50000033086468507799/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(138742631287010203/100000000000000000000 : ℝ)+(33086468507799/100000000000000000000 : ℝ) ≤ ((25272001665851518679/25275000000000000000 : ℝ)+(2985515623367/2022000000000000 : ℝ)*((12121/50000 : ℝ)+(2011/50000 : ℝ)))^(4755/1024 : ℝ) := by
    rw [show (25272001665851518679/25275000000000000000 : ℝ)+(2985515623367/2022000000000000 : ℝ)*((12121/50000 : ℝ)+(2011/50000 : ℝ))=(2500746735168039/2500000000000000 : ℝ) by norm_num, show 1+(138742631287010203/100000000000000000000 : ℝ)+(33086468507799/100000000000000000000 : ℝ)=(50069387858877759001/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(138742631287010203/100000000000000000000 : ℝ) ≤ ((25272001665851518679/25275000000000000000 : ℝ)+2*(2985515623367/2022000000000000 : ℝ)*(12121/50000 : ℝ))^(4755/1024 : ℝ) := by
    rw [show (25272001665851518679/25275000000000000000 : ℝ)+2*(2985515623367/2022000000000000 : ℝ)*(12121/50000 : ℝ)=(10005972456295523/10000000000000000 : ℝ) by norm_num, show 1+2*(138742631287010203/100000000000000000000 : ℝ)=(50138742631287010203/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (25272001665851518679/25275000000000000000 : ℝ)*(X 1 0+X 2 0)+(2985515623367/2022000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4755/1024 : ℝ)) (lo := (2011/50000 : ℝ)) (hi := (12121/50000 : ℝ)) (c := (25272001665851518679/25275000000000000000 : ℝ)) (alpha := (2985515623367/2022000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (25272001665851518679/25275000000000000000 : ℝ)*(X 0 1+X 2 1)+(2985515623367/2022000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4755/1024 : ℝ)) (lo := (2011/50000 : ℝ)) (hi := (12121/50000 : ℝ)) (c := (25272001665851518679/25275000000000000000 : ℝ)) (alpha := (2985515623367/2022000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (25272001665851518679/25275000000000000000 : ℝ)*(X 0 2+X 1 2)+(2985515623367/2022000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4755/1024 : ℝ)) (lo := (2011/50000 : ℝ)) (hi := (12121/50000 : ℝ)) (c := (25272001665851518679/25275000000000000000 : ℝ)) (alpha := (2985515623367/2022000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-168892657/1000000000 : ℝ)*X 0 0+(138247521/250000000 : ℝ)*X 0 1+(5120417407/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((537196313/1000000000 : ℝ)*X 1 0+(-1903080487/10000000000 : ℝ)*X 1 1+(256020863/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5371962867/10000000000 : ℝ)*X 2 0+(256020873/500000000 : ℝ)*X 2 1+(-951540287/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4201317323/10000000000 : ℝ)*X 0 0+(1860662981/5000000000 : ℝ)*X 0 1+(4727566829/10000000000 : ℝ)*X 0 2+(4201317323/10000000000 : ℝ)*X 1 0+(1860662981/5000000000 : ℝ)*X 1 1+(4727566829/10000000000 : ℝ)*X 1 2+(4201317323/10000000000 : ℝ)*X 2 0+(1860662981/5000000000 : ℝ)*X 2 1+(4727566829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1689149347/10000000000 : ℝ)*X 0 0+(1281218367/2500000000 : ℝ)*X 0 1+(276268791/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1052605941/2000000000 : ℝ)*X 1 0+(-1498121611/10000000000 : ℝ)*X 1 1+(5525376149/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1315757267/2500000000 : ℝ)*X 2 0+(552537639/1000000000 : ℝ)*X 2 1+(-299624433/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1050465873/2500000000 : ℝ)*X 0 0+(2358308977/5000000000 : ℝ)*X 0 1+(3732444433/10000000000 : ℝ)*X 0 2+(1050465873/2500000000 : ℝ)*X 1 0+(2358308977/5000000000 : ℝ)*X 1 1+(3732444433/10000000000 : ℝ)*X 1 2+(1050465873/2500000000 : ℝ)*X 2 0+(2358308977/5000000000 : ℝ)*X 2 1+(3732444433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1018320526814535164532419199/421250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12353717/12500000000000 : ℝ)*(base1) + (722731833/100000000000000 : ℝ)*(base19) + (150792813/25000000000000 : ℝ)*(base23) + (947327/1000000000000 : ℝ)*(upper3) + (4823129/20000000000000 : ℝ)*(upper5) + (1717956664442373/100000000000000 : ℝ)*(major0) + (1717956664442373/100000000000000 : ℝ)*(major1) + (1717956664442373/100000000000000 : ℝ)*(major2) + (2442106874166307/100000000000000 : ℝ)*(sp0) + (1221055142893737/50000000000000 : ℝ)*(sp1) + (305263800668507/12500000000000 : ℝ)*(sp2) + (993799832836059/100000000000000 : ℝ)*(sp3) + (264573921/6250000000000 : ℝ)*(sp4) + (461624073/20000000000000 : ℝ)*(sp7) + (12422527997327/1250000000000 : ℝ)*(f.failure) + (610527752129827/25000000000000 : ℝ)*(f.sum) + (22998640849797/33700000000000000000000000000 : ℝ)*base65 + (10000890792237407589/842500000000000000000000000000000 : ℝ)*base67 + (7385205366054907589/842500000000000000000000000000000 : ℝ)*base69 + (4848788487594907589/842500000000000000000000000000000 : ℝ)*base71 + (164327581962297/33700000000000000000000000000 : ℝ)*base73 + (10376205248987407589/842500000000000000000000000000000 : ℝ)*base75 + (3417547017384907589/842500000000000000000000000000000 : ℝ)*base77 + (2402879160777407589/842500000000000000000000000000000 : ℝ)*base79 + (208834373878897/33700000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (22397/25000000000000000000 : ℝ)*base89 + (22397/25000000000000000000 : ℝ)*base91 + (22397/25000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15294917706967895068431181/3291015625000000000000000000000 : ℝ) := by norm_num
    linear_combination (1025534359/100000000000000 : ℝ)*(base19) + (817390029/100000000000000 : ℝ)*(base23) + (57311361/100000000000000 : ℝ)*(upper2) + (230674529/100000000000000 : ℝ)*(upper3) + (10855643/50000000000000 : ℝ)*(upper5) + (109779404811221/6250000000000 : ℝ)*(major0) + (109779404811221/6250000000000 : ℝ)*(major1) + (109779404811221/6250000000000 : ℝ)*(major2) + (1532798487/20000000000000 : ℝ)*(sp1) + (6947157619/100000000000000 : ℝ)*(sp2) + (1248429559414859/50000000000000 : ℝ)*(sp4) + (624212607325731/25000000000000 : ℝ)*(sp5) + (2496851354282071/100000000000000 : ℝ)*(sp6) + (508040840106733/50000000000000 : ℝ)*(sp7) + (508040840106733/50000000000000 : ℝ)*(f.failure) + (1248429559414859/50000000000000 : ℝ)*(f.sum) + (9578538972389/12637500000000000000000000000 : ℝ)*base65 + (7139841113669853/52656250000000000000000000000000 : ℝ)*base67 + (444267651402732353/52656250000000000000000000000000 : ℝ)*base69 + (234184552457732353/52656250000000000000000000000000 : ℝ)*base71 + (198861862863197/25275000000000000000000000000 : ℝ)*base74 + (385589157903982353/52656250000000000000000000000000 : ℝ)*base75 + (469342387309763603/52656250000000000000000000000000 : ℝ)*base77 + (48463970828982353/52656250000000000000000000000000 : ℝ)*base79 + (30706671203747/25275000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (3876263/1000000000000000000000 : ℝ)*base89 + (3876263/1000000000000000000000 : ℝ)*base91 + (3876263/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1610_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34573411/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12121/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2011/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9131/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1113/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1610_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1610_s2_0 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-851415029/5000000000 : ℝ)*x 0 + (1366681547/2500000000 : ℝ)*x 1 + (1293622453/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (851415029/5000000000 : ℝ)^4759 ≤ (2096122581013/20000000000000 : ℝ)^3735 := by
    have hnat : (851415029 : ℕ)^4759*20000000000000^3735 ≤ 2096122581013^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851415029 5000000000 2096122581013 20000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366681547/2500000000 : ℝ)^4759 ≤ (4632567689163/10000000000000 : ℝ)^3735 := by
    have hnat : (1366681547 : ℕ)^4759*10000000000000^3735 ≤ 4632567689163^3735*2500000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366681547 2500000000 4632567689163 10000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1293622453/2500000000 : ℝ)^4759 ≤ (21596855092321/50000000000000 : ℝ)^3735 := by
    have hnat : (1293622453 : ℕ)^4759*50000000000000^3735 ≤ 21596855092321^3735*2500000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293622453 2500000000 21596855092321 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-851415029/5000000000 : ℝ), (1366681547/2500000000 : ℝ), (1293622453/2500000000 : ℝ)] ![(2096122581013/20000000000000 : ℝ), (4632567689163/10000000000000 : ℝ), (21596855092321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-851415029/5000000000 : ℝ)|^4759 ≤ (2096122581013/20000000000000 : ℝ)^3735
        have hw : |(-851415029/5000000000 : ℝ)|=(851415029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366681547/2500000000 : ℝ)|^4759 ≤ (4632567689163/10000000000000 : ℝ)^3735
        have hw : |(1366681547/2500000000 : ℝ)|=(1366681547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1293622453/2500000000 : ℝ)|^4759 ≤ (21596855092321/50000000000000 : ℝ)^3735
        have hw : |(1293622453/2500000000 : ℝ)|=(1293622453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s2_1 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071100183/2000000000 : ℝ)*x 0 + (-1853743317/10000000000 : ℝ)*x 1 + (64681121/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071100183/2000000000 : ℝ)^4759 ≤ (22564049128483/50000000000000 : ℝ)^3735 := by
    have hnat : (1071100183 : ℕ)^4759*50000000000000^3735 ≤ 22564049128483^3735*2000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071100183 2000000000 22564049128483 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1853743317/10000000000 : ℝ)^4759 ≤ (2919548235477/25000000000000 : ℝ)^3735 := by
    have hnat : (1853743317 : ℕ)^4759*25000000000000^3735 ≤ 2919548235477^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1853743317 10000000000 2919548235477 25000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64681121/125000000 : ℝ)^4759 ≤ (43193708780691/100000000000000 : ℝ)^3735 := by
    have hnat : (64681121 : ℕ)^4759*100000000000000^3735 ≤ 43193708780691^3735*125000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64681121 125000000 43193708780691 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071100183/2000000000 : ℝ), (-1853743317/10000000000 : ℝ), (64681121/125000000 : ℝ)] ![(22564049128483/50000000000000 : ℝ), (2919548235477/25000000000000 : ℝ), (43193708780691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071100183/2000000000 : ℝ)|^4759 ≤ (22564049128483/50000000000000 : ℝ)^3735
        have hw : |(1071100183/2000000000 : ℝ)|=(1071100183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1853743317/10000000000 : ℝ)|^4759 ≤ (2919548235477/25000000000000 : ℝ)^3735
        have hw : |(-1853743317/10000000000 : ℝ)|=(1853743317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(64681121/125000000 : ℝ)|^4759 ≤ (43193708780691/100000000000000 : ℝ)^3735
        have hw : |(64681121/125000000 : ℝ)|=(64681121/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s2_2 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071100167/2000000000 : ℝ)*x 0 + (5174489737/10000000000 : ℝ)*x 1 + (-1853743349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071100167/2000000000 : ℝ)^4759 ≤ (11282024349507/25000000000000 : ℝ)^3735 := by
    have hnat : (1071100167 : ℕ)^4759*25000000000000^3735 ≤ 11282024349507^3735*2000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071100167 2000000000 11282024349507 25000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5174489737/10000000000 : ℝ)^4759 ≤ (21596854693471/50000000000000 : ℝ)^3735 := by
    have hnat : (5174489737 : ℕ)^4759*50000000000000^3735 ≤ 21596854693471^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174489737 10000000000 21596854693471 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1853743349/10000000000 : ℝ)^4759 ≤ (11678193198771/100000000000000 : ℝ)^3735 := by
    have hnat : (1853743349 : ℕ)^4759*100000000000000^3735 ≤ 11678193198771^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1853743349 10000000000 11678193198771 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071100167/2000000000 : ℝ), (5174489737/10000000000 : ℝ), (-1853743349/10000000000 : ℝ)] ![(11282024349507/25000000000000 : ℝ), (21596854693471/50000000000000 : ℝ), (11678193198771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071100167/2000000000 : ℝ)|^4759 ≤ (11282024349507/25000000000000 : ℝ)^3735
        have hw : |(1071100167/2000000000 : ℝ)|=(1071100167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5174489737/10000000000 : ℝ)|^4759 ≤ (21596854693471/50000000000000 : ℝ)^3735
        have hw : |(5174489737/10000000000 : ℝ)|=(5174489737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1853743349/10000000000 : ℝ)|^4759 ≤ (11678193198771/100000000000000 : ℝ)^3735
        have hw : |(-1853743349/10000000000 : ℝ)|=(1853743349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s2_3 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2105788773/5000000000 : ℝ)*x 0 + (386429867/1000000000 : ℝ)*x 1 + (4582423151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105788773/5000000000 : ℝ)^4759 ≤ (33226251002853/100000000000000 : ℝ)^3735 := by
    have hnat : (2105788773 : ℕ)^4759*100000000000000^3735 ≤ 33226251002853^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105788773 5000000000 33226251002853 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (386429867/1000000000 : ℝ)^4759 ≤ (7443901578797/25000000000000 : ℝ)^3735 := by
    have hnat : (386429867 : ℕ)^4759*25000000000000^3735 ≤ 7443901578797^3735*1000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386429867 1000000000 7443901578797 25000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4582423151/10000000000 : ℝ)^4759 ≤ (36998142662177/100000000000000 : ℝ)^3735 := by
    have hnat : (4582423151 : ℕ)^4759*100000000000000^3735 ≤ 36998142662177^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4582423151 10000000000 36998142662177 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2105788773/5000000000 : ℝ), (386429867/1000000000 : ℝ), (4582423151/10000000000 : ℝ)] ![(33226251002853/100000000000000 : ℝ), (7443901578797/25000000000000 : ℝ), (36998142662177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2105788773/5000000000 : ℝ)|^4759 ≤ (33226251002853/100000000000000 : ℝ)^3735
        have hw : |(2105788773/5000000000 : ℝ)|=(2105788773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(386429867/1000000000 : ℝ)|^4759 ≤ (7443901578797/25000000000000 : ℝ)^3735
        have hw : |(386429867/1000000000 : ℝ)|=(386429867/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4582423151/10000000000 : ℝ)|^4759 ≤ (36998142662177/100000000000000 : ℝ)^3735
        have hw : |(4582423151/10000000000 : ℝ)|=(4582423151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s2_4 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-170291077/1000000000 : ℝ)*x 0 + (2588383343/5000000000 : ℝ)*x 1 + (2732212231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170291077/1000000000 : ℝ)^4759 ≤ (1310155734069/12500000000000 : ℝ)^3735 := by
    have hnat : (170291077 : ℕ)^4759*12500000000000^3735 ≤ 1310155734069^3735*1000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170291077 1000000000 1310155734069 12500000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588383343/5000000000 : ℝ)^4759 ≤ (21608964231393/50000000000000 : ℝ)^3735 := by
    have hnat : (2588383343 : ℕ)^4759*50000000000000^3735 ≤ 21608964231393^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588383343 5000000000 21608964231393 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2732212231/5000000000 : ℝ)^4759 ≤ (11575206412323/25000000000000 : ℝ)^3735 := by
    have hnat : (2732212231 : ℕ)^4759*25000000000000^3735 ≤ 11575206412323^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732212231 5000000000 11575206412323 25000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-170291077/1000000000 : ℝ), (2588383343/5000000000 : ℝ), (2732212231/5000000000 : ℝ)] ![(1310155734069/12500000000000 : ℝ), (21608964231393/50000000000000 : ℝ), (11575206412323/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-170291077/1000000000 : ℝ)|^4759 ≤ (1310155734069/12500000000000 : ℝ)^3735
        have hw : |(-170291077/1000000000 : ℝ)|=(170291077/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588383343/5000000000 : ℝ)|^4759 ≤ (21608964231393/50000000000000 : ℝ)^3735
        have hw : |(2588383343/5000000000 : ℝ)|=(2588383343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2732212231/5000000000 : ℝ)|^4759 ≤ (11575206412323/25000000000000 : ℝ)^3735
        have hw : |(2732212231/5000000000 : ℝ)|=(2732212231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s2_5 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055575671/2000000000 : ℝ)*x 0 + (-1563808677/10000000000 : ℝ)*x 1 + (546442469/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055575671/2000000000 : ℝ)^4759 ≤ (22148173751551/50000000000000 : ℝ)^3735 := by
    have hnat : (1055575671 : ℕ)^4759*50000000000000^3735 ≤ 22148173751551^3735*2000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055575671 2000000000 22148173751551 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1563808677/10000000000 : ℝ)^4759 ≤ (1175353045947/12500000000000 : ℝ)^3735 := by
    have hnat : (1563808677 : ℕ)^4759*12500000000000^3735 ≤ 1175353045947^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1563808677 10000000000 1175353045947 12500000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546442469/1000000000 : ℝ)^4759 ≤ (46300828110817/100000000000000 : ℝ)^3735 := by
    have hnat : (546442469 : ℕ)^4759*100000000000000^3735 ≤ 46300828110817^3735*1000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546442469 1000000000 46300828110817 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055575671/2000000000 : ℝ), (-1563808677/10000000000 : ℝ), (546442469/1000000000 : ℝ)] ![(22148173751551/50000000000000 : ℝ), (1175353045947/12500000000000 : ℝ), (46300828110817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055575671/2000000000 : ℝ)|^4759 ≤ (22148173751551/50000000000000 : ℝ)^3735
        have hw : |(1055575671/2000000000 : ℝ)|=(1055575671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1563808677/10000000000 : ℝ)|^4759 ≤ (1175353045947/12500000000000 : ℝ)^3735
        have hw : |(-1563808677/10000000000 : ℝ)|=(1563808677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(546442469/1000000000 : ℝ)|^4759 ≤ (46300828110817/100000000000000 : ℝ)^3735
        have hw : |(546442469/1000000000 : ℝ)|=(546442469/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s2_6 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659734863/1250000000 : ℝ)*x 0 + (683052989/1250000000 : ℝ)*x 1 + (-97738063/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659734863/1250000000 : ℝ)^4759 ≤ (44296353374019/100000000000000 : ℝ)^3735 := by
    have hnat : (659734863 : ℕ)^4759*100000000000000^3735 ≤ 44296353374019^3735*1250000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659734863 1250000000 44296353374019 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (683052989/1250000000 : ℝ)^4759 ≤ (46300819711403/100000000000000 : ℝ)^3735 := by
    have hnat : (683052989 : ℕ)^4759*100000000000000^3735 ≤ 46300819711403^3735*1250000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683052989 1250000000 46300819711403 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (97738063/625000000 : ℝ)^4759 ≤ (9402826903451/100000000000000 : ℝ)^3735 := by
    have hnat : (97738063 : ℕ)^4759*100000000000000^3735 ≤ 9402826903451^3735*625000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97738063 625000000 9402826903451 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659734863/1250000000 : ℝ), (683052989/1250000000 : ℝ), (-97738063/625000000 : ℝ)] ![(44296353374019/100000000000000 : ℝ), (46300819711403/100000000000000 : ℝ), (9402826903451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659734863/1250000000 : ℝ)|^4759 ≤ (44296353374019/100000000000000 : ℝ)^3735
        have hw : |(659734863/1250000000 : ℝ)|=(659734863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(683052989/1250000000 : ℝ)|^4759 ≤ (46300819711403/100000000000000 : ℝ)^3735
        have hw : |(683052989/1250000000 : ℝ)|=(683052989/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-97738063/625000000 : ℝ)|^4759 ≤ (9402826903451/100000000000000 : ℝ)^3735
        have hw : |(-97738063/625000000 : ℝ)|=(97738063/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_s2_7 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33694213/80000000 : ℝ)*x 0 + (4576828407/10000000000 : ℝ)*x 1 + (967488779/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33694213/80000000 : ℝ)^4759 ≤ (3322825220013/10000000000000 : ℝ)^3735 := by
    have hnat : (33694213 : ℕ)^4759*10000000000000^3735 ≤ 3322825220013^3735*80000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33694213 80000000 3322825220013 10000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4576828407/10000000000 : ℝ)^4759 ≤ (36940596371261/100000000000000 : ℝ)^3735 := by
    have hnat : (4576828407 : ℕ)^4759*100000000000000^3735 ≤ 36940596371261^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4576828407 10000000000 36940596371261 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (967488779/2500000000 : ℝ)^4759 ≤ (29831151418203/100000000000000 : ℝ)^3735 := by
    have hnat : (967488779 : ℕ)^4759*100000000000000^3735 ≤ 29831151418203^3735*2500000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967488779 2500000000 29831151418203 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33694213/80000000 : ℝ), (4576828407/10000000000 : ℝ), (967488779/2500000000 : ℝ)] ![(3322825220013/10000000000000 : ℝ), (36940596371261/100000000000000 : ℝ), (29831151418203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33694213/80000000 : ℝ)|^4759 ≤ (3322825220013/10000000000000 : ℝ)^3735
        have hw : |(33694213/80000000 : ℝ)|=(33694213/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4576828407/10000000000 : ℝ)|^4759 ≤ (36940596371261/100000000000000 : ℝ)^3735
        have hw : |(4576828407/10000000000 : ℝ)|=(4576828407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(967488779/2500000000 : ℝ)|^4759 ≤ (29831151418203/100000000000000 : ℝ)^3735
        have hw : |(967488779/2500000000 : ℝ)|=(967488779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1610_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34573411/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1113/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9131/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5149/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8247/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1113/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9131/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1113/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9131/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1113/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9131/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1113/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9131/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1113/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9131/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1113/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9131/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9131/100000 : ℝ) ^ (4755/1024 : ℝ) ≤ (1489738625083991/100000000000000000000 : ℝ) := by
    have hpowers : (9131/100000 : ℝ)^4755 ≤ (1489738625083991/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9131 : ℕ)^4755*100000000000000000000^1024 ≤ 1489738625083991^1024*100000^4755 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9131 100000 1489738625083991 100000000000000000000 4755 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9131/100000 : ℝ)) (X := (1489738625083991/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1113/6250 : ℝ) ^ (4755/1024 : ℝ) ≤ (16563818285640391/50000000000000000000 : ℝ) := by
    have hpowers : (1113/6250 : ℝ)^4755 ≤ (16563818285640391/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1113 : ℕ)^4755*50000000000000000000^1024 ≤ 16563818285640391^1024*6250^4755 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1113 6250 16563818285640391 50000000000000000000 4755 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1113/6250 : ℝ)) (X := (16563818285640391/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001489738625083991/50000000000000000000 : ℝ) ≤ (10000064162966167/10000000000000000 : ℝ) ^ (4755/1024 : ℝ) := by
    have hpowers : (50001489738625083991/50000000000000000000 : ℝ)^1024 ≤ (10000064162966167/10000000000000000 : ℝ)^4755 := by
      have hnat : (50001489738625083991 : ℕ)^1024*10000000000000000^4755 ≤ 10000064162966167^4755*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001489738625083991 50000000000000000000 10000064162966167 10000000000000000 1024 4755 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000064162966167/10000000000000000 : ℝ)) (X := (50001489738625083991/50000000000000000000 : ℝ)) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034617375196364773/100000000000000000000 : ℝ) ≤ (1250093173971857/1250000000000000 : ℝ) ^ (4755/1024 : ℝ) := by
    have hpowers : (100034617375196364773/100000000000000000000 : ℝ)^1024 ≤ (1250093173971857/1250000000000000 : ℝ)^4755 := by
      have hnat : (100034617375196364773 : ℕ)^1024*1250000000000000^4755 ≤ 1250093173971857^4755*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034617375196364773 100000000000000000000 1250093173971857 1250000000000000 1024 4755 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250093173971857/1250000000000000 : ℝ)) (X := (100034617375196364773/100000000000000000000 : ℝ)) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016563818285640391/25000000000000000000 : ℝ) ≤ (2000285324116709/2000000000000000 : ℝ) ^ (4755/1024 : ℝ) := by
    have hpowers : (25016563818285640391/25000000000000000000 : ℝ)^1024 ≤ (2000285324116709/2000000000000000 : ℝ)^4755 := by
      have hnat : (25016563818285640391 : ℕ)^1024*2000000000000000^4755 ≤ 2000285324116709^4755*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016563818285640391 25000000000000000000 2000285324116709 2000000000000000 1024 4755 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000285324116709/2000000000000000 : ℝ)) (X := (25016563818285640391/25000000000000000000 : ℝ)) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1489738625083991/100000000000000000000 : ℝ) ≤ ((86758116141553152541/86770000000000000000 : ℝ)+2*(681228808689/867700000000000 : ℝ)*(9131/100000 : ℝ))^(4755/1024 : ℝ) := by
    rw [show (86758116141553152541/86770000000000000000 : ℝ)+2*(681228808689/867700000000000 : ℝ)*(9131/100000 : ℝ)=(10000064162966167/10000000000000000 : ℝ) by norm_num, show 1+2*(1489738625083991/100000000000000000000 : ℝ)=(50001489738625083991/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16563818285640391/50000000000000000000 : ℝ)+(1489738625083991/100000000000000000000 : ℝ) ≤ ((86758116141553152541/86770000000000000000 : ℝ)+(681228808689/867700000000000 : ℝ)*((1113/6250 : ℝ)+(9131/100000 : ℝ)))^(4755/1024 : ℝ) := by
    rw [show (86758116141553152541/86770000000000000000 : ℝ)+(681228808689/867700000000000 : ℝ)*((1113/6250 : ℝ)+(9131/100000 : ℝ))=(1250093173971857/1250000000000000 : ℝ) by norm_num, show 1+(16563818285640391/50000000000000000000 : ℝ)+(1489738625083991/100000000000000000000 : ℝ)=(100034617375196364773/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16563818285640391/50000000000000000000 : ℝ) ≤ ((86758116141553152541/86770000000000000000 : ℝ)+2*(681228808689/867700000000000 : ℝ)*(1113/6250 : ℝ))^(4755/1024 : ℝ) := by
    rw [show (86758116141553152541/86770000000000000000 : ℝ)+2*(681228808689/867700000000000 : ℝ)*(1113/6250 : ℝ)=(2000285324116709/2000000000000000 : ℝ) by norm_num, show 1+2*(16563818285640391/50000000000000000000 : ℝ)=(25016563818285640391/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (86758116141553152541/86770000000000000000 : ℝ)*(X 1 0+X 2 0)+(681228808689/867700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4755/1024 : ℝ)) (lo := (9131/100000 : ℝ)) (hi := (1113/6250 : ℝ)) (c := (86758116141553152541/86770000000000000000 : ℝ)) (alpha := (681228808689/867700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (86758116141553152541/86770000000000000000 : ℝ)*(X 0 1+X 2 1)+(681228808689/867700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4755/1024 : ℝ)) (lo := (9131/100000 : ℝ)) (hi := (1113/6250 : ℝ)) (c := (86758116141553152541/86770000000000000000 : ℝ)) (alpha := (681228808689/867700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (86758116141553152541/86770000000000000000 : ℝ)*(X 0 2+X 1 2)+(681228808689/867700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4755/1024 : ℝ)) (lo := (9131/100000 : ℝ)) (hi := (1113/6250 : ℝ)) (c := (86758116141553152541/86770000000000000000 : ℝ)) (alpha := (681228808689/867700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-851415029/5000000000 : ℝ)*X 0 0+(1366681547/2500000000 : ℝ)*X 0 1+(1293622453/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1071100183/2000000000 : ℝ)*X 1 0+(-1853743317/10000000000 : ℝ)*X 1 1+(64681121/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071100167/2000000000 : ℝ)*X 2 0+(5174489737/10000000000 : ℝ)*X 2 1+(-1853743349/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2105788773/5000000000 : ℝ)*X 0 0+(386429867/1000000000 : ℝ)*X 0 1+(4582423151/10000000000 : ℝ)*X 0 2+(2105788773/5000000000 : ℝ)*X 1 0+(386429867/1000000000 : ℝ)*X 1 1+(4582423151/10000000000 : ℝ)*X 1 2+(2105788773/5000000000 : ℝ)*X 2 0+(386429867/1000000000 : ℝ)*X 2 1+(4582423151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-170291077/1000000000 : ℝ)*X 0 0+(2588383343/5000000000 : ℝ)*X 0 1+(2732212231/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1055575671/2000000000 : ℝ)*X 1 0+(-1563808677/10000000000 : ℝ)*X 1 1+(546442469/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((659734863/1250000000 : ℝ)*X 2 0+(683052989/1250000000 : ℝ)*X 2 1+(-97738063/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((33694213/80000000 : ℝ)*X 0 0+(4576828407/10000000000 : ℝ)*X 0 1+(967488779/2500000000 : ℝ)*X 0 2+(33694213/80000000 : ℝ)*X 1 0+(4576828407/10000000000 : ℝ)*X 1 1+(967488779/2500000000 : ℝ)*X 1 2+(33694213/80000000 : ℝ)*X 2 0+(4576828407/10000000000 : ℝ)*X 2 1+(967488779/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11462989733071114171538397741/1084625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1955435631/100000000000000 : ℝ)*(base19) + (1851758323/100000000000000 : ℝ)*(base23) + (28148953/100000000000000 : ℝ)*(lower2) + (68103551/25000000000000 : ℝ)*(upper3) + (50424337/25000000000000 : ℝ)*(upper5) + (601808310760311/25000000000000 : ℝ)*(major0) + (601808310760311/25000000000000 : ℝ)*(major1) + (601808310760311/25000000000000 : ℝ)*(major2) + (427738765185069/12500000000000 : ℝ)*(sp0) + (213870609849531/6250000000000 : ℝ)*(sp1) + (855482465317451/25000000000000 : ℝ)*(sp2) + (696262486283617/50000000000000 : ℝ)*(sp3) + (863661903/4000000000000 : ℝ)*(sp4) + (4724099889/50000000000000 : ℝ)*(sp7) + (1392534420767013/100000000000000 : ℝ)*(f.failure) + (3421931713028127/100000000000000 : ℝ)*(f.sum) + (59892629009909/10846250000000000000000000000 : ℝ)*base65 + (11334490720048500251/2169250000000000000000000000000000 : ℝ)*base67 + (9629981265221500251/2169250000000000000000000000000000 : ℝ)*base69 + (11690472883860000251/2169250000000000000000000000000000 : ℝ)*base71 + (159558002398713/21692500000000000000000000000 : ℝ)*base73 + (4748029028256000251/2169250000000000000000000000000000 : ℝ)*base75 + (13952669823235000251/2169250000000000000000000000000000 : ℝ)*base77 + (2243555905800000251/2169250000000000000000000000000000 : ℝ)*base79 + (145168460575753/21692500000000000000000000000 : ℝ)*base81 + (4308657/2000000000000000000000 : ℝ)*base90 + (4308657/2000000000000000000000 : ℝ)*base92 + (4308657/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23120799358012292214481532541/2169250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4857447/390625000000 : ℝ)*(base19) + (462600319/25000000000000 : ℝ)*(base23) + (89513551/50000000000000 : ℝ)*(upper3) + (133122529/100000000000000 : ℝ)*(lower4) + (22354083/12500000000000 : ℝ)*(upper5) + (1222758352373333/50000000000000 : ℝ)*(major0) + (1222758352373333/50000000000000 : ℝ)*(major1) + (1222758352373333/50000000000000 : ℝ)*(major2) + (16011706931/100000000000000 : ℝ)*(sp1) + (7770001703/50000000000000 : ℝ)*(sp2) + (1738176223094313/50000000000000 : ℝ)*(sp4) + (3476335190975263/100000000000000 : ℝ)*(sp5) + (434541881972993/12500000000000 : ℝ)*(sp6) + (1414680608023701/100000000000000 : ℝ)*(sp7) + (1414680608023701/100000000000000 : ℝ)*(f.failure) + (1738176223094313/50000000000000 : ℝ)*(f.sum) + (76648012469551/43385000000000000000000000000 : ℝ)*base66 + (9841505741567789153/4338500000000000000000000000000000 : ℝ)*base67 + (2378913563345289153/4338500000000000000000000000000000 : ℝ)*base69 + (1242822101094210847/4338500000000000000000000000000000 : ℝ)*base72 + (64804440489209/43385000000000000000000000000 : ℝ)*base73 + (5069450225932289153/4338500000000000000000000000000000 : ℝ)*base75 + (14614884972599789153/4338500000000000000000000000000000 : ℝ)*base77 + (25050445417621210847/4338500000000000000000000000000000 : ℝ)*base80 + (21571056598481/10846250000000000000000000000 : ℝ)*base81 + (7585889/2000000000000000000000 : ℝ)*base90 + (7585889/2000000000000000000000 : ℝ)*base92 + (7585889/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1610_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34573411/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1113/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9131/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5149/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8247/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1610_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1610_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34573411/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5149/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8247/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1610_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1610_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1610_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34573411/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5149/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8247/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1610_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
