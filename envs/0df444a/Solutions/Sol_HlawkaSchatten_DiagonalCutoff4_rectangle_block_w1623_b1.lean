-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1623_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:58:25.284392+00:00
-- url     : https://prove2.me/submissions/fa05b745-5365-4e85-b549-5f7d1baeba2a

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
theorem support_rectangle_w1623_s3_0 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-836010383/5000000000 : ℝ)*x 0 + (1363967823/2500000000 : ℝ)*x 1 + (5181658433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (836010383/5000000000 : ℝ)^4811 ≤ (10308778262273/100000000000000 : ℝ)^3787 := by
    have hnat : (836010383 : ℕ)^4811*100000000000000^3787 ≤ 10308778262273^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836010383 5000000000 10308778262273 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363967823/2500000000 : ℝ)^4811 ≤ (23157011503489/50000000000000 : ℝ)^3787 := by
    have hnat : (1363967823 : ℕ)^4811*50000000000000^3787 ≤ 23157011503489^3787*2500000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363967823 2500000000 23157011503489 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181658433/10000000000 : ℝ)^4811 ≤ (43377198716833/100000000000000 : ℝ)^3787 := by
    have hnat : (5181658433 : ℕ)^4811*100000000000000^3787 ≤ 43377198716833^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181658433 10000000000 43377198716833 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-836010383/5000000000 : ℝ), (1363967823/2500000000 : ℝ), (5181658433/10000000000 : ℝ)] ![(10308778262273/100000000000000 : ℝ), (23157011503489/50000000000000 : ℝ), (43377198716833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-836010383/5000000000 : ℝ)|^4811 ≤ (10308778262273/100000000000000 : ℝ)^3787
        have hw : |(-836010383/5000000000 : ℝ)|=(836010383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1363967823/2500000000 : ℝ)|^4811 ≤ (23157011503489/50000000000000 : ℝ)^3787
        have hw : |(1363967823/2500000000 : ℝ)|=(1363967823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181658433/10000000000 : ℝ)|^4811 ≤ (43377198716833/100000000000000 : ℝ)^3787
        have hw : |(5181658433/10000000000 : ℝ)|=(5181658433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s3_1 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070361131/2000000000 : ℝ)*x 0 + (-226668509/1250000000 : ℝ)*x 1 + (5181658427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070361131/2000000000 : ℝ)^4811 ≤ (45194664687569/100000000000000 : ℝ)^3787 := by
    have hnat : (1070361131 : ℕ)^4811*100000000000000^3787 ≤ 45194664687569^3787*2000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070361131 2000000000 45194664687569 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226668509/1250000000 : ℝ)^4811 ≤ (11428136642091/100000000000000 : ℝ)^3787 := by
    have hnat : (226668509 : ℕ)^4811*100000000000000^3787 ≤ 11428136642091^3787*1250000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226668509 1250000000 11428136642091 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181658427/10000000000 : ℝ)^4811 ≤ (43377198653023/100000000000000 : ℝ)^3787 := by
    have hnat : (5181658427 : ℕ)^4811*100000000000000^3787 ≤ 43377198653023^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181658427 10000000000 43377198653023 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070361131/2000000000 : ℝ), (-226668509/1250000000 : ℝ), (5181658427/10000000000 : ℝ)] ![(45194664687569/100000000000000 : ℝ), (11428136642091/100000000000000 : ℝ), (43377198653023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070361131/2000000000 : ℝ)|^4811 ≤ (45194664687569/100000000000000 : ℝ)^3787
        have hw : |(1070361131/2000000000 : ℝ)|=(1070361131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-226668509/1250000000 : ℝ)|^4811 ≤ (11428136642091/100000000000000 : ℝ)^3787
        have hw : |(-226668509/1250000000 : ℝ)|=(226668509/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181658427/10000000000 : ℝ)|^4811 ≤ (43377198653023/100000000000000 : ℝ)^3787
        have hw : |(5181658427/10000000000 : ℝ)|=(5181658427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s3_2 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675902831/5000000000 : ℝ)*x 0 + (1295414603/2500000000 : ℝ)*x 1 + (-1813348083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675902831/5000000000 : ℝ)^4811 ≤ (22597332381333/50000000000000 : ℝ)^3787 := by
    have hnat : (2675902831 : ℕ)^4811*50000000000000^3787 ≤ 22597332381333^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675902831 5000000000 22597332381333 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295414603/2500000000 : ℝ)^4811 ≤ (86754396987/200000000000 : ℝ)^3787 := by
    have hnat : (1295414603 : ℕ)^4811*200000000000^3787 ≤ 86754396987^3787*2500000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295414603 2500000000 86754396987 200000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1813348083/10000000000 : ℝ)^4811 ≤ (11428136730161/100000000000000 : ℝ)^3787 := by
    have hnat : (1813348083 : ℕ)^4811*100000000000000^3787 ≤ 11428136730161^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1813348083 10000000000 11428136730161 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675902831/5000000000 : ℝ), (1295414603/2500000000 : ℝ), (-1813348083/10000000000 : ℝ)] ![(22597332381333/50000000000000 : ℝ), (86754396987/200000000000 : ℝ), (11428136730161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675902831/5000000000 : ℝ)|^4811 ≤ (22597332381333/50000000000000 : ℝ)^3787
        have hw : |(2675902831/5000000000 : ℝ)|=(2675902831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295414603/2500000000 : ℝ)|^4811 ≤ (86754396987/200000000000 : ℝ)^3787
        have hw : |(1295414603/2500000000 : ℝ)|=(1295414603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1813348083/10000000000 : ℝ)|^4811 ≤ (11428136730161/100000000000000 : ℝ)^3787
        have hw : |(-1813348083/10000000000 : ℝ)|=(1813348083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s3_3 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2100951641/5000000000 : ℝ)*x 0 + (3869761573/10000000000 : ℝ)*x 1 + (182205799/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100951641/5000000000 : ℝ)^4811 ≤ (8309336563167/25000000000000 : ℝ)^3787 := by
    have hnat : (2100951641 : ℕ)^4811*25000000000000^3787 ≤ 8309336563167^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100951641 5000000000 8309336563167 25000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3869761573/10000000000 : ℝ)^4811 ≤ (3742006634089/12500000000000 : ℝ)^3787 := by
    have hnat : (3869761573 : ℕ)^4811*12500000000000^3787 ≤ 3742006634089^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3869761573 10000000000 3742006634089 12500000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (182205799/400000000 : ℝ)^4811 ≤ (36826600655513/100000000000000 : ℝ)^3787 := by
    have hnat : (182205799 : ℕ)^4811*100000000000000^3787 ≤ 36826600655513^3787*400000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182205799 400000000 36826600655513 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2100951641/5000000000 : ℝ), (3869761573/10000000000 : ℝ), (182205799/400000000 : ℝ)] ![(8309336563167/25000000000000 : ℝ), (3742006634089/12500000000000 : ℝ), (36826600655513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2100951641/5000000000 : ℝ)|^4811 ≤ (8309336563167/25000000000000 : ℝ)^3787
        have hw : |(2100951641/5000000000 : ℝ)|=(2100951641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3869761573/10000000000 : ℝ)|^4811 ≤ (3742006634089/12500000000000 : ℝ)^3787
        have hw : |(3869761573/10000000000 : ℝ)|=(3869761573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(182205799/400000000 : ℝ)|^4811 ≤ (36826600655513/100000000000000 : ℝ)^3787
        have hw : |(182205799/400000000 : ℝ)|=(182205799/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s3_4 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-41802241/250000000 : ℝ)*x 0 + (5183712877/10000000000 : ℝ)*x 1 + (5453795057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41802241/250000000 : ℝ)^4811 ≤ (2577329431829/25000000000000 : ℝ)^3787 := by
    have hnat : (41802241 : ℕ)^4811*25000000000000^3787 ≤ 2577329431829^3787*250000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41802241 250000000 2577329431829 25000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183712877/10000000000 : ℝ)^4811 ≤ (4339904866229/10000000000000 : ℝ)^3787 := by
    have hnat : (5183712877 : ℕ)^4811*10000000000000^3787 ≤ 4339904866229^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183712877 10000000000 4339904866229 10000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5453795057/10000000000 : ℝ)^4811 ≤ (23145816799681/50000000000000 : ℝ)^3787 := by
    have hnat : (5453795057 : ℕ)^4811*50000000000000^3787 ≤ 23145816799681^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453795057 10000000000 23145816799681 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-41802241/250000000 : ℝ), (5183712877/10000000000 : ℝ), (5453795057/10000000000 : ℝ)] ![(2577329431829/25000000000000 : ℝ), (4339904866229/10000000000000 : ℝ), (23145816799681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-41802241/250000000 : ℝ)|^4811 ≤ (2577329431829/25000000000000 : ℝ)^3787
        have hw : |(-41802241/250000000 : ℝ)|=(41802241/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183712877/10000000000 : ℝ)|^4811 ≤ (4339904866229/10000000000000 : ℝ)^3787
        have hw : |(5183712877/10000000000 : ℝ)|=(5183712877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5453795057/10000000000 : ℝ)|^4811 ≤ (23145816799681/50000000000000 : ℝ)^3787
        have hw : |(5453795057/10000000000 : ℝ)|=(5453795057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s3_5 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639410389/5000000000 : ℝ)*x 0 + (-1541211807/10000000000 : ℝ)*x 1 + (2726897257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639410389/5000000000 : ℝ)^4811 ≤ (4441311676839/10000000000000 : ℝ)^3787 := by
    have hnat : (2639410389 : ℕ)^4811*10000000000000^3787 ≤ 4441311676839^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639410389 5000000000 4441311676839 10000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1541211807/10000000000 : ℝ)^4811 ≤ (9295255464669/100000000000000 : ℝ)^3787 := by
    have hnat : (1541211807 : ℕ)^4811*100000000000000^3787 ≤ 9295255464669^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1541211807 10000000000 9295255464669 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2726897257/5000000000 : ℝ)^4811 ≤ (46291627744137/100000000000000 : ℝ)^3787 := by
    have hnat : (2726897257 : ℕ)^4811*100000000000000^3787 ≤ 46291627744137^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726897257 5000000000 46291627744137 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639410389/5000000000 : ℝ), (-1541211807/10000000000 : ℝ), (2726897257/5000000000 : ℝ)] ![(4441311676839/10000000000000 : ℝ), (9295255464669/100000000000000 : ℝ), (46291627744137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639410389/5000000000 : ℝ)|^4811 ≤ (4441311676839/10000000000000 : ℝ)^3787
        have hw : |(2639410389/5000000000 : ℝ)|=(2639410389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1541211807/10000000000 : ℝ)|^4811 ≤ (9295255464669/100000000000000 : ℝ)^3787
        have hw : |(-1541211807/10000000000 : ℝ)|=(1541211807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2726897257/5000000000 : ℝ)|^4811 ≤ (46291627744137/100000000000000 : ℝ)^3787
        have hw : |(2726897257/5000000000 : ℝ)|=(2726897257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s3_6 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639410223/5000000000 : ℝ)*x 0 + (1363448723/2500000000 : ℝ)*x 1 + (-77060587/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639410223/5000000000 : ℝ)^4811 ≤ (44413113219827/100000000000000 : ℝ)^3787 := by
    have hnat : (2639410223 : ℕ)^4811*100000000000000^3787 ≤ 44413113219827^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639410223 5000000000 44413113219827 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363448723/2500000000 : ℝ)^4811 ≤ (925832636403/2000000000000 : ℝ)^3787 := by
    have hnat : (1363448723 : ℕ)^4811*2000000000000^3787 ≤ 925832636403^3787*2500000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363448723 2500000000 925832636403 2000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (77060587/500000000 : ℝ)^4811 ≤ (9295254951319/100000000000000 : ℝ)^3787 := by
    have hnat : (77060587 : ℕ)^4811*100000000000000^3787 ≤ 9295254951319^3787*500000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77060587 500000000 9295254951319 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639410223/5000000000 : ℝ), (1363448723/2500000000 : ℝ), (-77060587/500000000 : ℝ)] ![(44413113219827/100000000000000 : ℝ), (925832636403/2000000000000 : ℝ), (9295254951319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639410223/5000000000 : ℝ)|^4811 ≤ (44413113219827/100000000000000 : ℝ)^3787
        have hw : |(2639410223/5000000000 : ℝ)|=(2639410223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1363448723/2500000000 : ℝ)|^4811 ≤ (925832636403/2000000000000 : ℝ)^3787
        have hw : |(1363448723/2500000000 : ℝ)|=(1363448723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-77060587/500000000 : ℝ)|^4811 ≤ (9295254951319/100000000000000 : ℝ)^3787
        have hw : |(-77060587/500000000 : ℝ)|=(77060587/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s3_7 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050518723/2500000000 : ℝ)*x 0 + (2275004499/5000000000 : ℝ)*x 1 + (3874951841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050518723/2500000000 : ℝ)^4811 ≤ (16619535380567/50000000000000 : ℝ)^3787 := by
    have hnat : (1050518723 : ℕ)^4811*50000000000000^3787 ≤ 16619535380567^3787*2500000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050518723 2500000000 16619535380567 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2275004499/5000000000 : ℝ)^4811 ≤ (36773858688333/100000000000000 : ℝ)^3787 := by
    have hnat : (2275004499 : ℕ)^4811*100000000000000^3787 ≤ 36773858688333^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2275004499 5000000000 36773858688333 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3874951841/10000000000 : ℝ)^4811 ≤ (5997414107823/20000000000000 : ℝ)^3787 := by
    have hnat : (3874951841 : ℕ)^4811*20000000000000^3787 ≤ 5997414107823^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3874951841 10000000000 5997414107823 20000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050518723/2500000000 : ℝ), (2275004499/5000000000 : ℝ), (3874951841/10000000000 : ℝ)] ![(16619535380567/50000000000000 : ℝ), (36773858688333/100000000000000 : ℝ), (5997414107823/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050518723/2500000000 : ℝ)|^4811 ≤ (16619535380567/50000000000000 : ℝ)^3787
        have hw : |(1050518723/2500000000 : ℝ)|=(1050518723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2275004499/5000000000 : ℝ)|^4811 ≤ (36773858688333/100000000000000 : ℝ)^3787
        have hw : |(2275004499/5000000000 : ℝ)|=(2275004499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3874951841/10000000000 : ℝ)|^4811 ≤ (5997414107823/20000000000000 : ℝ)^3787
        have hw : |(3874951841/10000000000 : ℝ)|=(3874951841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1623_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174972867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16441/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1301/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10509/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2041/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16441/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1301/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16441/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1301/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16441/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1301/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16441/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1301/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16441/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1301/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16441/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1301/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1301/12500 : ℝ) ^ (4807/1024 : ℝ) ≤ (12194441936543/500000000000000000 : ℝ) := by
    have hpowers : (1301/12500 : ℝ)^4807 ≤ (12194441936543/500000000000000000 : ℝ)^1024 := by
      have hnat : (1301 : ℕ)^4807*500000000000000000^1024 ≤ 12194441936543^1024*12500^4807 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1301 12500 12194441936543 500000000000000000 4807 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1301/12500 : ℝ)) (X := (12194441936543/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16441/100000 : ℝ) ^ (4807/1024 : ℝ) ≤ (5214872780840153/25000000000000000000 : ℝ) := by
    have hpowers : (16441/100000 : ℝ)^4807 ≤ (5214872780840153/25000000000000000000 : ℝ)^1024 := by
      have hnat : (16441 : ℕ)^4807*25000000000000000000^1024 ≤ 5214872780840153^1024*100000^4807 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16441 100000 5214872780840153 25000000000000000000 4807 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16441/100000 : ℝ)) (X := (5214872780840153/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (250012194441936543/250000000000000000 : ℝ) ≤ (5000051952855747/5000000000000000 : ℝ) ^ (4807/1024 : ℝ) := by
    have hpowers : (250012194441936543/250000000000000000 : ℝ)^1024 ≤ (5000051952855747/5000000000000000 : ℝ)^4807 := by
      have hnat : (250012194441936543 : ℕ)^1024*5000000000000000^4807 ≤ 5000051952855747^4807*250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250012194441936543 250000000000000000 5000051952855747 5000000000000000 1024 4807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000051952855747/5000000000000000 : ℝ)) (X := (250012194441936543/250000000000000000 : ℝ)) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25005824594877667303/25000000000000000000 : ℝ) ≤ (2000099252563957/2000000000000000 : ℝ) ^ (4807/1024 : ℝ) := by
    have hpowers : (25005824594877667303/25000000000000000000 : ℝ)^1024 ≤ (2000099252563957/2000000000000000 : ℝ)^4807 := by
      have hnat : (25005824594877667303 : ℕ)^1024*2000000000000000^4807 ≤ 2000099252563957^4807*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005824594877667303 25000000000000000000 2000099252563957 2000000000000000 1024 4807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000099252563957/2000000000000000 : ℝ)) (X := (25005824594877667303/25000000000000000000 : ℝ)) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505214872780840153/12500000000000000000 : ℝ) ≤ (2500222154982019/2500000000000000 : ℝ) ^ (4807/1024 : ℝ) := by
    have hpowers : (12505214872780840153/12500000000000000000 : ℝ)^1024 ≤ (2500222154982019/2500000000000000 : ℝ)^4807 := by
      have hnat : (12505214872780840153 : ℕ)^1024*2500000000000000^4807 ≤ 2500222154982019^4807*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505214872780840153 12500000000000000000 2500222154982019 2500000000000000 1024 4807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500222154982019/2500000000000000 : ℝ)) (X := (12505214872780840153/12500000000000000000 : ℝ)) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12194441936543/500000000000000000 : ℝ) ≤ ((30161229778795628923/30165000000000000000 : ℝ)+2*(392357108291/603300000000000 : ℝ)*(1301/12500 : ℝ))^(4807/1024 : ℝ) := by
    rw [show (30161229778795628923/30165000000000000000 : ℝ)+2*(392357108291/603300000000000 : ℝ)*(1301/12500 : ℝ)=(5000051952855747/5000000000000000 : ℝ) by norm_num, show 1+2*(12194441936543/500000000000000000 : ℝ)=(250012194441936543/250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5214872780840153/25000000000000000000 : ℝ)+(12194441936543/500000000000000000 : ℝ) ≤ ((30161229778795628923/30165000000000000000 : ℝ)+(392357108291/603300000000000 : ℝ)*((16441/100000 : ℝ)+(1301/12500 : ℝ)))^(4807/1024 : ℝ) := by
    rw [show (30161229778795628923/30165000000000000000 : ℝ)+(392357108291/603300000000000 : ℝ)*((16441/100000 : ℝ)+(1301/12500 : ℝ))=(2000099252563957/2000000000000000 : ℝ) by norm_num, show 1+(5214872780840153/25000000000000000000 : ℝ)+(12194441936543/500000000000000000 : ℝ)=(25005824594877667303/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5214872780840153/25000000000000000000 : ℝ) ≤ ((30161229778795628923/30165000000000000000 : ℝ)+2*(392357108291/603300000000000 : ℝ)*(16441/100000 : ℝ))^(4807/1024 : ℝ) := by
    rw [show (30161229778795628923/30165000000000000000 : ℝ)+2*(392357108291/603300000000000 : ℝ)*(16441/100000 : ℝ)=(2500222154982019/2500000000000000 : ℝ) by norm_num, show 1+2*(5214872780840153/25000000000000000000 : ℝ)=(12505214872780840153/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (30161229778795628923/30165000000000000000 : ℝ)*(X 1 0+X 2 0)+(392357108291/603300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4807/1024 : ℝ)) (lo := (1301/12500 : ℝ)) (hi := (16441/100000 : ℝ)) (c := (30161229778795628923/30165000000000000000 : ℝ)) (alpha := (392357108291/603300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (30161229778795628923/30165000000000000000 : ℝ)*(X 0 1+X 2 1)+(392357108291/603300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4807/1024 : ℝ)) (lo := (1301/12500 : ℝ)) (hi := (16441/100000 : ℝ)) (c := (30161229778795628923/30165000000000000000 : ℝ)) (alpha := (392357108291/603300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (30161229778795628923/30165000000000000000 : ℝ)*(X 0 2+X 1 2)+(392357108291/603300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4807/1024 : ℝ)) (lo := (1301/12500 : ℝ)) (hi := (16441/100000 : ℝ)) (c := (30161229778795628923/30165000000000000000 : ℝ)) (alpha := (392357108291/603300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-836010383/5000000000 : ℝ)*X 0 0+(1363967823/2500000000 : ℝ)*X 0 1+(5181658433/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070361131/2000000000 : ℝ)*X 1 0+(-226668509/1250000000 : ℝ)*X 1 1+(5181658427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675902831/5000000000 : ℝ)*X 2 0+(1295414603/2500000000 : ℝ)*X 2 1+(-1813348083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2100951641/5000000000 : ℝ)*X 0 0+(3869761573/10000000000 : ℝ)*X 0 1+(182205799/400000000 : ℝ)*X 0 2+(2100951641/5000000000 : ℝ)*X 1 0+(3869761573/10000000000 : ℝ)*X 1 1+(182205799/400000000 : ℝ)*X 1 2+(2100951641/5000000000 : ℝ)*X 2 0+(3869761573/10000000000 : ℝ)*X 2 1+(182205799/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-41802241/250000000 : ℝ)*X 0 0+(5183712877/10000000000 : ℝ)*X 0 1+(5453795057/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2639410389/5000000000 : ℝ)*X 1 0+(-1541211807/10000000000 : ℝ)*X 1 1+(2726897257/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2639410223/5000000000 : ℝ)*X 2 0+(1363448723/2500000000 : ℝ)*X 2 1+(-77060587/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1050518723/2500000000 : ℝ)*X 0 0+(2275004499/5000000000 : ℝ)*X 0 1+(3874951841/10000000000 : ℝ)*X 0 2+(1050518723/2500000000 : ℝ)*X 1 0+(2275004499/5000000000 : ℝ)*X 1 1+(3874951841/10000000000 : ℝ)*X 1 2+(1050518723/2500000000 : ℝ)*X 2 0+(2275004499/5000000000 : ℝ)*X 2 1+(3874951841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (553124722563622193290845513/50275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (908170653/50000000000000 : ℝ)*(base19) + (1725683203/100000000000000 : ℝ)*(base23) + (25535623/50000000000000 : ℝ)*(lower2) + (33854889/12500000000000 : ℝ)*(upper3) + (193901927/100000000000000 : ℝ)*(upper5) + (255295145754777/10000000000000 : ℝ)*(major0) + (255295145754777/10000000000000 : ℝ)*(major1) + (255295145754777/10000000000000 : ℝ)*(major2) + (3646824797045929/100000000000000 : ℝ)*(sp0) + (1823422553693463/50000000000000 : ℝ)*(sp1) + (3646845198045029/100000000000000 : ℝ)*(sp2) + (182380751944413/12500000000000 : ℝ)*(sp3) + (22126682303/100000000000000 : ℝ)*(sp4) + (2402269803/25000000000000 : ℝ)*(sp7) + (364763906158629/25000000000000 : ℝ)*(f.failure) + (455855865466029/12500000000000 : ℝ)*(f.sum) + (514491888927/100550000000000000000000000 : ℝ)*base66 + (807291511171194943/100550000000000000000000000000000 : ℝ)*base68 + (965366513370344943/100550000000000000000000000000000 : ℝ)*base70 + (646486983498444943/100550000000000000000000000000000 : ℝ)*base72 + (918928879159/1005500000000000000000000000 : ℝ)*base74 + (1131835069701044943/100550000000000000000000000000000 : ℝ)*base76 + (1118397058515844943/100550000000000000000000000000000 : ℝ)*base78 + (876364127443144943/100550000000000000000000000000000 : ℝ)*base80 + (4792863769397/2011000000000000000000000000 : ℝ)*base82 + (22919343/2500000000000000000000 : ℝ)*base89 + (22919343/2500000000000000000000 : ℝ)*base91 + (22919343/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (96242812327624697700029/10055000000000000000000000000 : ℝ) := by norm_num
    linear_combination (354704909/20000000000000 : ℝ)*(base19) + (393327297/25000000000000 : ℝ)*(base23) + (18354507/50000000000000 : ℝ)*(upper2) + (115382771/100000000000000 : ℝ)*(upper3) + (8332021/2500000000000 : ℝ)*(upper5) + (1295983609597337/50000000000000 : ℝ)*(major0) + (1295983609597337/50000000000000 : ℝ)*(major1) + (1295983609597337/50000000000000 : ℝ)*(major2) + (9000052611/50000000000000 : ℝ)*(sp1) + (7665939393/50000000000000 : ℝ)*(sp2) + (1851290158261101/50000000000000 : ℝ)*(sp4) + (740512108578487/20000000000000 : ℝ)*(sp5) + (925640852833557/25000000000000 : ℝ)*(sp6) + (740676901406283/50000000000000 : ℝ)*(sp7) + (740676901406283/50000000000000 : ℝ)*(f.failure) + (1851290158261101/50000000000000 : ℝ)*(f.sum) + (33168931370273/15082500000000000000000000000 : ℝ)*base66 + (174160142572828051/1508250000000000000000000000000000 : ℝ)*base67 + (2240888214785671949/1508250000000000000000000000000000 : ℝ)*base70 + (3912554375369671949/1508250000000000000000000000000000 : ℝ)*base72 + (103577019893699/30165000000000000000000000000 : ℝ)*base73 + (7623441027286828051/1508250000000000000000000000000000 : ℝ)*base75 + (8628651799604671949/1508250000000000000000000000000000 : ℝ)*base78 + (5530534979127328051/1508250000000000000000000000000000 : ℝ)*base79 + (20864996727893/15082500000000000000000000000 : ℝ)*base82 + (31676639/5000000000000000000000 : ℝ)*base90 + (31676639/5000000000000000000000 : ℝ)*base92 + (31676639/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1623_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174972867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16441/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1301/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10509/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2041/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1623_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1623_s4_0 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-836053329/5000000000 : ℝ)*x 0 + (5455442081/10000000000 : ℝ)*x 1 + (5182030403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (836053329/5000000000 : ℝ)^4811 ≤ (10309451024059/100000000000000 : ℝ)^3787 := by
    have hnat : (836053329 : ℕ)^4811*100000000000000^3787 ≤ 10309451024059^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836053329 5000000000 10309451024059 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5455442081/10000000000 : ℝ)^4811 ≤ (46309394353521/100000000000000 : ℝ)^3787 := by
    have hnat : (5455442081 : ℕ)^4811*100000000000000^3787 ≤ 46309394353521^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455442081 10000000000 46309394353521 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182030403/10000000000 : ℝ)^4811 ≤ (10845288653291/25000000000000 : ℝ)^3787 := by
    have hnat : (5182030403 : ℕ)^4811*25000000000000^3787 ≤ 10845288653291^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182030403 10000000000 10845288653291 25000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-836053329/5000000000 : ℝ), (5455442081/10000000000 : ℝ), (5182030403/10000000000 : ℝ)] ![(10309451024059/100000000000000 : ℝ), (46309394353521/100000000000000 : ℝ), (10845288653291/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-836053329/5000000000 : ℝ)|^4811 ≤ (10309451024059/100000000000000 : ℝ)^3787
        have hw : |(-836053329/5000000000 : ℝ)|=(836053329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5455442081/10000000000 : ℝ)|^4811 ≤ (46309394353521/100000000000000 : ℝ)^3787
        have hw : |(5455442081/10000000000 : ℝ)|=(5455442081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182030403/10000000000 : ℝ)|^4811 ≤ (10845288653291/25000000000000 : ℝ)^3787
        have hw : |(5182030403/10000000000 : ℝ)|=(5182030403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s4_1 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351690227/10000000000 : ℝ)*x 0 + (-906504467/5000000000 : ℝ)*x 1 + (2591015087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351690227/10000000000 : ℝ)^4811 ≤ (45193426356439/100000000000000 : ℝ)^3787 := by
    have hnat : (5351690227 : ℕ)^4811*100000000000000^3787 ≤ 45193426356439^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351690227 10000000000 45193426356439 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (906504467/5000000000 : ℝ)^4811 ≤ (11425421454913/100000000000000 : ℝ)^3787 := by
    have hnat : (906504467 : ℕ)^4811*100000000000000^3787 ≤ 11425421454913^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906504467 5000000000 11425421454913 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591015087/5000000000 : ℝ)^4811 ≤ (677830502777/1562500000000 : ℝ)^3787 := by
    have hnat : (2591015087 : ℕ)^4811*1562500000000^3787 ≤ 677830502777^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591015087 5000000000 677830502777 1562500000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351690227/10000000000 : ℝ), (-906504467/5000000000 : ℝ), (2591015087/5000000000 : ℝ)] ![(45193426356439/100000000000000 : ℝ), (11425421454913/100000000000000 : ℝ), (677830502777/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351690227/10000000000 : ℝ)|^4811 ≤ (45193426356439/100000000000000 : ℝ)^3787
        have hw : |(5351690227/10000000000 : ℝ)|=(5351690227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-906504467/5000000000 : ℝ)|^4811 ≤ (11425421454913/100000000000000 : ℝ)^3787
        have hw : |(-906504467/5000000000 : ℝ)|=(906504467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591015087/5000000000 : ℝ)|^4811 ≤ (677830502777/1562500000000 : ℝ)^3787
        have hw : |(2591015087/5000000000 : ℝ)|=(2591015087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s4_2 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351690127/10000000000 : ℝ)*x 0 + (161938447/312500000 : ℝ)*x 1 + (-3541033/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351690127/10000000000 : ℝ)^4811 ≤ (361547402269/800000000000 : ℝ)^3787 := by
    have hnat : (5351690127 : ℕ)^4811*800000000000^3787 ≤ 361547402269^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351690127 10000000000 361547402269 800000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161938447/312500000 : ℝ)^4811 ≤ (4338115356029/10000000000000 : ℝ)^3787 := by
    have hnat : (161938447 : ℕ)^4811*10000000000000^3787 ≤ 4338115356029^3787*312500000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161938447 312500000 4338115356029 10000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3541033/19531250 : ℝ)^4811 ≤ (11425421150687/100000000000000 : ℝ)^3787 := by
    have hnat : (3541033 : ℕ)^4811*100000000000000^3787 ≤ 11425421150687^3787*19531250^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3541033 19531250 11425421150687 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351690127/10000000000 : ℝ), (161938447/312500000 : ℝ), (-3541033/19531250 : ℝ)] ![(361547402269/800000000000 : ℝ), (4338115356029/10000000000000 : ℝ), (11425421150687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351690127/10000000000 : ℝ)|^4811 ≤ (361547402269/800000000000 : ℝ)^3787
        have hw : |(5351690127/10000000000 : ℝ)|=(5351690127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(161938447/312500000 : ℝ)|^4811 ≤ (4338115356029/10000000000000 : ℝ)^3787
        have hw : |(161938447/312500000 : ℝ)|=(161938447/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3541033/19531250 : ℝ)|^4811 ≤ (11425421150687/100000000000000 : ℝ)^3787
        have hw : |(-3541033/19531250 : ℝ)|=(3541033/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s4_3 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (840391801/2000000000 : ℝ)*x 0 + (967689183/2500000000 : ℝ)*x 1 + (56926727/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (840391801/2000000000 : ℝ)^4811 ≤ (33237906210869/100000000000000 : ℝ)^3787 := by
    have hnat : (840391801 : ℕ)^4811*100000000000000^3787 ≤ 33237906210869^3787*2000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840391801 2000000000 33237906210869 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (967689183/2500000000 : ℝ)^4811 ≤ (3743229187863/12500000000000 : ℝ)^3787 := by
    have hnat : (967689183 : ℕ)^4811*12500000000000^3787 ≤ 3743229187863^3787*2500000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967689183 2500000000 3743229187863 12500000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56926727/125000000 : ℝ)^4811 ≤ (7363252056627/20000000000000 : ℝ)^3787 := by
    have hnat : (56926727 : ℕ)^4811*20000000000000^3787 ≤ 7363252056627^3787*125000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56926727 125000000 7363252056627 20000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(840391801/2000000000 : ℝ), (967689183/2500000000 : ℝ), (56926727/125000000 : ℝ)] ![(33237906210869/100000000000000 : ℝ), (3743229187863/12500000000000 : ℝ), (7363252056627/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(840391801/2000000000 : ℝ)|^4811 ≤ (33237906210869/100000000000000 : ℝ)^3787
        have hw : |(840391801/2000000000 : ℝ)|=(840391801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(967689183/2500000000 : ℝ)|^4811 ≤ (3743229187863/12500000000000 : ℝ)^3787
        have hw : |(967689183/2500000000 : ℝ)|=(967689183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(56926727/125000000 : ℝ)|^4811 ≤ (7363252056627/20000000000000 : ℝ)^3787
        have hw : |(56926727/125000000 : ℝ)|=(56926727/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s4_4 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-836087419/5000000000 : ℝ)*x 0 + (207362931/400000000 : ℝ)*x 1 + (68167221/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (836087419/5000000000 : ℝ)^4811 ≤ (10309985060639/100000000000000 : ℝ)^3787 := by
    have hnat : (836087419 : ℕ)^4811*100000000000000^3787 ≤ 10309985060639^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836087419 5000000000 10309985060639 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207362931/400000000 : ℝ)^4811 ≤ (21701440950113/50000000000000 : ℝ)^3787 := by
    have hnat : (207362931 : ℕ)^4811*50000000000000^3787 ≤ 21701440950113^3787*400000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207362931 400000000 21701440950113 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68167221/125000000 : ℝ)^4811 ≤ (1157178325671/2500000000000 : ℝ)^3787 := by
    have hnat : (68167221 : ℕ)^4811*2500000000000^3787 ≤ 1157178325671^3787*125000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68167221 125000000 1157178325671 2500000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-836087419/5000000000 : ℝ), (207362931/400000000 : ℝ), (68167221/125000000 : ℝ)] ![(10309985060639/100000000000000 : ℝ), (21701440950113/50000000000000 : ℝ), (1157178325671/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-836087419/5000000000 : ℝ)|^4811 ≤ (10309985060639/100000000000000 : ℝ)^3787
        have hw : |(-836087419/5000000000 : ℝ)|=(836087419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207362931/400000000 : ℝ)|^4811 ≤ (21701440950113/50000000000000 : ℝ)^3787
        have hw : |(207362931/400000000 : ℝ)|=(207362931/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68167221/125000000 : ℝ)|^4811 ≤ (1157178325671/2500000000000 : ℝ)^3787
        have hw : |(68167221/125000000 : ℝ)|=(68167221/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s4_5 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639459487/5000000000 : ℝ)*x 0 + (-154166121/1000000000 : ℝ)*x 1 + (68167223/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639459487/5000000000 : ℝ)^4811 ≤ (22207083166617/50000000000000 : ℝ)^3787 := by
    have hnat : (2639459487 : ℕ)^4811*50000000000000^3787 ≤ 22207083166617^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639459487 5000000000 22207083166617 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (154166121/1000000000 : ℝ)^4811 ≤ (4649349450833/50000000000000 : ℝ)^3787 := by
    have hnat : (154166121 : ℕ)^4811*50000000000000^3787 ≤ 4649349450833^3787*1000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154166121 1000000000 4649349450833 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68167223/125000000 : ℝ)^4811 ≤ (46287134752101/100000000000000 : ℝ)^3787 := by
    have hnat : (68167223 : ℕ)^4811*100000000000000^3787 ≤ 46287134752101^3787*125000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68167223 125000000 46287134752101 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639459487/5000000000 : ℝ), (-154166121/1000000000 : ℝ), (68167223/125000000 : ℝ)] ![(22207083166617/50000000000000 : ℝ), (4649349450833/50000000000000 : ℝ), (46287134752101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639459487/5000000000 : ℝ)|^4811 ≤ (22207083166617/50000000000000 : ℝ)^3787
        have hw : |(2639459487/5000000000 : ℝ)|=(2639459487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-154166121/1000000000 : ℝ)|^4811 ≤ (4649349450833/50000000000000 : ℝ)^3787
        have hw : |(-154166121/1000000000 : ℝ)|=(154166121/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68167223/125000000 : ℝ)|^4811 ≤ (46287134752101/100000000000000 : ℝ)^3787
        have hw : |(68167223/125000000 : ℝ)|=(68167223/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s4_6 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (263945949/500000000 : ℝ)*x 0 + (34083611/62500000 : ℝ)*x 1 + (-770830657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263945949/500000000 : ℝ)^4811 ≤ (8882833279473/20000000000000 : ℝ)^3787 := by
    have hnat : (263945949 : ℕ)^4811*20000000000000^3787 ≤ 8882833279473^3787*500000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263945949 500000000 8882833279473 20000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34083611/62500000 : ℝ)^4811 ≤ (4628713388947/10000000000000 : ℝ)^3787 := by
    have hnat : (34083611 : ℕ)^4811*10000000000000^3787 ≤ 4628713388947^3787*62500000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34083611 62500000 4628713388947 10000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (770830657/5000000000 : ℝ)^4811 ≤ (9298699698571/100000000000000 : ℝ)^3787 := by
    have hnat : (770830657 : ℕ)^4811*100000000000000^3787 ≤ 9298699698571^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      770830657 5000000000 9298699698571 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263945949/500000000 : ℝ), (34083611/62500000 : ℝ), (-770830657/5000000000 : ℝ)] ![(8882833279473/20000000000000 : ℝ), (4628713388947/10000000000000 : ℝ), (9298699698571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263945949/500000000 : ℝ)|^4811 ≤ (8882833279473/20000000000000 : ℝ)^3787
        have hw : |(263945949/500000000 : ℝ)|=(263945949/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(34083611/62500000 : ℝ)|^4811 ≤ (4628713388947/10000000000000 : ℝ)^3787
        have hw : |(34083611/62500000 : ℝ)|=(34083611/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-770830657/5000000000 : ℝ)|^4811 ≤ (9298699698571/100000000000000 : ℝ)^3787
        have hw : |(-770830657/5000000000 : ℝ)|=(770830657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s4_7 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2101064499/5000000000 : ℝ)*x 0 + (4549031983/10000000000 : ℝ)*x 1 + (77518337/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2101064499/5000000000 : ℝ)^4811 ≤ (33239614476143/100000000000000 : ℝ)^3787 := by
    have hnat : (2101064499 : ℕ)^4811*100000000000000^3787 ≤ 33239614476143^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101064499 5000000000 33239614476143 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4549031983/10000000000 : ℝ)^4811 ≤ (18381913712611/50000000000000 : ℝ)^3787 := by
    have hnat : (4549031983 : ℕ)^4811*50000000000000^3787 ≤ 18381913712611^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4549031983 10000000000 18381913712611 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (77518337/200000000 : ℝ)^4811 ≤ (29996558082369/100000000000000 : ℝ)^3787 := by
    have hnat : (77518337 : ℕ)^4811*100000000000000^3787 ≤ 29996558082369^3787*200000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77518337 200000000 29996558082369 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2101064499/5000000000 : ℝ), (4549031983/10000000000 : ℝ), (77518337/200000000 : ℝ)] ![(33239614476143/100000000000000 : ℝ), (18381913712611/50000000000000 : ℝ), (29996558082369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2101064499/5000000000 : ℝ)|^4811 ≤ (33239614476143/100000000000000 : ℝ)^3787
        have hw : |(2101064499/5000000000 : ℝ)|=(2101064499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4549031983/10000000000 : ℝ)|^4811 ≤ (18381913712611/50000000000000 : ℝ)^3787
        have hw : |(4549031983/10000000000 : ℝ)|=(4549031983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(77518337/200000000 : ℝ)|^4811 ≤ (29996558082369/100000000000000 : ℝ)^3787
        have hw : |(77518337/200000000 : ℝ)|=(77518337/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1623_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174972867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2041/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10509/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10517/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16319/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2041/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10509/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2041/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10509/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2041/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10509/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2041/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10509/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2041/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10509/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2041/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10509/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10509/100000 : ℝ) ^ (4807/1024 : ℝ) ≤ (1275999441627287/50000000000000000000 : ℝ) := by
    have hpowers : (10509/100000 : ℝ)^4807 ≤ (1275999441627287/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10509 : ℕ)^4807*50000000000000000000^1024 ≤ 1275999441627287^1024*100000^4807 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10509 100000 1275999441627287 50000000000000000000 4807 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10509/100000 : ℝ)) (X := (1275999441627287/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2041/12500 : ℝ) ^ (4807/1024 : ℝ) ≤ (20194962811016209/100000000000000000000 : ℝ) := by
    have hpowers : (2041/12500 : ℝ)^4807 ≤ (20194962811016209/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2041 : ℕ)^4807*100000000000000000000^1024 ≤ 20194962811016209^1024*12500^4807 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2041 12500 20194962811016209 100000000000000000000 4807 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2041/12500 : ℝ)) (X := (20194962811016209/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001275999441627287/25000000000000000000 : ℝ) ≤ (5000054362271157/5000000000000000 : ℝ) ^ (4807/1024 : ℝ) := by
    have hpowers : (25001275999441627287/25000000000000000000 : ℝ)^1024 ≤ (5000054362271157/5000000000000000 : ℝ)^4807 := by
      have hnat : (25001275999441627287 : ℕ)^1024*5000000000000000^4807 ≤ 5000054362271157^4807*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001275999441627287 25000000000000000000 5000054362271157 5000000000000000 1024 4807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000054362271157/5000000000000000 : ℝ)) (X := (25001275999441627287/25000000000000000000 : ℝ)) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100022746961694270783/100000000000000000000 : ℝ) ≤ (5000242259248881/5000000000000000 : ℝ) ^ (4807/1024 : ℝ) := by
    have hpowers : (100022746961694270783/100000000000000000000 : ℝ)^1024 ≤ (5000242259248881/5000000000000000 : ℝ)^4807 := by
      have hnat : (100022746961694270783 : ℕ)^1024*5000000000000000^4807 ≤ 5000242259248881^4807*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100022746961694270783 100000000000000000000 5000242259248881 5000000000000000 1024 4807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000242259248881/5000000000000000 : ℝ)) (X := (100022746961694270783/100000000000000000000 : ℝ)) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50020194962811016209/50000000000000000000 : ℝ) ≤ (1000086031245321/1000000000000000 : ℝ) ^ (4807/1024 : ℝ) := by
    have hpowers : (50020194962811016209/50000000000000000000 : ℝ)^1024 ≤ (1000086031245321/1000000000000000 : ℝ)^4807 := by
      have hnat : (50020194962811016209 : ℕ)^1024*1000000000000000^4807 ≤ 1000086031245321^4807*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020194962811016209 50000000000000000000 1000086031245321 1000000000000000 1024 4807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000086031245321/1000000000000000 : ℝ)) (X := (50020194962811016209/50000000000000000000 : ℝ)) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1275999441627287/50000000000000000000 : ℝ) ≤ ((29091367115378059551/29095000000000000000 : ℝ)+2*(46974244431/72737500000000 : ℝ)*(10509/100000 : ℝ))^(4807/1024 : ℝ) := by
    rw [show (29091367115378059551/29095000000000000000 : ℝ)+2*(46974244431/72737500000000 : ℝ)*(10509/100000 : ℝ)=(5000054362271157/5000000000000000 : ℝ) by norm_num, show 1+2*(1275999441627287/50000000000000000000 : ℝ)=(25001275999441627287/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20194962811016209/100000000000000000000 : ℝ)+(1275999441627287/50000000000000000000 : ℝ) ≤ ((29091367115378059551/29095000000000000000 : ℝ)+(46974244431/72737500000000 : ℝ)*((2041/12500 : ℝ)+(10509/100000 : ℝ)))^(4807/1024 : ℝ) := by
    rw [show (29091367115378059551/29095000000000000000 : ℝ)+(46974244431/72737500000000 : ℝ)*((2041/12500 : ℝ)+(10509/100000 : ℝ))=(5000242259248881/5000000000000000 : ℝ) by norm_num, show 1+(20194962811016209/100000000000000000000 : ℝ)+(1275999441627287/50000000000000000000 : ℝ)=(100022746961694270783/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20194962811016209/100000000000000000000 : ℝ) ≤ ((29091367115378059551/29095000000000000000 : ℝ)+2*(46974244431/72737500000000 : ℝ)*(2041/12500 : ℝ))^(4807/1024 : ℝ) := by
    rw [show (29091367115378059551/29095000000000000000 : ℝ)+2*(46974244431/72737500000000 : ℝ)*(2041/12500 : ℝ)=(1000086031245321/1000000000000000 : ℝ) by norm_num, show 1+2*(20194962811016209/100000000000000000000 : ℝ)=(50020194962811016209/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29091367115378059551/29095000000000000000 : ℝ)*(X 1 0+X 2 0)+(46974244431/72737500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4807/1024 : ℝ)) (lo := (10509/100000 : ℝ)) (hi := (2041/12500 : ℝ)) (c := (29091367115378059551/29095000000000000000 : ℝ)) (alpha := (46974244431/72737500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29091367115378059551/29095000000000000000 : ℝ)*(X 0 1+X 2 1)+(46974244431/72737500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4807/1024 : ℝ)) (lo := (10509/100000 : ℝ)) (hi := (2041/12500 : ℝ)) (c := (29091367115378059551/29095000000000000000 : ℝ)) (alpha := (46974244431/72737500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29091367115378059551/29095000000000000000 : ℝ)*(X 0 2+X 1 2)+(46974244431/72737500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4807/1024 : ℝ)) (lo := (10509/100000 : ℝ)) (hi := (2041/12500 : ℝ)) (c := (29091367115378059551/29095000000000000000 : ℝ)) (alpha := (46974244431/72737500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-836053329/5000000000 : ℝ)*X 0 0+(5455442081/10000000000 : ℝ)*X 0 1+(5182030403/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351690227/10000000000 : ℝ)*X 1 0+(-906504467/5000000000 : ℝ)*X 1 1+(2591015087/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351690127/10000000000 : ℝ)*X 2 0+(161938447/312500000 : ℝ)*X 2 1+(-3541033/19531250 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((840391801/2000000000 : ℝ)*X 0 0+(967689183/2500000000 : ℝ)*X 0 1+(56926727/125000000 : ℝ)*X 0 2+(840391801/2000000000 : ℝ)*X 1 0+(967689183/2500000000 : ℝ)*X 1 1+(56926727/125000000 : ℝ)*X 1 2+(840391801/2000000000 : ℝ)*X 2 0+(967689183/2500000000 : ℝ)*X 2 1+(56926727/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-836087419/5000000000 : ℝ)*X 0 0+(207362931/400000000 : ℝ)*X 0 1+(68167221/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2639459487/5000000000 : ℝ)*X 1 0+(-154166121/1000000000 : ℝ)*X 1 1+(68167223/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((263945949/500000000 : ℝ)*X 2 0+(34083611/62500000 : ℝ)*X 2 1+(-770830657/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2101064499/5000000000 : ℝ)*X 0 0+(4549031983/10000000000 : ℝ)*X 0 1+(77518337/200000000 : ℝ)*X 0 2+(2101064499/5000000000 : ℝ)*X 1 0+(4549031983/10000000000 : ℝ)*X 1 1+(77518337/200000000 : ℝ)*X 1 2+(2101064499/5000000000 : ℝ)*X 2 0+(4549031983/10000000000 : ℝ)*X 2 1+(77518337/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8077472131709678945188141683/727375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (954026409/50000000000000 : ℝ)*(base19) + (17039509/1000000000000 : ℝ)*(base23) + (72653733/100000000000000 : ℝ)*(lower2) + (134231979/50000000000000 : ℝ)*(upper3) + (189276323/100000000000000 : ℝ)*(upper5) + (2560430618150511/100000000000000 : ℝ)*(major0) + (2560430618150511/100000000000000 : ℝ)*(major1) + (2560430618150511/100000000000000 : ℝ)*(major2) + (1828754937146919/50000000000000 : ℝ)*(sp0) + (914382216162871/25000000000000 : ℝ)*(sp1) + (1828764534376701/50000000000000 : ℝ)*(sp2) + (731660192406139/50000000000000 : ℝ)*(sp3) + (4179682093/20000000000000 : ℝ)*(sp4) + (1941723803/20000000000000 : ℝ)*(sp7) + (365832523357823/25000000000000 : ℝ)*(f.failure) + (1828765386352151/50000000000000 : ℝ)*(f.sum) + (56585488473879/14547500000000000000000000000 : ℝ)*base65 + (145710785443805193/126500000000000000000000000000000 : ℝ)*base68 + (822710594918805193/126500000000000000000000000000000 : ℝ)*base70 + (695501952544805193/126500000000000000000000000000000 : ℝ)*base72 + (71621952421353/29095000000000000000000000000 : ℝ)*base73 + (582474483121805193/126500000000000000000000000000000 : ℝ)*base76 + (1074649673573805193/126500000000000000000000000000000 : ℝ)*base78 + (727635795998694807/126500000000000000000000000000000 : ℝ)*base79 + (59732698231659/14547500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (17811459/2500000000000000000000 : ℝ)*base90 + (17811459/2500000000000000000000 : ℝ)*base92 + (17811459/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6577251717831395630358482223/727375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (789654807/50000000000000 : ℝ)*(base19) + (788138147/50000000000000 : ℝ)*(base23) + (280376591/50000000000000 : ℝ)*(lower1) + (547683/50000000000000 : ℝ)*(upper2) + (24793569/12500000000000 : ℝ)*(upper3) + (31632599/20000000000000 : ℝ)*(upper5) + (2599435242361691/100000000000000 : ℝ)*(major0) + (2599435242361691/100000000000000 : ℝ)*(major1) + (2599435242361691/100000000000000 : ℝ)*(major2) + (84590047/12500000000000 : ℝ)*(sp1) + (464156034616867/12500000000000 : ℝ)*(sp4) + (1856623010452473/50000000000000 : ℝ)*(sp5) + (1856623350329321/50000000000000 : ℝ)*(sp6) + (92851369148341/6250000000000 : ℝ)*(sp7) + (92851369148341/6250000000000 : ℝ)*(f.failure) + (464156034616867/12500000000000 : ℝ)*(f.sum) + (15076127365729/3636875000000000000000000000 : ℝ)*base66 + (595991614223849533/126500000000000000000000000000000 : ℝ)*base68 + (2728083768371849533/126500000000000000000000000000000 : ℝ)*base70 + (339501377517849533/126500000000000000000000000000000 : ℝ)*base72 + (3241726854203/7273750000000000000000000000 : ℝ)*base74 + (21925843252150467/126500000000000000000000000000000 : ℝ)*base75 + (467774199623849533/126500000000000000000000000000000 : ℝ)*base78 + (1228892179003849533/126500000000000000000000000000000 : ℝ)*base80 + (49282759395857/7273750000000000000000000000 : ℝ)*base81 + (4313647/625000000000000000000 : ℝ)*base89 + (4313647/625000000000000000000 : ℝ)*base91 + (4313647/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1623_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174972867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2041/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10509/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10517/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16319/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1623_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1623_s5_0 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-418028363/2500000000 : ℝ)*x 0 + (5455408833/10000000000 : ℝ)*x 1 + (647757389/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418028363/2500000000 : ℝ)^4811 ≤ (10309504239467/100000000000000 : ℝ)^3787 := by
    have hnat : (418028363 : ℕ)^4811*100000000000000^3787 ≤ 10309504239467^3787*2500000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418028363 2500000000 10309504239467 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5455408833/10000000000 : ℝ)^4811 ≤ (23154517903971/50000000000000 : ℝ)^3787 := by
    have hnat : (5455408833 : ℕ)^4811*50000000000000^3787 ≤ 23154517903971^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455408833 10000000000 23154517903971 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647757389/1250000000 : ℝ)^4811 ≤ (21690729968107/50000000000000 : ℝ)^3787 := by
    have hnat : (647757389 : ℕ)^4811*50000000000000^3787 ≤ 21690729968107^3787*1250000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647757389 1250000000 21690729968107 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-418028363/2500000000 : ℝ), (5455408833/10000000000 : ℝ), (647757389/1250000000 : ℝ)] ![(10309504239467/100000000000000 : ℝ), (23154517903971/50000000000000 : ℝ), (21690729968107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-418028363/2500000000 : ℝ)|^4811 ≤ (10309504239467/100000000000000 : ℝ)^3787
        have hw : |(-418028363/2500000000 : ℝ)|=(418028363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5455408833/10000000000 : ℝ)|^4811 ≤ (23154517903971/50000000000000 : ℝ)^3787
        have hw : |(5455408833/10000000000 : ℝ)|=(5455408833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647757389/1250000000 : ℝ)|^4811 ≤ (21690729968107/50000000000000 : ℝ)^3787
        have hw : |(647757389/1250000000 : ℝ)|=(647757389/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s5_1 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070336221/2000000000 : ℝ)*x 0 + (-1812982479/10000000000 : ℝ)*x 1 + (5182059291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070336221/2000000000 : ℝ)^4811 ≤ (22596664247193/50000000000000 : ℝ)^3787 := by
    have hnat : (1070336221 : ℕ)^4811*50000000000000^3787 ≤ 22596664247193^3787*2000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070336221 2000000000 22596664247193 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1812982479/10000000000 : ℝ)^4811 ≤ (2285041931637/20000000000000 : ℝ)^3787 := by
    have hnat : (1812982479 : ℕ)^4811*20000000000000^3787 ≤ 2285041931637^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1812982479 10000000000 2285041931637 20000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182059291/10000000000 : ℝ)^4811 ≤ (21690730919949/50000000000000 : ℝ)^3787 := by
    have hnat : (5182059291 : ℕ)^4811*50000000000000^3787 ≤ 21690730919949^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182059291 10000000000 21690730919949 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070336221/2000000000 : ℝ), (-1812982479/10000000000 : ℝ), (5182059291/10000000000 : ℝ)] ![(22596664247193/50000000000000 : ℝ), (2285041931637/20000000000000 : ℝ), (21690730919949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070336221/2000000000 : ℝ)|^4811 ≤ (22596664247193/50000000000000 : ℝ)^3787
        have hw : |(1070336221/2000000000 : ℝ)|=(1070336221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1812982479/10000000000 : ℝ)|^4811 ≤ (2285041931637/20000000000000 : ℝ)^3787
        have hw : |(-1812982479/10000000000 : ℝ)|=(1812982479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182059291/10000000000 : ℝ)|^4811 ≤ (21690730919949/50000000000000 : ℝ)^3787
        have hw : |(5182059291/10000000000 : ℝ)|=(5182059291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s5_2 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351681069/10000000000 : ℝ)*x 0 + (5182059429/10000000000 : ℝ)*x 1 + (-226622793/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351681069/10000000000 : ℝ)^4811 ≤ (22596664054087/50000000000000 : ℝ)^3787 := by
    have hnat : (5351681069 : ℕ)^4811*50000000000000^3787 ≤ 22596664054087^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351681069 10000000000 22596664054087 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182059429/10000000000 : ℝ)^4811 ≤ (43381463307543/100000000000000 : ℝ)^3787 := by
    have hnat : (5182059429 : ℕ)^4811*100000000000000^3787 ≤ 43381463307543^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182059429 10000000000 43381463307543 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226622793/1250000000 : ℝ)^4811 ≤ (2856302144347/25000000000000 : ℝ)^3787 := by
    have hnat : (226622793 : ℕ)^4811*25000000000000^3787 ≤ 2856302144347^3787*1250000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226622793 1250000000 2856302144347 25000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351681069/10000000000 : ℝ), (5182059429/10000000000 : ℝ), (-226622793/1250000000 : ℝ)] ![(22596664054087/50000000000000 : ℝ), (43381463307543/100000000000000 : ℝ), (2856302144347/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351681069/10000000000 : ℝ)|^4811 ≤ (22596664054087/50000000000000 : ℝ)^3787
        have hw : |(5351681069/10000000000 : ℝ)|=(5351681069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182059429/10000000000 : ℝ)|^4811 ≤ (43381463307543/100000000000000 : ℝ)^3787
        have hw : |(5182059429/10000000000 : ℝ)|=(5182059429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-226622793/1250000000 : ℝ)|^4811 ≤ (2856302144347/25000000000000 : ℝ)^3787
        have hw : |(-226622793/1250000000 : ℝ)|=(226622793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s5_3 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050490793/2500000000 : ℝ)*x 0 + (3870834131/10000000000 : ℝ)*x 1 + (4554060011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050490793/2500000000 : ℝ)^4811 ≤ (16618974042483/50000000000000 : ℝ)^3787 := by
    have hnat : (1050490793 : ℕ)^4811*50000000000000^3787 ≤ 16618974042483^3787*2500000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050490793 2500000000 16618974042483 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3870834131/10000000000 : ℝ)^4811 ≤ (14973297104681/50000000000000 : ℝ)^3787 := by
    have hnat : (3870834131 : ℕ)^4811*50000000000000^3787 ≤ 14973297104681^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3870834131 10000000000 14973297104681 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4554060011/10000000000 : ℝ)^4811 ≤ (18407728844539/50000000000000 : ℝ)^3787 := by
    have hnat : (4554060011 : ℕ)^4811*50000000000000^3787 ≤ 18407728844539^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4554060011 10000000000 18407728844539 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050490793/2500000000 : ℝ), (3870834131/10000000000 : ℝ), (4554060011/10000000000 : ℝ)] ![(16618974042483/50000000000000 : ℝ), (14973297104681/50000000000000 : ℝ), (18407728844539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050490793/2500000000 : ℝ)|^4811 ≤ (16618974042483/50000000000000 : ℝ)^3787
        have hw : |(1050490793/2500000000 : ℝ)|=(1050490793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3870834131/10000000000 : ℝ)|^4811 ≤ (14973297104681/50000000000000 : ℝ)^3787
        have hw : |(3870834131/10000000000 : ℝ)|=(3870834131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4554060011/10000000000 : ℝ)|^4811 ≤ (18407728844539/50000000000000 : ℝ)^3787
        have hw : |(4554060011/10000000000 : ℝ)|=(4554060011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s5_4 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-418045369/2500000000 : ℝ)*x 0 + (5184101179/10000000000 : ℝ)*x 1 + (5453345333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418045369/2500000000 : ℝ)^4811 ≤ (5155018527359/50000000000000 : ℝ)^3787 := by
    have hnat : (418045369 : ℕ)^4811*50000000000000^3787 ≤ 5155018527359^3787*2500000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418045369 2500000000 5155018527359 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184101179/10000000000 : ℝ)^4811 ≤ (8680635738729/20000000000000 : ℝ)^3787 := by
    have hnat : (5184101179 : ℕ)^4811*20000000000000^3787 ≤ 8680635738729^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184101179 10000000000 8680635738729 20000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5453345333/10000000000 : ℝ)^4811 ≤ (1446462007291/3125000000000 : ℝ)^3787 := by
    have hnat : (5453345333 : ℕ)^4811*3125000000000^3787 ≤ 1446462007291^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453345333 10000000000 1446462007291 3125000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-418045369/2500000000 : ℝ), (5184101179/10000000000 : ℝ), (5453345333/10000000000 : ℝ)] ![(5155018527359/50000000000000 : ℝ), (8680635738729/20000000000000 : ℝ), (1446462007291/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-418045369/2500000000 : ℝ)|^4811 ≤ (5155018527359/50000000000000 : ℝ)^3787
        have hw : |(-418045369/2500000000 : ℝ)|=(418045369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184101179/10000000000 : ℝ)|^4811 ≤ (8680635738729/20000000000000 : ℝ)^3787
        have hw : |(5184101179/10000000000 : ℝ)|=(5184101179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5453345333/10000000000 : ℝ)|^4811 ≤ (1446462007291/3125000000000 : ℝ)^3787
        have hw : |(5453345333/10000000000 : ℝ)|=(5453345333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s5_5 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639463211/5000000000 : ℝ)*x 0 + (-308339303/2000000000 : ℝ)*x 1 + (5453345369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639463211/5000000000 : ℝ)^4811 ≤ (22207122970581/50000000000000 : ℝ)^3787 := by
    have hnat : (2639463211 : ℕ)^4811*50000000000000^3787 ≤ 22207122970581^3787*5000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639463211 5000000000 22207122970581 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (308339303/2000000000 : ℝ)^4811 ≤ (9298969428813/100000000000000 : ℝ)^3787 := by
    have hnat : (308339303 : ℕ)^4811*100000000000000^3787 ≤ 9298969428813^3787*2000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      308339303 2000000000 9298969428813 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5453345369/10000000000 : ℝ)^4811 ≤ (9257356924299/20000000000000 : ℝ)^3787 := by
    have hnat : (5453345369 : ℕ)^4811*20000000000000^3787 ≤ 9257356924299^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453345369 10000000000 9257356924299 20000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639463211/5000000000 : ℝ), (-308339303/2000000000 : ℝ), (5453345369/10000000000 : ℝ)] ![(22207122970581/50000000000000 : ℝ), (9298969428813/100000000000000 : ℝ), (9257356924299/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639463211/5000000000 : ℝ)|^4811 ≤ (22207122970581/50000000000000 : ℝ)^3787
        have hw : |(2639463211/5000000000 : ℝ)|=(2639463211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-308339303/2000000000 : ℝ)|^4811 ≤ (9298969428813/100000000000000 : ℝ)^3787
        have hw : |(-308339303/2000000000 : ℝ)|=(308339303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5453345369/10000000000 : ℝ)|^4811 ≤ (9257356924299/20000000000000 : ℝ)^3787
        have hw : |(5453345369/10000000000 : ℝ)|=(5453345369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s5_6 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319731627/2500000000 : ℝ)*x 0 + (5453345257/10000000000 : ℝ)*x 1 + (-1541696551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319731627/2500000000 : ℝ)^4811 ≤ (44414246860373/100000000000000 : ℝ)^3787 := by
    have hnat : (1319731627 : ℕ)^4811*100000000000000^3787 ≤ 44414246860373^3787*2500000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319731627 2500000000 44414246860373 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5453345257/10000000000 : ℝ)^4811 ≤ (23143391706907/50000000000000 : ℝ)^3787 := by
    have hnat : (5453345257 : ℕ)^4811*50000000000000^3787 ≤ 23143391706907^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453345257 10000000000 23143391706907 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1541696551/10000000000 : ℝ)^4811 ≤ (4649484852333/50000000000000 : ℝ)^3787 := by
    have hnat : (1541696551 : ℕ)^4811*50000000000000^3787 ≤ 4649484852333^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1541696551 10000000000 4649484852333 50000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319731627/2500000000 : ℝ), (5453345257/10000000000 : ℝ), (-1541696551/10000000000 : ℝ)] ![(44414246860373/100000000000000 : ℝ), (23143391706907/50000000000000 : ℝ), (4649484852333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319731627/2500000000 : ℝ)|^4811 ≤ (44414246860373/100000000000000 : ℝ)^3787
        have hw : |(1319731627/2500000000 : ℝ)|=(1319731627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5453345257/10000000000 : ℝ)|^4811 ≤ (23143391706907/50000000000000 : ℝ)^3787
        have hw : |(5453345257/10000000000 : ℝ)|=(5453345257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1541696551/10000000000 : ℝ)|^4811 ≤ (4649484852333/50000000000000 : ℝ)^3787
        have hw : |(-1541696551/10000000000 : ℝ)|=(1541696551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1623_s5_7 (p : ℝ) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4202133441/10000000000 : ℝ)*x 0 + (4548955889/10000000000 : ℝ)*x 1 + (387599177/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4202133441/10000000000 : ℝ)^4811 ≤ (33239659124247/100000000000000 : ℝ)^3787 := by
    have hnat : (4202133441 : ℕ)^4811*100000000000000^3787 ≤ 33239659124247^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4202133441 10000000000 33239659124247 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4548955889/10000000000 : ℝ)^4811 ≤ (4595380771637/12500000000000 : ℝ)^3787 := by
    have hnat : (4548955889 : ℕ)^4811*12500000000000^3787 ≤ 4595380771637^3787*10000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4548955889 10000000000 4595380771637 12500000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (387599177/1000000000 : ℝ)^4811 ≤ (29997294689517/100000000000000 : ℝ)^3787 := by
    have hnat : (387599177 : ℕ)^4811*100000000000000^3787 ≤ 29997294689517^3787*1000000000^4811 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387599177 1000000000 29997294689517 100000000000000 4811 3787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4811/1024 : ℝ)) 4811 3787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4202133441/10000000000 : ℝ), (4548955889/10000000000 : ℝ), (387599177/1000000000 : ℝ)] ![(33239659124247/100000000000000 : ℝ), (4595380771637/12500000000000 : ℝ), (29997294689517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4202133441/10000000000 : ℝ)|^4811 ≤ (33239659124247/100000000000000 : ℝ)^3787
        have hw : |(4202133441/10000000000 : ℝ)|=(4202133441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4548955889/10000000000 : ℝ)|^4811 ≤ (4595380771637/12500000000000 : ℝ)^3787
        have hw : |(4548955889/10000000000 : ℝ)|=(4548955889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(387599177/1000000000 : ℝ)|^4811 ≤ (29997294689517/100000000000000 : ℝ)^3787
        have hw : |(387599177/1000000000 : ℝ)|=(387599177/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1623_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174972867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16319/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10517/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5259/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8159/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16319/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10517/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16319/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10517/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16319/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10517/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16319/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10517/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16319/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10517/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16319/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10517/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10517/100000 : ℝ) ^ (4807/1024 : ℝ) ≤ (512226294464307/20000000000000000000 : ℝ) := by
    have hpowers : (10517/100000 : ℝ)^4807 ≤ (512226294464307/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10517 : ℕ)^4807*20000000000000000000^1024 ≤ 512226294464307^1024*100000^4807 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10517 100000 512226294464307 20000000000000000000 4807 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10517/100000 : ℝ)) (X := (512226294464307/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16319/100000 : ℝ) ^ (4807/1024 : ℝ) ≤ (10071380561086527/50000000000000000000 : ℝ) := by
    have hpowers : (16319/100000 : ℝ)^4807 ≤ (10071380561086527/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16319 : ℕ)^4807*50000000000000000000^1024 ≤ 10071380561086527^1024*100000^4807 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16319 100000 10071380561086527 50000000000000000000 4807 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16319/100000 : ℝ)) (X := (10071380561086527/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000512226294464307/10000000000000000000 : ℝ) ≤ (10000109113616369/10000000000000000 : ℝ) ^ (4807/1024 : ℝ) := by
    have hpowers : (10000512226294464307/10000000000000000000 : ℝ)^1024 ≤ (10000109113616369/10000000000000000 : ℝ)^4807 := by
      have hnat : (10000512226294464307 : ℕ)^1024*10000000000000000^4807 ≤ 10000109113616369^4807*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000512226294464307 10000000000000000000 10000109113616369 10000000000000000 1024 4807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000109113616369/10000000000000000 : ℝ)) (X := (10000512226294464307/10000000000000000000 : ℝ)) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100022703892594494589/100000000000000000000 : ℝ) ≤ (10000483601192327/10000000000000000 : ℝ) ^ (4807/1024 : ℝ) := by
    have hpowers : (100022703892594494589/100000000000000000000 : ℝ)^1024 ≤ (10000483601192327/10000000000000000 : ℝ)^4807 := by
      have hnat : (100022703892594494589 : ℕ)^1024*10000000000000000^4807 ≤ 10000483601192327^4807*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100022703892594494589 100000000000000000000 10000483601192327 10000000000000000 1024 4807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000483601192327/10000000000000000 : ℝ)) (X := (100022703892594494589/100000000000000000000 : ℝ)) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010071380561086527/25000000000000000000 : ℝ) ≤ (2000171617753657/2000000000000000 : ℝ) ^ (4807/1024 : ℝ) := by
    have hpowers : (25010071380561086527/25000000000000000000 : ℝ)^1024 ≤ (2000171617753657/2000000000000000 : ℝ)^4807 := by
      have hnat : (25010071380561086527 : ℕ)^1024*2000000000000000^4807 ≤ 2000171617753657^4807*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010071380561086527 25000000000000000000 2000171617753657 2000000000000000 1024 4807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000171617753657/2000000000000000 : ℝ)) (X := (25010071380561086527/25000000000000000000 : ℝ)) (by norm_num) 4807 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(512226294464307/20000000000000000000 : ℝ) ≤ ((9668792684254912061/9670000000000000000 : ℝ)+2*(62414595993/96700000000000 : ℝ)*(10517/100000 : ℝ))^(4807/1024 : ℝ) := by
    rw [show (9668792684254912061/9670000000000000000 : ℝ)+2*(62414595993/96700000000000 : ℝ)*(10517/100000 : ℝ)=(10000109113616369/10000000000000000 : ℝ) by norm_num, show 1+2*(512226294464307/20000000000000000000 : ℝ)=(10000512226294464307/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10071380561086527/50000000000000000000 : ℝ)+(512226294464307/20000000000000000000 : ℝ) ≤ ((9668792684254912061/9670000000000000000 : ℝ)+(62414595993/96700000000000 : ℝ)*((16319/100000 : ℝ)+(10517/100000 : ℝ)))^(4807/1024 : ℝ) := by
    rw [show (9668792684254912061/9670000000000000000 : ℝ)+(62414595993/96700000000000 : ℝ)*((16319/100000 : ℝ)+(10517/100000 : ℝ))=(10000483601192327/10000000000000000 : ℝ) by norm_num, show 1+(10071380561086527/50000000000000000000 : ℝ)+(512226294464307/20000000000000000000 : ℝ)=(100022703892594494589/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10071380561086527/50000000000000000000 : ℝ) ≤ ((9668792684254912061/9670000000000000000 : ℝ)+2*(62414595993/96700000000000 : ℝ)*(16319/100000 : ℝ))^(4807/1024 : ℝ) := by
    rw [show (9668792684254912061/9670000000000000000 : ℝ)+2*(62414595993/96700000000000 : ℝ)*(16319/100000 : ℝ)=(2000171617753657/2000000000000000 : ℝ) by norm_num, show 1+2*(10071380561086527/50000000000000000000 : ℝ)=(25010071380561086527/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9668792684254912061/9670000000000000000 : ℝ)*(X 1 0+X 2 0)+(62414595993/96700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4807/1024 : ℝ)) (lo := (10517/100000 : ℝ)) (hi := (16319/100000 : ℝ)) (c := (9668792684254912061/9670000000000000000 : ℝ)) (alpha := (62414595993/96700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9668792684254912061/9670000000000000000 : ℝ)*(X 0 1+X 2 1)+(62414595993/96700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4807/1024 : ℝ)) (lo := (10517/100000 : ℝ)) (hi := (16319/100000 : ℝ)) (c := (9668792684254912061/9670000000000000000 : ℝ)) (alpha := (62414595993/96700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9668792684254912061/9670000000000000000 : ℝ)*(X 0 2+X 1 2)+(62414595993/96700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4807/1024 : ℝ)) (lo := (10517/100000 : ℝ)) (hi := (16319/100000 : ℝ)) (c := (9668792684254912061/9670000000000000000 : ℝ)) (alpha := (62414595993/96700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-418028363/2500000000 : ℝ)*X 0 0+(5455408833/10000000000 : ℝ)*X 0 1+(647757389/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070336221/2000000000 : ℝ)*X 1 0+(-1812982479/10000000000 : ℝ)*X 1 1+(5182059291/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351681069/10000000000 : ℝ)*X 2 0+(5182059429/10000000000 : ℝ)*X 2 1+(-226622793/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1050490793/2500000000 : ℝ)*X 0 0+(3870834131/10000000000 : ℝ)*X 0 1+(4554060011/10000000000 : ℝ)*X 0 2+(1050490793/2500000000 : ℝ)*X 1 0+(3870834131/10000000000 : ℝ)*X 1 1+(4554060011/10000000000 : ℝ)*X 1 2+(1050490793/2500000000 : ℝ)*X 2 0+(3870834131/10000000000 : ℝ)*X 2 1+(4554060011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-418045369/2500000000 : ℝ)*X 0 0+(5184101179/10000000000 : ℝ)*X 0 1+(5453345333/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2639463211/5000000000 : ℝ)*X 1 0+(-308339303/2000000000 : ℝ)*X 1 1+(5453345369/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319731627/2500000000 : ℝ)*X 2 0+(5453345257/10000000000 : ℝ)*X 2 1+(-1541696551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4202133441/10000000000 : ℝ)*X 0 0+(4548955889/10000000000 : ℝ)*X 0 1+(387599177/1000000000 : ℝ)*X 0 2+(4202133441/10000000000 : ℝ)*X 1 0+(4548955889/10000000000 : ℝ)*X 1 1+(387599177/1000000000 : ℝ)*X 1 2+(4202133441/10000000000 : ℝ)*X 2 0+(4548955889/10000000000 : ℝ)*X 2 1+(387599177/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1623_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (107763884720026240745415651/15109375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1163353771/100000000000000 : ℝ)*(base19) + (1109525551/100000000000000 : ℝ)*(base23) + (15637077/100000000000000 : ℝ)*(lower2) + (10103213/10000000000000 : ℝ)*(upper3) + (179693353/100000000000000 : ℝ)*(upper5) + (80031456178299/3125000000000 : ℝ)*(major0) + (80031456178299/3125000000000 : ℝ)*(major1) + (80031456178299/3125000000000 : ℝ)*(major2) + (914583582909497/25000000000000 : ℝ)*(sp0) + (1829176259335843/50000000000000 : ℝ)*(sp1) + (1829176286249953/50000000000000 : ℝ)*(sp2) + (365913066520507/25000000000000 : ℝ)*(sp3) + (19350387469/100000000000000 : ℝ)*(sp4) + (11215299/160000000000 : ℝ)*(sp7) + (731829637821951/50000000000000 : ℝ)*(f.failure) + (228647105126591/6250000000000 : ℝ)*(f.sum) + (27880459947261/4835000000000000000000000000 : ℝ)*base66 + (312564165232923261/30218750000000000000000000000000 : ℝ)*base68 + (325341450296392011/30218750000000000000000000000000 : ℝ)*base70 + (232530537846704511/30218750000000000000000000000000 : ℝ)*base72 + (15257680435609/4835000000000000000000000000 : ℝ)*base73 + (627569920666110761/30218750000000000000000000000000 : ℝ)*base76 + (392079085660079511/30218750000000000000000000000000 : ℝ)*base78 + (335096465491454511/30218750000000000000000000000000 : ℝ)*base80 + (829633150483/2417500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2003517/5000000000000000000000 : ℝ)*base89 + (2003517/5000000000000000000000 : ℝ)*base91 + (2003517/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14888252517838246299123/2417500000000000000000000000 : ℝ) := by norm_num
    linear_combination (204585169/25000000000000 : ℝ)*(base19) + (485485997/50000000000000 : ℝ)*(base23) + (272822271/100000000000000 : ℝ)*(lower1) + (14077463/12500000000000 : ℝ)*(upper3) + (23199039/50000000000000 : ℝ)*(lower4) + (66121589/50000000000000 : ℝ)*(upper5) + (325003134572337/12500000000000 : ℝ)*(major0) + (325003134572337/12500000000000 : ℝ)*(major1) + (325003134572337/12500000000000 : ℝ)*(major2) + (61403739/20000000000000 : ℝ)*(sp2) + (371409094110953/10000000000000 : ℝ)*(sp4) + (1857045061384427/50000000000000 : ℝ)*(sp5) + (1857044831559421/50000000000000 : ℝ)*(sp6) + (1485959006763429/100000000000000 : ℝ)*(sp7) + (1485959006763429/100000000000000 : ℝ)*(f.failure) + (371409094110953/10000000000000 : ℝ)*(f.sum) + (6271100600113/4835000000000000000000000000 : ℝ)*base65 + (122686322877731557/120875000000000000000000000000000 : ℝ)*base67 + (433312516025143443/120875000000000000000000000000000 : ℝ)*base70 + (3808918084722481557/120875000000000000000000000000000 : ℝ)*base71 + (8237124439343/4835000000000000000000000000 : ℝ)*base73 + (5833933710723356557/120875000000000000000000000000000 : ℝ)*base75 + (502619226402643443/120875000000000000000000000000000 : ℝ)*base78 + (1582971335071393443/120875000000000000000000000000000 : ℝ)*base80 + (3254993991013/1208750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (37119057/10000000000000000000000 : ℝ)*base90 + (37119057/10000000000000000000000 : ℝ)*base92 + (37119057/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1623_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174972867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16319/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10517/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5259/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8159/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1623_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1623_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174972867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16441/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1301/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5259/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8159/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1623_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1623_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1623_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4807/1024 : ℝ) ≤ p) (hpb : p ≤ (4811/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (174972867/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16441/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1301/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5259/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8159/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1623_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
