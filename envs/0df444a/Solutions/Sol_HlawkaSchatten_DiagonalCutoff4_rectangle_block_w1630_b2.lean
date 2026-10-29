-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1630_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:59:56.61509+00:00
-- url     : https://prove2.me/submissions/c2f7eea1-7920-4600-9f90-101f059de38a

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
theorem support_rectangle_w1630_box_0 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1389837851/10000000000 : ℝ)*x 0 + (676628807/1250000000 : ℝ)*x 1 + (2706515231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1389837851/10000000000 : ℝ)^4839 ≤ (4091603884879/50000000000000 : ℝ)^3815 := by
    have hnat : (1389837851 : ℕ)^4839*50000000000000^3815 ≤ 4091603884879^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389837851 10000000000 4091603884879 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676628807/1250000000 : ℝ)^4839 ≤ (45908396076721/100000000000000 : ℝ)^3815 := by
    have hnat : (676628807 : ℕ)^4839*100000000000000^3815 ≤ 45908396076721^3815*1250000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676628807 1250000000 45908396076721 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706515231/5000000000 : ℝ)^4839 ≤ (22954198070633/50000000000000 : ℝ)^3815 := by
    have hnat : (2706515231 : ℕ)^4839*50000000000000^3815 ≤ 22954198070633^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706515231 5000000000 22954198070633 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1389837851/10000000000 : ℝ), (676628807/1250000000 : ℝ), (2706515231/5000000000 : ℝ)] ![(4091603884879/50000000000000 : ℝ), (45908396076721/100000000000000 : ℝ), (22954198070633/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1389837851/10000000000 : ℝ)|^4839 ≤ (4091603884879/50000000000000 : ℝ)^3815
        have hw : |(-1389837851/10000000000 : ℝ)|=(1389837851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676628807/1250000000 : ℝ)|^4839 ≤ (45908396076721/100000000000000 : ℝ)^3815
        have hw : |(676628807/1250000000 : ℝ)|=(676628807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706515231/5000000000 : ℝ)|^4839 ≤ (22954198070633/50000000000000 : ℝ)^3815
        have hw : |(2706515231/5000000000 : ℝ)|=(2706515231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_box_1 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251250589/10000000000 : ℝ)*x 0 + (-1617126447/10000000000 : ℝ)*x 1 + (1082606083/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251250589/10000000000 : ℝ)^4839 ≤ (44175075858967/100000000000000 : ℝ)^3815 := by
    have hnat : (5251250589 : ℕ)^4839*100000000000000^3815 ≤ 44175075858967^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251250589 10000000000 44175075858967 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1617126447/10000000000 : ℝ)^4839 ≤ (79332227927/800000000000 : ℝ)^3815 := by
    have hnat : (1617126447 : ℕ)^4839*800000000000^3815 ≤ 79332227927^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1617126447 10000000000 79332227927 800000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082606083/2000000000 : ℝ)^4839 ≤ (22954197817831/50000000000000 : ℝ)^3815 := by
    have hnat : (1082606083 : ℕ)^4839*50000000000000^3815 ≤ 22954197817831^3815*2000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082606083 2000000000 22954197817831 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251250589/10000000000 : ℝ), (-1617126447/10000000000 : ℝ), (1082606083/2000000000 : ℝ)] ![(44175075858967/100000000000000 : ℝ), (79332227927/800000000000 : ℝ), (22954197817831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251250589/10000000000 : ℝ)|^4839 ≤ (44175075858967/100000000000000 : ℝ)^3815
        have hw : |(5251250589/10000000000 : ℝ)|=(5251250589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1617126447/10000000000 : ℝ)|^4839 ≤ (79332227927/800000000000 : ℝ)^3815
        have hw : |(-1617126447/10000000000 : ℝ)|=(1617126447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082606083/2000000000 : ℝ)|^4839 ≤ (22954197817831/50000000000000 : ℝ)^3815
        have hw : |(1082606083/2000000000 : ℝ)|=(1082606083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_box_2 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625625281/5000000000 : ℝ)*x 0 + (1353257609/2500000000 : ℝ)*x 1 + (-323425291/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625625281/5000000000 : ℝ)^4839 ≤ (44175075570869/100000000000000 : ℝ)^3815 := by
    have hnat : (2625625281 : ℕ)^4839*100000000000000^3815 ≤ 44175075570869^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625625281 5000000000 44175075570869 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353257609/2500000000 : ℝ)^4839 ≤ (4590839586157/10000000000000 : ℝ)^3815 := by
    have hnat : (1353257609 : ℕ)^4839*10000000000000^3815 ≤ 4590839586157^3815*2500000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353257609 2500000000 4590839586157 10000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323425291/2000000000 : ℝ)^4839 ≤ (99165285531/1000000000000 : ℝ)^3815 := by
    have hnat : (323425291 : ℕ)^4839*1000000000000^3815 ≤ 99165285531^3815*2000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323425291 2000000000 99165285531 1000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625625281/5000000000 : ℝ), (1353257609/2500000000 : ℝ), (-323425291/2000000000 : ℝ)] ![(44175075570869/100000000000000 : ℝ), (4590839586157/10000000000000 : ℝ), (99165285531/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625625281/5000000000 : ℝ)|^4839 ≤ (44175075570869/100000000000000 : ℝ)^3815
        have hw : |(2625625281/5000000000 : ℝ)|=(2625625281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353257609/2500000000 : ℝ)|^4839 ≤ (4590839586157/10000000000000 : ℝ)^3815
        have hw : |(1353257609/2500000000 : ℝ)|=(1353257609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-323425291/2000000000 : ℝ)|^4839 ≤ (99165285531/1000000000000 : ℝ)^3815
        have hw : |(-323425291/2000000000 : ℝ)|=(323425291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_box_3 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (447458309/1000000000 : ℝ)*x 0 + (813922711/2000000000 : ℝ)*x 1 + (4069613533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (447458309/1000000000 : ℝ)^4839 ≤ (36058663460191/100000000000000 : ℝ)^3815 := by
    have hnat : (447458309 : ℕ)^4839*100000000000000^3815 ≤ 36058663460191^3815*1000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447458309 1000000000 36058663460191 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (813922711/2000000000 : ℝ)^4839 ≤ (6394133674893/20000000000000 : ℝ)^3815 := by
    have hnat : (813922711 : ℕ)^4839*20000000000000^3815 ≤ 6394133674893^3815*2000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      813922711 2000000000 6394133674893 20000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4069613533/10000000000 : ℝ)^4839 ≤ (7992667038811/25000000000000 : ℝ)^3815 := by
    have hnat : (4069613533 : ℕ)^4839*25000000000000^3815 ≤ 7992667038811^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4069613533 10000000000 7992667038811 25000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(447458309/1000000000 : ℝ), (813922711/2000000000 : ℝ), (4069613533/10000000000 : ℝ)] ![(36058663460191/100000000000000 : ℝ), (6394133674893/20000000000000 : ℝ), (7992667038811/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(447458309/1000000000 : ℝ)|^4839 ≤ (36058663460191/100000000000000 : ℝ)^3815
        have hw : |(447458309/1000000000 : ℝ)|=(447458309/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(813922711/2000000000 : ℝ)|^4839 ≤ (6394133674893/20000000000000 : ℝ)^3815
        have hw : |(813922711/2000000000 : ℝ)|=(813922711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4069613533/10000000000 : ℝ)|^4839 ≤ (7992667038811/25000000000000 : ℝ)^3815
        have hw : |(4069613533/10000000000 : ℝ)|=(4069613533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_box_4 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-241409679/1250000000 : ℝ)*x 0 + (5215082559/10000000000 : ℝ)*x 1 + (5215084099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (241409679/1250000000 : ℝ)^4839 ≤ (6210481458319/50000000000000 : ℝ)^3815 := by
    have hnat : (241409679 : ℕ)^4839*50000000000000^3815 ≤ 6210481458319^3815*1250000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241409679 1250000000 6210481458319 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215082559/10000000000 : ℝ)^4839 ≤ (10947377584333/25000000000000 : ℝ)^3815 := by
    have hnat : (5215082559 : ℕ)^4839*25000000000000^3815 ≤ 10947377584333^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215082559 10000000000 10947377584333 25000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215084099/10000000000 : ℝ)^4839 ≤ (21894763369551/50000000000000 : ℝ)^3815 := by
    have hnat : (5215084099 : ℕ)^4839*50000000000000^3815 ≤ 21894763369551^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215084099 10000000000 21894763369551 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-241409679/1250000000 : ℝ), (5215082559/10000000000 : ℝ), (5215084099/10000000000 : ℝ)] ![(6210481458319/50000000000000 : ℝ), (10947377584333/25000000000000 : ℝ), (21894763369551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-241409679/1250000000 : ℝ)|^4839 ≤ (6210481458319/50000000000000 : ℝ)^3815
        have hw : |(-241409679/1250000000 : ℝ)|=(241409679/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215082559/10000000000 : ℝ)|^4839 ≤ (10947377584333/25000000000000 : ℝ)^3815
        have hw : |(5215082559/10000000000 : ℝ)|=(5215082559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215084099/10000000000 : ℝ)|^4839 ≤ (21894763369551/50000000000000 : ℝ)^3815
        have hw : |(5215084099/10000000000 : ℝ)|=(5215084099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_box_5 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538748731/1000000000 : ℝ)*x 0 + (-1701417501/10000000000 : ℝ)*x 1 + (5215083837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538748731/1000000000 : ℝ)^4839 ≤ (45633789033657/100000000000000 : ℝ)^3815 := by
    have hnat : (538748731 : ℕ)^4839*100000000000000^3815 ≤ 45633789033657^3815*1000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538748731 1000000000 45633789033657 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1701417501/10000000000 : ℝ)^4839 ≤ (10576687004969/100000000000000 : ℝ)^3815 := by
    have hnat : (1701417501 : ℕ)^4839*100000000000000^3815 ≤ 10576687004969^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1701417501 10000000000 10576687004969 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215083837/10000000000 : ℝ)^4839 ≤ (43789523948671/100000000000000 : ℝ)^3815 := by
    have hnat : (5215083837 : ℕ)^4839*100000000000000^3815 ≤ 43789523948671^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215083837 10000000000 43789523948671 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538748731/1000000000 : ℝ), (-1701417501/10000000000 : ℝ), (5215083837/10000000000 : ℝ)] ![(45633789033657/100000000000000 : ℝ), (10576687004969/100000000000000 : ℝ), (43789523948671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538748731/1000000000 : ℝ)|^4839 ≤ (45633789033657/100000000000000 : ℝ)^3815
        have hw : |(538748731/1000000000 : ℝ)|=(538748731/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1701417501/10000000000 : ℝ)|^4839 ≤ (10576687004969/100000000000000 : ℝ)^3815
        have hw : |(-1701417501/10000000000 : ℝ)|=(1701417501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215083837/10000000000 : ℝ)|^4839 ≤ (43789523948671/100000000000000 : ℝ)^3815
        have hw : |(5215083837/10000000000 : ℝ)|=(5215083837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_box_6 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26937437/50000000 : ℝ)*x 0 + (1043016581/2000000000 : ℝ)*x 1 + (-1701418637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26937437/50000000 : ℝ)^4839 ≤ (45633790000607/100000000000000 : ℝ)^3815 := by
    have hnat : (26937437 : ℕ)^4839*100000000000000^3815 ≤ 45633790000607^3815*50000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26937437 50000000 45633790000607 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043016581/2000000000 : ℝ)^4839 ≤ (8757902804481/20000000000000 : ℝ)^3815 := by
    have hnat : (1043016581 : ℕ)^4839*20000000000000^3815 ≤ 8757902804481^3815*2000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043016581 2000000000 8757902804481 20000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1701418637/10000000000 : ℝ)^4839 ≤ (2644173990573/25000000000000 : ℝ)^3815 := by
    have hnat : (1701418637 : ℕ)^4839*25000000000000^3815 ≤ 2644173990573^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1701418637 10000000000 2644173990573 25000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26937437/50000000 : ℝ), (1043016581/2000000000 : ℝ), (-1701418637/10000000000 : ℝ)] ![(45633790000607/100000000000000 : ℝ), (8757902804481/20000000000000 : ℝ), (2644173990573/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26937437/50000000 : ℝ)|^4839 ≤ (45633790000607/100000000000000 : ℝ)^3815
        have hw : |(26937437/50000000 : ℝ)|=(26937437/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043016581/2000000000 : ℝ)|^4839 ≤ (8757902804481/20000000000000 : ℝ)^3815
        have hw : |(1043016581/2000000000 : ℝ)|=(1043016581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1701418637/10000000000 : ℝ)|^4839 ≤ (2644173990573/25000000000000 : ℝ)^3815
        have hw : |(-1701418637/10000000000 : ℝ)|=(1701418637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_box_7 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3911944391/10000000000 : ℝ)*x 0 + (1087649829/2500000000 : ℝ)*x 1 + (2175299517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3911944391/10000000000 : ℝ)^4839 ≤ (30407806737639/100000000000000 : ℝ)^3815 := by
    have hnat : (3911944391 : ℕ)^4839*100000000000000^3815 ≤ 30407806737639^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3911944391 10000000000 30407806737639 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087649829/2500000000 : ℝ)^4839 ≤ (17398049028383/50000000000000 : ℝ)^3815 := by
    have hnat : (1087649829 : ℕ)^4839*50000000000000^3815 ≤ 17398049028383^3815*2500000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087649829 2500000000 17398049028383 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2175299517/5000000000 : ℝ)^4839 ≤ (34796095195939/100000000000000 : ℝ)^3815 := by
    have hnat : (2175299517 : ℕ)^4839*100000000000000^3815 ≤ 34796095195939^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175299517 5000000000 34796095195939 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3911944391/10000000000 : ℝ), (1087649829/2500000000 : ℝ), (2175299517/5000000000 : ℝ)] ![(30407806737639/100000000000000 : ℝ), (17398049028383/50000000000000 : ℝ), (34796095195939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3911944391/10000000000 : ℝ)|^4839 ≤ (30407806737639/100000000000000 : ℝ)^3815
        have hw : |(3911944391/10000000000 : ℝ)|=(3911944391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087649829/2500000000 : ℝ)|^4839 ≤ (17398049028383/50000000000000 : ℝ)^3815
        have hw : |(1087649829/2500000000 : ℝ)|=(1087649829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2175299517/5000000000 : ℝ)|^4839 ≤ (34796095195939/100000000000000 : ℝ)^3815
        have hw : |(2175299517/5000000000 : ℝ)|=(2175299517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_box_8 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-226994881/1250000000 : ℝ)*x 0 + (5073203329/10000000000 : ℝ)*x 1 + (2721366027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (226994881/1250000000 : ℝ)^4839 ≤ (2871968260253/25000000000000 : ℝ)^3815 := by
    have hnat : (226994881 : ℕ)^4839*25000000000000^3815 ≤ 2871968260253^3815*1250000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226994881 1250000000 2871968260253 25000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5073203329/10000000000 : ℝ)^4839 ≤ (42283979935129/100000000000000 : ℝ)^3815 := by
    have hnat : (5073203329 : ℕ)^4839*100000000000000^3815 ≤ 42283979935129^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5073203329 10000000000 42283979935129 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721366027/5000000000 : ℝ)^4839 ≤ (23114073503147/50000000000000 : ℝ)^3815 := by
    have hnat : (2721366027 : ℕ)^4839*50000000000000^3815 ≤ 23114073503147^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721366027 5000000000 23114073503147 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-226994881/1250000000 : ℝ), (5073203329/10000000000 : ℝ), (2721366027/5000000000 : ℝ)] ![(2871968260253/25000000000000 : ℝ), (42283979935129/100000000000000 : ℝ), (23114073503147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-226994881/1250000000 : ℝ)|^4839 ≤ (2871968260253/25000000000000 : ℝ)^3815
        have hw : |(-226994881/1250000000 : ℝ)|=(226994881/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5073203329/10000000000 : ℝ)|^4839 ≤ (42283979935129/100000000000000 : ℝ)^3815
        have hw : |(5073203329/10000000000 : ℝ)|=(5073203329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721366027/5000000000 : ℝ)|^4839 ≤ (23114073503147/50000000000000 : ℝ)^3815
        have hw : |(2721366027/5000000000 : ℝ)|=(2721366027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_box_9 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230806787/10000000000 : ℝ)*x 0 + (-802016839/5000000000 : ℝ)*x 1 + (5442732267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230806787/10000000000 : ℝ)^4839 ≤ (219785244697/500000000000 : ℝ)^3815 := by
    have hnat : (5230806787 : ℕ)^4839*500000000000^3815 ≤ 219785244697^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230806787 10000000000 219785244697 500000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (802016839/5000000000 : ℝ)^4839 ≤ (4907400869239/50000000000000 : ℝ)^3815 := by
    have hnat : (802016839 : ℕ)^4839*50000000000000^3815 ≤ 4907400869239^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802016839 5000000000 4907400869239 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5442732267/10000000000 : ℝ)^4839 ≤ (46228149301017/100000000000000 : ℝ)^3815 := by
    have hnat : (5442732267 : ℕ)^4839*100000000000000^3815 ≤ 46228149301017^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442732267 10000000000 46228149301017 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230806787/10000000000 : ℝ), (-802016839/5000000000 : ℝ), (5442732267/10000000000 : ℝ)] ![(219785244697/500000000000 : ℝ), (4907400869239/50000000000000 : ℝ), (46228149301017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230806787/10000000000 : ℝ)|^4839 ≤ (219785244697/500000000000 : ℝ)^3815
        have hw : |(5230806787/10000000000 : ℝ)|=(5230806787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-802016839/5000000000 : ℝ)|^4839 ≤ (4907400869239/50000000000000 : ℝ)^3815
        have hw : |(-802016839/5000000000 : ℝ)|=(802016839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5442732267/10000000000 : ℝ)|^4839 ≤ (46228149301017/100000000000000 : ℝ)^3815
        have hw : |(5442732267/10000000000 : ℝ)|=(5442732267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_box_10 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1307701739/2500000000 : ℝ)*x 0 + (544273233/1000000000 : ℝ)*x 1 + (-20050417/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1307701739/2500000000 : ℝ)^4839 ≤ (43957050740789/100000000000000 : ℝ)^3815 := by
    have hnat : (1307701739 : ℕ)^4839*100000000000000^3815 ≤ 43957050740789^3815*2500000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307701739 2500000000 43957050740789 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544273233/1000000000 : ℝ)^4839 ≤ (23114074989869/50000000000000 : ℝ)^3815 := by
    have hnat : (544273233 : ℕ)^4839*50000000000000^3815 ≤ 23114074989869^3815*1000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544273233 1000000000 23114074989869 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20050417/125000000 : ℝ)^4839 ≤ (1962959854083/20000000000000 : ℝ)^3815 := by
    have hnat : (20050417 : ℕ)^4839*20000000000000^3815 ≤ 1962959854083^3815*125000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20050417 125000000 1962959854083 20000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1307701739/2500000000 : ℝ), (544273233/1000000000 : ℝ), (-20050417/125000000 : ℝ)] ![(43957050740789/100000000000000 : ℝ), (23114074989869/50000000000000 : ℝ), (1962959854083/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1307701739/2500000000 : ℝ)|^4839 ≤ (43957050740789/100000000000000 : ℝ)^3815
        have hw : |(1307701739/2500000000 : ℝ)|=(1307701739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(544273233/1000000000 : ℝ)|^4839 ≤ (23114074989869/50000000000000 : ℝ)^3815
        have hw : |(544273233/1000000000 : ℝ)|=(544273233/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-20050417/125000000 : ℝ)|^4839 ≤ (1962959854083/20000000000000 : ℝ)^3815
        have hw : |(-20050417/125000000 : ℝ)|=(20050417/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_box_11 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (455661959/1000000000 : ℝ)*x 0 + (4027375469/10000000000 : ℝ)*x 1 + (4027375279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (455661959/1000000000 : ℝ)^4839 ≤ (18449630203471/50000000000000 : ℝ)^3815 := by
    have hnat : (455661959 : ℕ)^4839*50000000000000^3815 ≤ 18449630203471^3815*1000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455661959 1000000000 18449630203471 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4027375469/10000000000 : ℝ)^4839 ≤ (7887592682833/25000000000000 : ℝ)^3815 := by
    have hnat : (4027375469 : ℕ)^4839*25000000000000^3815 ≤ 7887592682833^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4027375469 10000000000 7887592682833 25000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4027375279/10000000000 : ℝ)^4839 ≤ (15775184421677/50000000000000 : ℝ)^3815 := by
    have hnat : (4027375279 : ℕ)^4839*50000000000000^3815 ≤ 15775184421677^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4027375279 10000000000 15775184421677 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(455661959/1000000000 : ℝ), (4027375469/10000000000 : ℝ), (4027375279/10000000000 : ℝ)] ![(18449630203471/50000000000000 : ℝ), (7887592682833/25000000000000 : ℝ), (15775184421677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(455661959/1000000000 : ℝ)|^4839 ≤ (18449630203471/50000000000000 : ℝ)^3815
        have hw : |(455661959/1000000000 : ℝ)|=(455661959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4027375469/10000000000 : ℝ)|^4839 ≤ (7887592682833/25000000000000 : ℝ)^3815
        have hw : |(4027375469/10000000000 : ℝ)|=(4027375469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4027375279/10000000000 : ℝ)|^4839 ≤ (15775184421677/50000000000000 : ℝ)^3815
        have hw : |(4027375279/10000000000 : ℝ)|=(4027375279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_box_12 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-375912021/2500000000 : ℝ)*x 0 + (5549323599/10000000000 : ℝ)*x 1 + (207809153/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (375912021/2500000000 : ℝ)^4839 ≤ (4521167570667/50000000000000 : ℝ)^3815 := by
    have hnat : (375912021 : ℕ)^4839*50000000000000^3815 ≤ 4521167570667^3815*2500000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375912021 2500000000 4521167570667 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5549323599/10000000000 : ℝ)^4839 ≤ (9475899712219/20000000000000 : ℝ)^3815 := by
    have hnat : (5549323599 : ℕ)^4839*20000000000000^3815 ≤ 9475899712219^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5549323599 10000000000 9475899712219 20000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207809153/400000000 : ℝ)^4839 ≤ (4357816628769/10000000000000 : ℝ)^3815 := by
    have hnat : (207809153 : ℕ)^4839*10000000000000^3815 ≤ 4357816628769^3815*400000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207809153 400000000 4357816628769 10000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-375912021/2500000000 : ℝ), (5549323599/10000000000 : ℝ), (207809153/400000000 : ℝ)] ![(4521167570667/50000000000000 : ℝ), (9475899712219/20000000000000 : ℝ), (4357816628769/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-375912021/2500000000 : ℝ)|^4839 ≤ (4521167570667/50000000000000 : ℝ)^3815
        have hw : |(-375912021/2500000000 : ℝ)|=(375912021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5549323599/10000000000 : ℝ)|^4839 ≤ (9475899712219/20000000000000 : ℝ)^3815
        have hw : |(5549323599/10000000000 : ℝ)|=(5549323599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207809153/400000000 : ℝ)|^4839 ≤ (4357816628769/10000000000000 : ℝ)^3815
        have hw : |(207809153/400000000 : ℝ)|=(207809153/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_box_13 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540116041/1000000000 : ℝ)*x 0 + (-854790093/5000000000 : ℝ)*x 1 + (5195228971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540116041/1000000000 : ℝ)^4839 ≤ (45780741252539/100000000000000 : ℝ)^3815 := by
    have hnat : (540116041 : ℕ)^4839*100000000000000^3815 ≤ 45780741252539^3815*1000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540116041 1000000000 45780741252539 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (854790093/5000000000 : ℝ)^4839 ≤ (10641090893023/100000000000000 : ℝ)^3815 := by
    have hnat : (854790093 : ℕ)^4839*100000000000000^3815 ≤ 10641090893023^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854790093 5000000000 10641090893023 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5195228971/10000000000 : ℝ)^4839 ≤ (2723635490067/6250000000000 : ℝ)^3815 := by
    have hnat : (5195228971 : ℕ)^4839*6250000000000^3815 ≤ 2723635490067^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195228971 10000000000 2723635490067 6250000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540116041/1000000000 : ℝ), (-854790093/5000000000 : ℝ), (5195228971/10000000000 : ℝ)] ![(45780741252539/100000000000000 : ℝ), (10641090893023/100000000000000 : ℝ), (2723635490067/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540116041/1000000000 : ℝ)|^4839 ≤ (45780741252539/100000000000000 : ℝ)^3815
        have hw : |(540116041/1000000000 : ℝ)|=(540116041/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-854790093/5000000000 : ℝ)|^4839 ≤ (10641090893023/100000000000000 : ℝ)^3815
        have hw : |(-854790093/5000000000 : ℝ)|=(854790093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5195228971/10000000000 : ℝ)|^4839 ≤ (2723635490067/6250000000000 : ℝ)^3815
        have hw : |(5195228971/10000000000 : ℝ)|=(5195228971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_box_14 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1350290151/2500000000 : ℝ)*x 0 + (81175449/156250000 : ℝ)*x 1 + (-1709580239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1350290151/2500000000 : ℝ)^4839 ≤ (45780743338271/100000000000000 : ℝ)^3815 := by
    have hnat : (1350290151 : ℕ)^4839*100000000000000^3815 ≤ 45780743338271^3815*2500000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350290151 2500000000 45780743338271 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81175449/156250000 : ℝ)^4839 ≤ (21789082670383/50000000000000 : ℝ)^3815 := by
    have hnat : (81175449 : ℕ)^4839*50000000000000^3815 ≤ 21789082670383^3815*156250000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81175449 156250000 21789082670383 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1709580239/10000000000 : ℝ)^4839 ≤ (1330136413933/12500000000000 : ℝ)^3815 := by
    have hnat : (1709580239 : ℕ)^4839*12500000000000^3815 ≤ 1330136413933^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1709580239 10000000000 1330136413933 12500000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1350290151/2500000000 : ℝ), (81175449/156250000 : ℝ), (-1709580239/10000000000 : ℝ)] ![(45780743338271/100000000000000 : ℝ), (21789082670383/50000000000000 : ℝ), (1330136413933/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1350290151/2500000000 : ℝ)|^4839 ≤ (45780743338271/100000000000000 : ℝ)^3815
        have hw : |(1350290151/2500000000 : ℝ)|=(1350290151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81175449/156250000 : ℝ)|^4839 ≤ (21789082670383/50000000000000 : ℝ)^3815
        have hw : |(81175449/156250000 : ℝ)|=(81175449/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1709580239/10000000000 : ℝ)|^4839 ≤ (1330136413933/12500000000000 : ℝ)^3815
        have hw : |(-1709580239/10000000000 : ℝ)|=(1709580239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_box_15 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1926941607/5000000000 : ℝ)*x 0 + (2189366423/5000000000 : ℝ)*x 1 + (4378732219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1926941607/5000000000 : ℝ)^4839 ≤ (29836498816633/100000000000000 : ℝ)^3815 := by
    have hnat : (1926941607 : ℕ)^4839*100000000000000^3815 ≤ 29836498816633^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926941607 5000000000 29836498816633 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2189366423/5000000000 : ℝ)^4839 ≤ (877043844313/2500000000000 : ℝ)^3815 := by
    have hnat : (2189366423 : ℕ)^4839*2500000000000^3815 ≤ 877043844313^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189366423 5000000000 877043844313 2500000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4378732219/10000000000 : ℝ)^4839 ≤ (35081747400729/100000000000000 : ℝ)^3815 := by
    have hnat : (4378732219 : ℕ)^4839*100000000000000^3815 ≤ 35081747400729^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378732219 10000000000 35081747400729 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1926941607/5000000000 : ℝ), (2189366423/5000000000 : ℝ), (4378732219/10000000000 : ℝ)] ![(29836498816633/100000000000000 : ℝ), (877043844313/2500000000000 : ℝ), (35081747400729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1926941607/5000000000 : ℝ)|^4839 ≤ (29836498816633/100000000000000 : ℝ)^3815
        have hw : |(1926941607/5000000000 : ℝ)|=(1926941607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2189366423/5000000000 : ℝ)|^4839 ≤ (877043844313/2500000000000 : ℝ)^3815
        have hw : |(2189366423/5000000000 : ℝ)|=(2189366423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4378732219/10000000000 : ℝ)|^4839 ≤ (35081747400729/100000000000000 : ℝ)^3815
        have hw : |(4378732219/10000000000 : ℝ)|=(4378732219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1630_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35221777/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3261/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (66/625 : ℝ)*pair X i i ≤ pair X i h) :
    -(16247/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(5841/10000 : ℝ) ∧ (10103/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (88027/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3261/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (66/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3261/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (66/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3261/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (66/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3261/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (66/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3261/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (66/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3261/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (66/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (66/625 : ℝ) ^ (4835/1024 : ℝ) ≤ (2455012763720543/100000000000000000000 : ℝ) := by
    have hpowers : (66/625 : ℝ)^4835 ≤ (2455012763720543/100000000000000000000 : ℝ)^1024 := by
      have hnat : (66 : ℕ)^4835*100000000000000000000^1024 ≤ 2455012763720543^1024*625^4835 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66 625 2455012763720543 100000000000000000000 4835 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (66/625 : ℝ)) (X := (2455012763720543/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3261/20000 : ℝ) ^ (4835/1024 : ℝ) ≤ (19091108063395063/100000000000000000000 : ℝ) := by
    have hpowers : (3261/20000 : ℝ)^4835 ≤ (19091108063395063/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3261 : ℕ)^4835*100000000000000000000^1024 ≤ 19091108063395063^1024*20000^4835 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3261 20000 19091108063395063 100000000000000000000 4835 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3261/20000 : ℝ)) (X := (19091108063395063/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002455012763720543/50000000000000000000 : ℝ) ≤ (10000103986946233/10000000000000000 : ℝ) ^ (4835/1024 : ℝ) := by
    have hpowers : (50002455012763720543/50000000000000000000 : ℝ)^1024 ≤ (10000103986946233/10000000000000000 : ℝ)^4835 := by
      have hnat : (50002455012763720543 : ℕ)^1024*10000000000000000^4835 ≤ 10000103986946233^4835*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002455012763720543 50000000000000000000 10000103986946233 10000000000000000 1024 4835 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000103986946233/10000000000000000 : ℝ)) (X := (50002455012763720543/50000000000000000000 : ℝ)) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50010773060413557803/50000000000000000000 : ℝ) ≤ (10000456284477371/10000000000000000 : ℝ) ^ (4835/1024 : ℝ) := by
    have hpowers : (50010773060413557803/50000000000000000000 : ℝ)^1024 ≤ (10000456284477371/10000000000000000 : ℝ)^4835 := by
      have hnat : (50010773060413557803 : ℕ)^1024*10000000000000000^4835 ≤ 10000456284477371^4835*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010773060413557803 50000000000000000000 10000456284477371 10000000000000000 1024 4835 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000456284477371/10000000000000000 : ℝ)) (X := (50010773060413557803/50000000000000000000 : ℝ)) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50019091108063395063/50000000000000000000 : ℝ) ≤ (10000808582008509/10000000000000000 : ℝ) ^ (4835/1024 : ℝ) := by
    have hpowers : (50019091108063395063/50000000000000000000 : ℝ)^1024 ≤ (10000808582008509/10000000000000000 : ℝ)^4835 := by
      have hnat : (50019091108063395063 : ℕ)^1024*10000000000000000^4835 ≤ 10000808582008509^4835*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019091108063395063 50000000000000000000 10000808582008509 10000000000000000 1024 4835 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000808582008509/10000000000000000 : ℝ)) (X := (50019091108063395063/50000000000000000000 : ℝ)) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2455012763720543/100000000000000000000 : ℝ) ≤ ((765908758415312987/766000000000000000 : ℝ)+2*(176148765569/287250000000000 : ℝ)*(66/625 : ℝ))^(4835/1024 : ℝ) := by
    rw [show (765908758415312987/766000000000000000 : ℝ)+2*(176148765569/287250000000000 : ℝ)*(66/625 : ℝ)=(10000103986946233/10000000000000000 : ℝ) by norm_num, show 1+2*(2455012763720543/100000000000000000000 : ℝ)=(50002455012763720543/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19091108063395063/100000000000000000000 : ℝ)+(2455012763720543/100000000000000000000 : ℝ) ≤ ((765908758415312987/766000000000000000 : ℝ)+(176148765569/287250000000000 : ℝ)*((3261/20000 : ℝ)+(66/625 : ℝ)))^(4835/1024 : ℝ) := by
    rw [show (765908758415312987/766000000000000000 : ℝ)+(176148765569/287250000000000 : ℝ)*((3261/20000 : ℝ)+(66/625 : ℝ))=(10000456284477371/10000000000000000 : ℝ) by norm_num, show 1+(19091108063395063/100000000000000000000 : ℝ)+(2455012763720543/100000000000000000000 : ℝ)=(50010773060413557803/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19091108063395063/100000000000000000000 : ℝ) ≤ ((765908758415312987/766000000000000000 : ℝ)+2*(176148765569/287250000000000 : ℝ)*(3261/20000 : ℝ))^(4835/1024 : ℝ) := by
    rw [show (765908758415312987/766000000000000000 : ℝ)+2*(176148765569/287250000000000 : ℝ)*(3261/20000 : ℝ)=(10000808582008509/10000000000000000 : ℝ) by norm_num, show 1+2*(19091108063395063/100000000000000000000 : ℝ)=(50019091108063395063/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (765908758415312987/766000000000000000 : ℝ)*(X 1 0+X 2 0)+(176148765569/287250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4835/1024 : ℝ)) (lo := (66/625 : ℝ)) (hi := (3261/20000 : ℝ)) (c := (765908758415312987/766000000000000000 : ℝ)) (alpha := (176148765569/287250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (765908758415312987/766000000000000000 : ℝ)*(X 0 1+X 2 1)+(176148765569/287250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4835/1024 : ℝ)) (lo := (66/625 : ℝ)) (hi := (3261/20000 : ℝ)) (c := (765908758415312987/766000000000000000 : ℝ)) (alpha := (176148765569/287250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (765908758415312987/766000000000000000 : ℝ)*(X 0 2+X 1 2)+(176148765569/287250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4835/1024 : ℝ)) (lo := (66/625 : ℝ)) (hi := (3261/20000 : ℝ)) (c := (765908758415312987/766000000000000000 : ℝ)) (alpha := (176148765569/287250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1389837851/10000000000 : ℝ)*X 0 0+(676628807/1250000000 : ℝ)*X 0 1+(2706515231/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5251250589/10000000000 : ℝ)*X 1 0+(-1617126447/10000000000 : ℝ)*X 1 1+(1082606083/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2625625281/5000000000 : ℝ)*X 2 0+(1353257609/2500000000 : ℝ)*X 2 1+(-323425291/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((447458309/1000000000 : ℝ)*X 0 0+(813922711/2000000000 : ℝ)*X 0 1+(4069613533/10000000000 : ℝ)*X 0 2+(447458309/1000000000 : ℝ)*X 1 0+(813922711/2000000000 : ℝ)*X 1 1+(4069613533/10000000000 : ℝ)*X 1 2+(447458309/1000000000 : ℝ)*X 2 0+(813922711/2000000000 : ℝ)*X 2 1+(4069613533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-241409679/1250000000 : ℝ)*X 0 0+(5215082559/10000000000 : ℝ)*X 0 1+(5215084099/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((538748731/1000000000 : ℝ)*X 1 0+(-1701417501/10000000000 : ℝ)*X 1 1+(5215083837/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((26937437/50000000 : ℝ)*X 2 0+(1043016581/2000000000 : ℝ)*X 2 1+(-1701418637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3911944391/10000000000 : ℝ)*X 0 0+(1087649829/2500000000 : ℝ)*X 0 1+(2175299517/5000000000 : ℝ)*X 0 2+(3911944391/10000000000 : ℝ)*X 1 0+(1087649829/2500000000 : ℝ)*X 1 1+(2175299517/5000000000 : ℝ)*X 1 2+(3911944391/10000000000 : ℝ)*X 2 0+(1087649829/2500000000 : ℝ)*X 2 1+(2175299517/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-226994881/1250000000 : ℝ)*X 0 0+(5073203329/10000000000 : ℝ)*X 0 1+(2721366027/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5230806787/10000000000 : ℝ)*X 1 0+(-802016839/5000000000 : ℝ)*X 1 1+(5442732267/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1307701739/2500000000 : ℝ)*X 2 0+(544273233/1000000000 : ℝ)*X 2 1+(-20050417/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((455661959/1000000000 : ℝ)*X 0 0+(4027375469/10000000000 : ℝ)*X 0 1+(4027375279/10000000000 : ℝ)*X 0 2+(455661959/1000000000 : ℝ)*X 1 0+(4027375469/10000000000 : ℝ)*X 1 1+(4027375279/10000000000 : ℝ)*X 1 2+(455661959/1000000000 : ℝ)*X 2 0+(4027375469/10000000000 : ℝ)*X 2 1+(4027375279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-375912021/2500000000 : ℝ)*X 0 0+(5549323599/10000000000 : ℝ)*X 0 1+(207809153/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((540116041/1000000000 : ℝ)*X 1 0+(-854790093/5000000000 : ℝ)*X 1 1+(5195228971/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1350290151/2500000000 : ℝ)*X 2 0+(81175449/156250000 : ℝ)*X 2 1+(-1709580239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1926941607/5000000000 : ℝ)*X 0 0+(2189366423/5000000000 : ℝ)*X 0 1+(4378732219/10000000000 : ℝ)*X 0 2+(1926941607/5000000000 : ℝ)*X 1 0+(2189366423/5000000000 : ℝ)*X 1 1+(4378732219/10000000000 : ℝ)*X 1 2+(1926941607/5000000000 : ℝ)*X 2 0+(2189366423/5000000000 : ℝ)*X 2 1+(4378732219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-16247/25000 : ℝ) ≤ (-6222410634472390083145216107971/9575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (170000589/100000000000000 : ℝ)*(upper1) + (125175281/50000000000000 : ℝ)*(lower4) + (26920759/100000000000000 : ℝ)*(upper5) + (430165917662411/25000000000000 : ℝ)*(major0) + (430165917662411/25000000000000 : ℝ)*(major1) + (430165917662411/25000000000000 : ℝ)*(major2) + (3431062717/25000000000000 : ℝ)*(sp2) + (1599546711/50000000000000 : ℝ)*(sp3) + (62148352500861/2500000000000 : ℝ)*(sp4) + (1242940641060253/50000000000000 : ℝ)*(sp5) + (248593027166771/10000000000000 : ℝ)*(sp6) + (488521075118353/50000000000000 : ℝ)*(sp7) + (4947942069/50000000000000 : ℝ)*(sp12) + (62713798073/100000000000000 : ℝ)*(sp13) + (61065334333133/6250000000000 : ℝ)*(f.failure) + (1242971997959289/50000000000000 : ℝ)*(f.sum) + (66652959223111/14362500000000000000000000000 : ℝ)*base65 + (310766201811366971/57450000000000000000000000000000 : ℝ)*base67 + (25513720058033029/57450000000000000000000000000000 : ℝ)*base70 + (113546907545766971/57450000000000000000000000000000 : ℝ)*base71 + (41474478881461/14362500000000000000000000000 : ℝ)*base73 + (153408162920783029/57450000000000000000000000000000 : ℝ)*base76 + (134333867202066971/57450000000000000000000000000000 : ℝ)*base77 + (268918968260166971/57450000000000000000000000000000 : ℝ)*base79 + (5829348878371/897656250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (762659/125000000000000000000 : ℝ)*base90 + (762659/125000000000000000000 : ℝ)*base92 + (762659/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (5841/10000 : ℝ) ≤ (4474407066161887345934647176989/7660000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67/6250000000 : ℝ)*(lower1) + (1753877/100000000000000 : ℝ)*(upper2) + (757167/10000000000000 : ℝ)*(lower3) + (1010457/6250000000000 : ℝ)*(lower5) + (361648893517549/20000000000000 : ℝ)*(major0) + (361648893517549/20000000000000 : ℝ)*(major1) + (904122233793873/50000000000000 : ℝ)*(major2) + (642560351268101/25000000000000 : ℝ)*(sp0) + (514048332258041/20000000000000 : ℝ)*(sp1) + (64256032016153/2500000000000 : ℝ)*(sp2) + (32086744725453/3125000000000 : ℝ)*(sp3) + (190322043/50000000000000 : ℝ)*(sp6) + (283854621/50000000000000 : ℝ)*(sp11) + (128108901/50000000000000 : ℝ)*(sp12) + (1026776398923737/100000000000000 : ℝ)*(f.failure) + (514048332258041/20000000000000 : ℝ)*(f.sum) + (57625370545579/28725000000000000000000000000 : ℝ)*base65 + (145026275013238337/15320000000000000000000000000000 : ℝ)*base68 + (167671640920194047/114900000000000000000000000000000 : ℝ)*base70 + (41942296333038337/15320000000000000000000000000000 : ℝ)*base72 + (25812474373537/3590625000000000000000000000 : ℝ)*base74 + (612445151902505953/114900000000000000000000000000000 : ℝ)*base75 + (8257396809774589/45960000000000000000000000000000 : ℝ)*base77 + (446097494851505411/45960000000000000000000000000000 : ℝ)*base80 + (12748941065141/2872500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (4620649/2000000000000000000000 : ℝ)*base89 + (4620649/2000000000000000000000 : ℝ)*base91 + (15379351/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (10103/12500 : ℝ) ≤ (7739143776096475407212636903/9575000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47721137/100000000000000 : ℝ)*(lower3) + (8404563/10000000000000 : ℝ)*(upper4) + (135847/2000000000000 : ℝ)*(lower5) + (1908361582398131/100000000000000 : ℝ)*(major0) + (1908361582398131/100000000000000 : ℝ)*(major1) + (1908361582398131/100000000000000 : ℝ)*(major2) + (412695911/12500000000000 : ℝ)*(sp0) + (9693706919/25000000000000 : ℝ)*(sp1) + (57515342397/100000000000000 : ℝ)*(sp2) + (5196136089/25000000000000 : ℝ)*(sp3) + (67653793046163/2500000000000 : ℝ)*(sp8) + (676529062146533/25000000000000 : ℝ)*(sp9) + (270609750807141/10000000000000 : ℝ)*(sp10) + (270901291971841/25000000000000 : ℝ)*(sp11) + (1083625952431719/100000000000000 : ℝ)*(f.failure) + (169134688963363/6250000000000 : ℝ)*(f.sum) + (26055394061561/14362500000000000000000000000 : ℝ)*base66 + (1144459388859593891/229800000000000000000000000000000 : ℝ)*base67 + (1393708207273206109/229800000000000000000000000000000 : ℝ)*base70 + (779235969831606109/229800000000000000000000000000000 : ℝ)*base72 + (45974713956889/14362500000000000000000000000 : ℝ)*base73 + (1756288404783606109/229800000000000000000000000000000 : ℝ)*base76 + (817132689393593891/229800000000000000000000000000000 : ℝ)*base77 + (843538130936393891/229800000000000000000000000000000 : ℝ)*base79 + (186863334128947/28725000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5655337/2000000000000000000000 : ℝ)*base90 + (5655337/2000000000000000000000 : ℝ)*base92 + (5655337/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-88027/100000 : ℝ) ≤ (-8428299257994472892076522010923/9575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1646531/6250000000000 : ℝ)*(upper1) + (36140389/100000000000000 : ℝ)*(lower2) + (2529713/4000000000000 : ℝ)*(upper3) + (2034267/12500000000000 : ℝ)*(upper5) + (487854796333881/25000000000000 : ℝ)*(major0) + (487854796333881/25000000000000 : ℝ)*(major1) + (487854796333881/25000000000000 : ℝ)*(major2) + (2182591133/100000000000000 : ℝ)*(sp4) + (3409448779/25000000000000 : ℝ)*(sp6) + (1936280963/25000000000000 : ℝ)*(sp7) + (176506384514563/6250000000000 : ℝ)*(sp12) + (141205216741207/5000000000000 : ℝ)*(sp13) + (88252834282157/3125000000000 : ℝ)*(sp14) + (55403381421791/5000000000000 : ℝ)*(sp15) + (138509421694959/12500000000000 : ℝ)*(f.failure) + (141205216741207/5000000000000 : ℝ)*(f.sum) + (3271667536951/2393750000000000000000000000 : ℝ)*base65 + (48408675106866547/19150000000000000000000000000000 : ℝ)*base67 + (46425515967266547/19150000000000000000000000000000 : ℝ)*base69 + (131215134169716547/19150000000000000000000000000000 : ℝ)*base71 + (1937875112537/1196875000000000000000000000 : ℝ)*base74 + (185963711154316547/19150000000000000000000000000000 : ℝ)*base75 + (203513824021316547/19150000000000000000000000000000 : ℝ)*base77 + (169486072436116547/19150000000000000000000000000000 : ℝ)*base79 + (11234367399763/1196875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2077857/250000000000000000000 : ℝ)*base90 + (2077857/250000000000000000000 : ℝ)*base92 + (2077857/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1630_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35221777/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3261/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (66/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16247/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(5841/10000 : ℝ) else (10103/12500 : ℝ) ≤ X j i ∧ X j i ≤ (88027/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1630_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1630_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35221777/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3261/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (66/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16247/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(5841/10000 : ℝ) else (10103/12500 : ℝ) ≤ X j i ∧ X j i ≤ (88027/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1630_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35221777/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3261/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (66/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16247/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(5841/10000 : ℝ) else (10103/12500 : ℝ) ≤ X j i ∧ X j i ≤ (88027/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1630_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
