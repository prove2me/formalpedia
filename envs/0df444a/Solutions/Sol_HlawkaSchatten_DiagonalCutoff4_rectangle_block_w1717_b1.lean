-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1717_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:55:22.557392+00:00
-- url     : https://prove2.me/submissions/256da209-59ac-4143-a97d-fabf5cdaa3a8

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
theorem support_rectangle_w1717_s3_0 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-43349459/312500000 : ℝ)*x 0 + (5465587883/10000000000 : ℝ)*x 1 + (642389437/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43349459/312500000 : ℝ)^5359 ≤ (8699437744387/100000000000000 : ℝ)^4335 := by
    have hnat : (43349459 : ℕ)^5359*100000000000000^4335 ≤ 8699437744387^4335*312500000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43349459 312500000 8699437744387 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5465587883/10000000000 : ℝ)^5359 ≤ (47387336090723/100000000000000 : ℝ)^4335 := by
    have hnat : (5465587883 : ℕ)^5359*100000000000000^4335 ≤ 47387336090723^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465587883 10000000000 47387336090723 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (642389437/1250000000 : ℝ)^5359 ≤ (10978306539639/25000000000000 : ℝ)^4335 := by
    have hnat : (642389437 : ℕ)^5359*25000000000000^4335 ≤ 10978306539639^4335*1250000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642389437 1250000000 10978306539639 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-43349459/312500000 : ℝ), (5465587883/10000000000 : ℝ), (642389437/1250000000 : ℝ)] ![(8699437744387/100000000000000 : ℝ), (47387336090723/100000000000000 : ℝ), (10978306539639/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-43349459/312500000 : ℝ)|^5359 ≤ (8699437744387/100000000000000 : ℝ)^4335
        have hw : |(-43349459/312500000 : ℝ)|=(43349459/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5465587883/10000000000 : ℝ)|^5359 ≤ (47387336090723/100000000000000 : ℝ)^4335
        have hw : |(5465587883/10000000000 : ℝ)|=(5465587883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(642389437/1250000000 : ℝ)|^5359 ≤ (10978306539639/25000000000000 : ℝ)^4335
        have hw : |(642389437/1250000000 : ℝ)|=(642389437/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s3_1 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5341161869/10000000000 : ℝ)*x 0 + (-389092651/2500000000 : ℝ)*x 1 + (1284779167/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5341161869/10000000000 : ℝ)^5359 ≤ (11514331368863/25000000000000 : ℝ)^4335 := by
    have hnat : (5341161869 : ℕ)^5359*25000000000000^4335 ≤ 11514331368863^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5341161869 10000000000 11514331368863 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (389092651/2500000000 : ℝ)^5359 ≤ (501471798511/5000000000000 : ℝ)^4335 := by
    have hnat : (389092651 : ℕ)^5359*5000000000000^4335 ≤ 501471798511^4335*2500000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389092651 2500000000 501471798511 5000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1284779167/2500000000 : ℝ)^5359 ≤ (21956619269401/50000000000000 : ℝ)^4335 := by
    have hnat : (1284779167 : ℕ)^5359*50000000000000^4335 ≤ 21956619269401^4335*2500000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284779167 2500000000 21956619269401 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5341161869/10000000000 : ℝ), (-389092651/2500000000 : ℝ), (1284779167/2500000000 : ℝ)] ![(11514331368863/25000000000000 : ℝ), (501471798511/5000000000000 : ℝ), (21956619269401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5341161869/10000000000 : ℝ)|^5359 ≤ (11514331368863/25000000000000 : ℝ)^4335
        have hw : |(5341161869/10000000000 : ℝ)|=(5341161869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-389092651/2500000000 : ℝ)|^5359 ≤ (501471798511/5000000000000 : ℝ)^4335
        have hw : |(-389092651/2500000000 : ℝ)|=(389092651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1284779167/2500000000 : ℝ)|^5359 ≤ (21956619269401/50000000000000 : ℝ)^4335
        have hw : |(1284779167/2500000000 : ℝ)|=(1284779167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s3_2 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5341162657/10000000000 : ℝ)*x 0 + (642389489/1250000000 : ℝ)*x 1 + (-1556370551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5341162657/10000000000 : ℝ)^5359 ≤ (46057333875541/100000000000000 : ℝ)^4335 := by
    have hnat : (5341162657 : ℕ)^5359*100000000000000^4335 ≤ 46057333875541^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5341162657 10000000000 46057333875541 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (642389489/1250000000 : ℝ)^5359 ≤ (4391323055291/10000000000000 : ℝ)^4335 := by
    have hnat : (642389489 : ℕ)^5359*10000000000000^4335 ≤ 4391323055291^4335*1250000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642389489 1250000000 4391323055291 10000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1556370551/10000000000 : ℝ)^5359 ≤ (2005887109601/20000000000000 : ℝ)^4335 := by
    have hnat : (1556370551 : ℕ)^5359*20000000000000^4335 ≤ 2005887109601^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1556370551 10000000000 2005887109601 20000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5341162657/10000000000 : ℝ), (642389489/1250000000 : ℝ), (-1556370551/10000000000 : ℝ)] ![(46057333875541/100000000000000 : ℝ), (4391323055291/10000000000000 : ℝ), (2005887109601/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5341162657/10000000000 : ℝ)|^5359 ≤ (46057333875541/100000000000000 : ℝ)^4335
        have hw : |(5341162657/10000000000 : ℝ)|=(5341162657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(642389489/1250000000 : ℝ)|^5359 ≤ (4391323055291/10000000000000 : ℝ)^4335
        have hw : |(642389489/1250000000 : ℝ)|=(642389489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1556370551/10000000000 : ℝ)|^5359 ≤ (2005887109601/20000000000000 : ℝ)^4335
        have hw : |(-1556370551/10000000000 : ℝ)|=(1556370551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s3_3 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (409582247/1000000000 : ℝ)*x 0 + (1816264759/5000000000 : ℝ)*x 1 + (4594176747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (409582247/1000000000 : ℝ)^5359 ≤ (8292960148709/25000000000000 : ℝ)^4335 := by
    have hnat : (409582247 : ℕ)^5359*25000000000000^4335 ≤ 8292960148709^4335*1000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409582247 1000000000 8292960148709 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1816264759/5000000000 : ℝ)^5359 ≤ (28597175975247/100000000000000 : ℝ)^4335 := by
    have hnat : (1816264759 : ℕ)^5359*100000000000000^4335 ≤ 28597175975247^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1816264759 5000000000 28597175975247 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4594176747/10000000000 : ℝ)^5359 ≤ (4778872927977/12500000000000 : ℝ)^4335 := by
    have hnat : (4594176747 : ℕ)^5359*12500000000000^4335 ≤ 4778872927977^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4594176747 10000000000 4778872927977 12500000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(409582247/1000000000 : ℝ), (1816264759/5000000000 : ℝ), (4594176747/10000000000 : ℝ)] ![(8292960148709/25000000000000 : ℝ), (28597175975247/100000000000000 : ℝ), (4778872927977/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(409582247/1000000000 : ℝ)|^5359 ≤ (8292960148709/25000000000000 : ℝ)^4335
        have hw : |(409582247/1000000000 : ℝ)|=(409582247/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1816264759/5000000000 : ℝ)|^5359 ≤ (28597175975247/100000000000000 : ℝ)^4335
        have hw : |(1816264759/5000000000 : ℝ)|=(1816264759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4594176747/10000000000 : ℝ)|^5359 ≤ (4778872927977/12500000000000 : ℝ)^4335
        have hw : |(4594176747/10000000000 : ℝ)|=(4594176747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s3_4 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-693664583/5000000000 : ℝ)*x 0 + (2571376589/5000000000 : ℝ)*x 1 + (1092379239/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (693664583/5000000000 : ℝ)^5359 ≤ (174011467129/2000000000000 : ℝ)^4335 := by
    have hnat : (693664583 : ℕ)^5359*2000000000000^4335 ≤ 174011467129^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693664583 5000000000 174011467129 2000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2571376589/5000000000 : ℝ)^5359 ≤ (43951655474379/100000000000000 : ℝ)^4335 := by
    have hnat : (2571376589 : ℕ)^5359*100000000000000^4335 ≤ 43951655474379^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2571376589 5000000000 43951655474379 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092379239/2000000000 : ℝ)^5359 ≤ (47347771160411/100000000000000 : ℝ)^4335 := by
    have hnat : (1092379239 : ℕ)^5359*100000000000000^4335 ≤ 47347771160411^4335*2000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092379239 2000000000 47347771160411 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-693664583/5000000000 : ℝ), (2571376589/5000000000 : ℝ), (1092379239/2000000000 : ℝ)] ![(174011467129/2000000000000 : ℝ), (43951655474379/100000000000000 : ℝ), (47347771160411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-693664583/5000000000 : ℝ)|^5359 ≤ (174011467129/2000000000000 : ℝ)^4335
        have hw : |(-693664583/5000000000 : ℝ)|=(693664583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2571376589/5000000000 : ℝ)|^5359 ≤ (43951655474379/100000000000000 : ℝ)^4335
        have hw : |(2571376589/5000000000 : ℝ)|=(2571376589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092379239/2000000000 : ℝ)|^5359 ≤ (47347771160411/100000000000000 : ℝ)^4335
        have hw : |(1092379239/2000000000 : ℝ)|=(1092379239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s3_5 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (656721037/1250000000 : ℝ)*x 0 + (-246717901/2000000000 : ℝ)*x 1 + (1092379239/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656721037/1250000000 : ℝ)^5359 ≤ (11281879249577/25000000000000 : ℝ)^4335 := by
    have hnat : (656721037 : ℕ)^5359*25000000000000^4335 ≤ 11281879249577^4335*1250000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656721037 1250000000 11281879249577 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (246717901/2000000000 : ℝ)^5359 ≤ (7524711832319/100000000000000 : ℝ)^4335 := by
    have hnat : (246717901 : ℕ)^5359*100000000000000^4335 ≤ 7524711832319^4335*2000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246717901 2000000000 7524711832319 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092379239/2000000000 : ℝ)^5359 ≤ (47347771160411/100000000000000 : ℝ)^4335 := by
    have hnat : (1092379239 : ℕ)^5359*100000000000000^4335 ≤ 47347771160411^4335*2000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092379239 2000000000 47347771160411 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656721037/1250000000 : ℝ), (-246717901/2000000000 : ℝ), (1092379239/2000000000 : ℝ)] ![(11281879249577/25000000000000 : ℝ), (7524711832319/100000000000000 : ℝ), (47347771160411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656721037/1250000000 : ℝ)|^5359 ≤ (11281879249577/25000000000000 : ℝ)^4335
        have hw : |(656721037/1250000000 : ℝ)|=(656721037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-246717901/2000000000 : ℝ)|^5359 ≤ (7524711832319/100000000000000 : ℝ)^4335
        have hw : |(-246717901/2000000000 : ℝ)|=(246717901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092379239/2000000000 : ℝ)|^5359 ≤ (47347771160411/100000000000000 : ℝ)^4335
        have hw : |(1092379239/2000000000 : ℝ)|=(1092379239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s3_6 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (656721037/1250000000 : ℝ)*x 0 + (1092379239/2000000000 : ℝ)*x 1 + (-246717901/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656721037/1250000000 : ℝ)^5359 ≤ (11281879249577/25000000000000 : ℝ)^4335 := by
    have hnat : (656721037 : ℕ)^5359*25000000000000^4335 ≤ 11281879249577^4335*1250000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656721037 1250000000 11281879249577 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092379239/2000000000 : ℝ)^5359 ≤ (47347771160411/100000000000000 : ℝ)^4335 := by
    have hnat : (1092379239 : ℕ)^5359*100000000000000^4335 ≤ 47347771160411^4335*2000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092379239 2000000000 47347771160411 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (246717901/2000000000 : ℝ)^5359 ≤ (7524711832319/100000000000000 : ℝ)^4335 := by
    have hnat : (246717901 : ℕ)^5359*100000000000000^4335 ≤ 7524711832319^4335*2000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246717901 2000000000 7524711832319 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656721037/1250000000 : ℝ), (1092379239/2000000000 : ℝ), (-246717901/2000000000 : ℝ)] ![(11281879249577/25000000000000 : ℝ), (47347771160411/100000000000000 : ℝ), (7524711832319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656721037/1250000000 : ℝ)|^5359 ≤ (11281879249577/25000000000000 : ℝ)^4335
        have hw : |(656721037/1250000000 : ℝ)|=(656721037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1092379239/2000000000 : ℝ)|^5359 ≤ (47347771160411/100000000000000 : ℝ)^4335
        have hw : |(1092379239/2000000000 : ℝ)|=(1092379239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-246717901/2000000000 : ℝ)|^5359 ≤ (7524711832319/100000000000000 : ℝ)^4335
        have hw : |(-246717901/2000000000 : ℝ)|=(246717901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s3_7 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (409625477/1000000000 : ℝ)*x 0 + (1145865537/2500000000 : ℝ)*x 1 + (910850909/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (409625477/1000000000 : ℝ)^5359 ≤ (33176168858911/100000000000000 : ℝ)^4335 := by
    have hnat : (409625477 : ℕ)^5359*100000000000000^4335 ≤ 33176168858911^4335*1000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409625477 1000000000 33176168858911 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1145865537/2500000000 : ℝ)^5359 ≤ (38120789250357/100000000000000 : ℝ)^4335 := by
    have hnat : (1145865537 : ℕ)^5359*100000000000000^4335 ≤ 38120789250357^4335*2500000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145865537 2500000000 38120789250357 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (910850909/2500000000 : ℝ)^5359 ≤ (2870304187637/10000000000000 : ℝ)^4335 := by
    have hnat : (910850909 : ℕ)^5359*10000000000000^4335 ≤ 2870304187637^4335*2500000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910850909 2500000000 2870304187637 10000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(409625477/1000000000 : ℝ), (1145865537/2500000000 : ℝ), (910850909/2500000000 : ℝ)] ![(33176168858911/100000000000000 : ℝ), (38120789250357/100000000000000 : ℝ), (2870304187637/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(409625477/1000000000 : ℝ)|^5359 ≤ (33176168858911/100000000000000 : ℝ)^4335
        have hw : |(409625477/1000000000 : ℝ)|=(409625477/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1145865537/2500000000 : ℝ)|^5359 ≤ (38120789250357/100000000000000 : ℝ)^4335
        have hw : |(1145865537/2500000000 : ℝ)|=(1145865537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(910850909/2500000000 : ℝ)|^5359 ≤ (2870304187637/10000000000000 : ℝ)^4335
        have hw : |(910850909/2500000000 : ℝ)|=(910850909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1717_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39455713/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10057/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (629/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17043/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10057/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10057/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10057/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10057/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10057/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10057/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10057/100000 : ℝ) ^ (5351/1024 : ℝ) ≤ (612792104176327/100000000000000000000 : ℝ) := by
    have hpowers : (10057/100000 : ℝ)^5351 ≤ (612792104176327/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10057 : ℕ)^5351*100000000000000000000^1024 ≤ 612792104176327^1024*100000^5351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10057 100000 612792104176327 100000000000000000000 5351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10057/100000 : ℝ)) (X := (612792104176327/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17051/100000 : ℝ) ^ (5351/1024 : ℝ) ≤ (9670364469646071/100000000000000000000 : ℝ) := by
    have hpowers : (17051/100000 : ℝ)^5351 ≤ (9670364469646071/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17051 : ℕ)^5351*100000000000000000000^1024 ≤ 9670364469646071^1024*100000^5351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17051 100000 9670364469646071 100000000000000000000 5351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17051/100000 : ℝ)) (X := (9670364469646071/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000612792104176327/50000000000000000000 : ℝ) ≤ (1250002931676347/1250000000000000 : ℝ) ^ (5351/1024 : ℝ) := by
    have hpowers : (50000612792104176327/50000000000000000000 : ℝ)^1024 ≤ (1250002931676347/1250000000000000 : ℝ)^5351 := by
      have hnat : (50000612792104176327 : ℕ)^1024*1250000000000000^5351 ≤ 1250002931676347^5351*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000612792104176327 50000000000000000000 1250002931676347 1250000000000000 1024 5351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250002931676347/1250000000000000 : ℝ)) (X := (50000612792104176327/50000000000000000000 : ℝ)) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50005141578286911199/50000000000000000000 : ℝ) ≤ (2500049194143897/2500000000000000 : ℝ) ^ (5351/1024 : ℝ) := by
    have hpowers : (50005141578286911199/50000000000000000000 : ℝ)^1024 ≤ (2500049194143897/2500000000000000 : ℝ)^5351 := by
      have hnat : (50005141578286911199 : ℕ)^1024*2500000000000000^5351 ≤ 2500049194143897^5351*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005141578286911199 50000000000000000000 2500049194143897 2500000000000000 1024 5351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500049194143897/2500000000000000 : ℝ)) (X := (50005141578286911199/50000000000000000000 : ℝ)) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50009670364469646071/50000000000000000000 : ℝ) ≤ (25000925249351/25000000000000 : ℝ) ^ (5351/1024 : ℝ) := by
    have hpowers : (50009670364469646071/50000000000000000000 : ℝ)^1024 ≤ (25000925249351/25000000000000 : ℝ)^5351 := by
      have hnat : (50009670364469646071 : ℕ)^1024*25000000000000^5351 ≤ 25000925249351^5351*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009670364469646071 50000000000000000000 25000925249351 25000000000000 1024 5351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (25000925249351/25000000000000 : ℝ)) (X := (50009670364469646071/50000000000000000000 : ℝ)) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(612792104176327/100000000000000000000 : ℝ) ≤ ((8742084726377242347/8742500000000000000 : ℝ)+2*(43330791203/174850000000000 : ℝ)*(10057/100000 : ℝ))^(5351/1024 : ℝ) := by
    rw [show (8742084726377242347/8742500000000000000 : ℝ)+2*(43330791203/174850000000000 : ℝ)*(10057/100000 : ℝ)=(1250002931676347/1250000000000000 : ℝ) by norm_num, show 1+2*(612792104176327/100000000000000000000 : ℝ)=(50000612792104176327/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9670364469646071/100000000000000000000 : ℝ)+(612792104176327/100000000000000000000 : ℝ) ≤ ((8742084726377242347/8742500000000000000 : ℝ)+(43330791203/174850000000000 : ℝ)*((17051/100000 : ℝ)+(10057/100000 : ℝ)))^(5351/1024 : ℝ) := by
    rw [show (8742084726377242347/8742500000000000000 : ℝ)+(43330791203/174850000000000 : ℝ)*((17051/100000 : ℝ)+(10057/100000 : ℝ))=(2500049194143897/2500000000000000 : ℝ) by norm_num, show 1+(9670364469646071/100000000000000000000 : ℝ)+(612792104176327/100000000000000000000 : ℝ)=(50005141578286911199/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9670364469646071/100000000000000000000 : ℝ) ≤ ((8742084726377242347/8742500000000000000 : ℝ)+2*(43330791203/174850000000000 : ℝ)*(17051/100000 : ℝ))^(5351/1024 : ℝ) := by
    rw [show (8742084726377242347/8742500000000000000 : ℝ)+2*(43330791203/174850000000000 : ℝ)*(17051/100000 : ℝ)=(25000925249351/25000000000000 : ℝ) by norm_num, show 1+2*(9670364469646071/100000000000000000000 : ℝ)=(50009670364469646071/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8742084726377242347/8742500000000000000 : ℝ)*(X 1 0+X 2 0)+(43330791203/174850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5351/1024 : ℝ)) (lo := (10057/100000 : ℝ)) (hi := (17051/100000 : ℝ)) (c := (8742084726377242347/8742500000000000000 : ℝ)) (alpha := (43330791203/174850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8742084726377242347/8742500000000000000 : ℝ)*(X 0 1+X 2 1)+(43330791203/174850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5351/1024 : ℝ)) (lo := (10057/100000 : ℝ)) (hi := (17051/100000 : ℝ)) (c := (8742084726377242347/8742500000000000000 : ℝ)) (alpha := (43330791203/174850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8742084726377242347/8742500000000000000 : ℝ)*(X 0 2+X 1 2)+(43330791203/174850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5351/1024 : ℝ)) (lo := (10057/100000 : ℝ)) (hi := (17051/100000 : ℝ)) (c := (8742084726377242347/8742500000000000000 : ℝ)) (alpha := (43330791203/174850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-43349459/312500000 : ℝ)*X 0 0+(5465587883/10000000000 : ℝ)*X 0 1+(642389437/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5341161869/10000000000 : ℝ)*X 1 0+(-389092651/2500000000 : ℝ)*X 1 1+(1284779167/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5341162657/10000000000 : ℝ)*X 2 0+(642389489/1250000000 : ℝ)*X 2 1+(-1556370551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((409582247/1000000000 : ℝ)*X 0 0+(1816264759/5000000000 : ℝ)*X 0 1+(4594176747/10000000000 : ℝ)*X 0 2+(409582247/1000000000 : ℝ)*X 1 0+(1816264759/5000000000 : ℝ)*X 1 1+(4594176747/10000000000 : ℝ)*X 1 2+(409582247/1000000000 : ℝ)*X 2 0+(1816264759/5000000000 : ℝ)*X 2 1+(4594176747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-693664583/5000000000 : ℝ)*X 0 0+(2571376589/5000000000 : ℝ)*X 0 1+(1092379239/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((656721037/1250000000 : ℝ)*X 1 0+(-246717901/2000000000 : ℝ)*X 1 1+(1092379239/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((656721037/1250000000 : ℝ)*X 2 0+(1092379239/2000000000 : ℝ)*X 2 1+(-246717901/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((409625477/1000000000 : ℝ)*X 0 0+(1145865537/2500000000 : ℝ)*X 0 1+(910850909/2500000000 : ℝ)*X 0 2+(409625477/1000000000 : ℝ)*X 1 0+(1145865537/2500000000 : ℝ)*X 1 1+(910850909/2500000000 : ℝ)*X 1 2+(409625477/1000000000 : ℝ)*X 2 0+(1145865537/2500000000 : ℝ)*X 2 1+(910850909/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6883940613488145851810210313/437125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1065017393/100000000000000 : ℝ)*(base19) + (298029819/20000000000000 : ℝ)*(base23) + (164320329/50000000000000 : ℝ)*(upper3) + (1430061/10000000000000 : ℝ)*(upper4) + (400880243/100000000000000 : ℝ)*(upper5) + (2051484873575593/100000000000000 : ℝ)*(major0) + (2051484873575593/100000000000000 : ℝ)*(major1) + (2051484873575593/100000000000000 : ℝ)*(major2) + (191441238014237/6250000000000 : ℝ)*(sp0) + (3063075722059289/100000000000000 : ℝ)*(sp1) + (3063075296927587/100000000000000 : ℝ)*(sp2) + (1039887292217173/100000000000000 : ℝ)*(sp3) + (1697884889/10000000000000 : ℝ)*(sp4) + (2571458333/50000000000000 : ℝ)*(sp7) + (1039892435133839/100000000000000 : ℝ)*(f.failure) + (1531538393538341/50000000000000 : ℝ)*(f.sum) + (1254800490521/2185625000000000000000000000 : ℝ)*base65 + (2312887611392313229/874250000000000000000000000000000 : ℝ)*base68 + (5158505137829063229/874250000000000000000000000000000 : ℝ)*base70 + (233429199767563229/874250000000000000000000000000000 : ℝ)*base72 + (18874322919713/4371250000000000000000000000 : ℝ)*base74 + (1178998406076563229/874250000000000000000000000000000 : ℝ)*base76 + (1555751822620936771/874250000000000000000000000000000 : ℝ)*base77 + (1555539609798686771/874250000000000000000000000000000 : ℝ)*base79 + (7964484398077/4371250000000000000000000000 : ℝ)*base81 + (8172207/2000000000000000000000 : ℝ)*base89 + (8172207/2000000000000000000000 : ℝ)*base91 + (8172207/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5487467863735782080310822801/437125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1709899241/100000000000000 : ℝ)*(base19) + (1839811273/100000000000000 : ℝ)*(base23) + (508661783/100000000000000 : ℝ)*(lower1) + (1069233/400000000000 : ℝ)*(upper3) + (14542153/25000000000000 : ℝ)*(lower4) + (130424387/50000000000000 : ℝ)*(upper5) + (2098566524146361/100000000000000 : ℝ)*(major0) + (2098566524146361/100000000000000 : ℝ)*(major1) + (2098566524146361/100000000000000 : ℝ)*(major2) + (576934241/50000000000000 : ℝ)*(sp2) + (626674925291677/20000000000000 : ℝ)*(sp4) + (391671614569893/12500000000000 : ℝ)*(sp5) + (313337163277863/10000000000000 : ℝ)*(sp6) + (531879001691431/50000000000000 : ℝ)*(sp7) + (531879001691431/50000000000000 : ℝ)*(f.failure) + (626674925291677/20000000000000 : ℝ)*(f.sum) + (2318431778813/546406250000000000000000000 : ℝ)*base65 + (19177029559411200733/874250000000000000000000000000000 : ℝ)*base68 + (303568615635450733/874250000000000000000000000000000 : ℝ)*base70 + (2919162498782299267/874250000000000000000000000000000 : ℝ)*base71 + (62313690048797/8742500000000000000000000000 : ℝ)*base74 + (68107619913993299267/874250000000000000000000000000000 : ℝ)*base75 + (290989545570200733/874250000000000000000000000000000 : ℝ)*base78 + (1982543624733200733/874250000000000000000000000000000 : ℝ)*base80 + (29797196896033/8742500000000000000000000000 : ℝ)*base81 + (6095303/1000000000000000000000 : ℝ)*base89 + (6095303/1000000000000000000000 : ℝ)*base91 + (6095303/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1717_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39455713/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10057/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (629/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17043/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1717_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1717_s4_0 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-21674777/156250000 : ℝ)*x 0 + (5465576023/10000000000 : ℝ)*x 1 + (2569562649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21674777/156250000 : ℝ)^5359 ≤ (8699461312557/100000000000000 : ℝ)^4335 := by
    have hnat : (21674777 : ℕ)^5359*100000000000000^4335 ≤ 8699461312557^4335*156250000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21674777 156250000 8699461312557 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5465576023/10000000000 : ℝ)^5359 ≤ (47387208973427/100000000000000 : ℝ)^4335 := by
    have hnat : (5465576023 : ℕ)^5359*100000000000000^4335 ≤ 47387208973427^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465576023 10000000000 47387208973427 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2569562649/5000000000 : ℝ)^5359 ≤ (1756533188021/4000000000000 : ℝ)^4335 := by
    have hnat : (2569562649 : ℕ)^5359*4000000000000^4335 ≤ 1756533188021^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569562649 5000000000 1756533188021 4000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21674777/156250000 : ℝ), (5465576023/10000000000 : ℝ), (2569562649/5000000000 : ℝ)] ![(8699461312557/100000000000000 : ℝ), (47387208973427/100000000000000 : ℝ), (1756533188021/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21674777/156250000 : ℝ)|^5359 ≤ (8699461312557/100000000000000 : ℝ)^4335
        have hw : |(-21674777/156250000 : ℝ)|=(21674777/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5465576023/10000000000 : ℝ)|^5359 ≤ (47387208973427/100000000000000 : ℝ)^4335
        have hw : |(5465576023/10000000000 : ℝ)|=(5465576023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2569562649/5000000000 : ℝ)|^5359 ≤ (1756533188021/4000000000000 : ℝ)^4335
        have hw : |(2569562649/5000000000 : ℝ)|=(2569562649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s4_1 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534115953/1000000000 : ℝ)*x 0 + (-311272047/2000000000 : ℝ)*x 1 + (80298857/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534115953/1000000000 : ℝ)^5359 ≤ (46057300541689/100000000000000 : ℝ)^4335 := by
    have hnat : (534115953 : ℕ)^5359*100000000000000^4335 ≤ 46057300541689^4335*1000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534115953 1000000000 46057300541689 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (311272047/2000000000 : ℝ)^5359 ≤ (10029353367437/100000000000000 : ℝ)^4335 := by
    have hnat : (311272047 : ℕ)^5359*100000000000000^4335 ≤ 10029353367437^4335*2000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311272047 2000000000 10029353367437 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80298857/156250000 : ℝ)^5359 ≤ (10978336518431/25000000000000 : ℝ)^4335 := by
    have hnat : (80298857 : ℕ)^5359*25000000000000^4335 ≤ 10978336518431^4335*156250000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80298857 156250000 10978336518431 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534115953/1000000000 : ℝ), (-311272047/2000000000 : ℝ), (80298857/156250000 : ℝ)] ![(46057300541689/100000000000000 : ℝ), (10029353367437/100000000000000 : ℝ), (10978336518431/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534115953/1000000000 : ℝ)|^5359 ≤ (46057300541689/100000000000000 : ℝ)^4335
        have hw : |(534115953/1000000000 : ℝ)|=(534115953/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-311272047/2000000000 : ℝ)|^5359 ≤ (10029353367437/100000000000000 : ℝ)^4335
        have hw : |(-311272047/2000000000 : ℝ)|=(311272047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(80298857/156250000 : ℝ)|^5359 ≤ (10978336518431/25000000000000 : ℝ)^4335
        have hw : |(80298857/156250000 : ℝ)|=(80298857/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s4_2 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5341160163/10000000000 : ℝ)*x 0 + (2569562843/5000000000 : ℝ)*x 1 + (-1556360929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5341160163/10000000000 : ℝ)^5359 ≤ (1842292291579/4000000000000 : ℝ)^4335 := by
    have hnat : (5341160163 : ℕ)^5359*4000000000000^4335 ≤ 1842292291579^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5341160163 10000000000 1842292291579 4000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2569562843/5000000000 : ℝ)^5359 ≤ (21956666899553/50000000000000 : ℝ)^4335 := by
    have hnat : (2569562843 : ℕ)^5359*50000000000000^4335 ≤ 21956666899553^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569562843 5000000000 21956666899553 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1556360929/10000000000 : ℝ)^5359 ≤ (501467944803/5000000000000 : ℝ)^4335 := by
    have hnat : (1556360929 : ℕ)^5359*5000000000000^4335 ≤ 501467944803^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1556360929 10000000000 501467944803 5000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5341160163/10000000000 : ℝ), (2569562843/5000000000 : ℝ), (-1556360929/10000000000 : ℝ)] ![(1842292291579/4000000000000 : ℝ), (21956666899553/50000000000000 : ℝ), (501467944803/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5341160163/10000000000 : ℝ)|^5359 ≤ (1842292291579/4000000000000 : ℝ)^4335
        have hw : |(5341160163/10000000000 : ℝ)|=(5341160163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2569562843/5000000000 : ℝ)|^5359 ≤ (21956666899553/50000000000000 : ℝ)^4335
        have hw : |(2569562843/5000000000 : ℝ)|=(2569562843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1556360929/10000000000 : ℝ)|^5359 ≤ (501467944803/5000000000000 : ℝ)^4335
        have hw : |(-1556360929/10000000000 : ℝ)|=(1556360929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s4_3 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4095824543/10000000000 : ℝ)*x 0 + (3632561377/10000000000 : ℝ)*x 1 + (4594144589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4095824543/10000000000 : ℝ)^5359 ≤ (33171861349821/100000000000000 : ℝ)^4335 := by
    have hnat : (4095824543 : ℕ)^5359*100000000000000^4335 ≤ 33171861349821^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4095824543 10000000000 33171861349821 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3632561377/10000000000 : ℝ)^5359 ≤ (28597486032033/100000000000000 : ℝ)^4335 := by
    have hnat : (3632561377 : ℕ)^5359*100000000000000^4335 ≤ 28597486032033^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3632561377 10000000000 28597486032033 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4594144589/10000000000 : ℝ)^5359 ≤ (38230652604319/100000000000000 : ℝ)^4335 := by
    have hnat : (4594144589 : ℕ)^5359*100000000000000^4335 ≤ 38230652604319^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4594144589 10000000000 38230652604319 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4095824543/10000000000 : ℝ), (3632561377/10000000000 : ℝ), (4594144589/10000000000 : ℝ)] ![(33171861349821/100000000000000 : ℝ), (28597486032033/100000000000000 : ℝ), (38230652604319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4095824543/10000000000 : ℝ)|^5359 ≤ (33171861349821/100000000000000 : ℝ)^4335
        have hw : |(4095824543/10000000000 : ℝ)|=(4095824543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3632561377/10000000000 : ℝ)|^5359 ≤ (28597486032033/100000000000000 : ℝ)^4335
        have hw : |(3632561377/10000000000 : ℝ)|=(3632561377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4594144589/10000000000 : ℝ)|^5359 ≤ (38230652604319/100000000000000 : ℝ)^4335
        have hw : |(4594144589/10000000000 : ℝ)|=(4594144589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s4_4 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1387332703/10000000000 : ℝ)*x 0 + (5142762393/10000000000 : ℝ)*x 1 + (5461884551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1387332703/10000000000 : ℝ)^5359 ≤ (1087575097299/12500000000000 : ℝ)^4335 := by
    have hnat : (1387332703 : ℕ)^5359*12500000000000^4335 ≤ 1087575097299^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1387332703 10000000000 1087575097299 12500000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5142762393/10000000000 : ℝ)^5359 ≤ (43951752831931/100000000000000 : ℝ)^4335 := by
    have hnat : (5142762393 : ℕ)^5359*100000000000000^4335 ≤ 43951752831931^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5142762393 10000000000 43951752831931 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5461884551/10000000000 : ℝ)^5359 ≤ (5918455797269/12500000000000 : ℝ)^4335 := by
    have hnat : (5461884551 : ℕ)^5359*12500000000000^4335 ≤ 5918455797269^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461884551 10000000000 5918455797269 12500000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1387332703/10000000000 : ℝ), (5142762393/10000000000 : ℝ), (5461884551/10000000000 : ℝ)] ![(1087575097299/12500000000000 : ℝ), (43951752831931/100000000000000 : ℝ), (5918455797269/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1387332703/10000000000 : ℝ)|^5359 ≤ (1087575097299/12500000000000 : ℝ)^4335
        have hw : |(-1387332703/10000000000 : ℝ)|=(1387332703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5142762393/10000000000 : ℝ)|^5359 ≤ (43951752831931/100000000000000 : ℝ)^4335
        have hw : |(5142762393/10000000000 : ℝ)|=(5142762393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5461884551/10000000000 : ℝ)|^5359 ≤ (5918455797269/12500000000000 : ℝ)^4335
        have hw : |(5461884551/10000000000 : ℝ)|=(5461884551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s4_5 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210150873/400000000 : ℝ)*x 0 + (-616800831/5000000000 : ℝ)*x 1 + (5461884143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210150873/400000000 : ℝ)^5359 ≤ (45127554471171/100000000000000 : ℝ)^4335 := by
    have hnat : (210150873 : ℕ)^5359*100000000000000^4335 ≤ 45127554471171^4335*400000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210150873 400000000 45127554471171 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (616800831/5000000000 : ℝ)^5359 ≤ (376240175259/5000000000000 : ℝ)^4335 := by
    have hnat : (616800831 : ℕ)^5359*5000000000000^4335 ≤ 376240175259^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      616800831 5000000000 376240175259 5000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5461884143/10000000000 : ℝ)^5359 ≤ (9469528401169/20000000000000 : ℝ)^4335 := by
    have hnat : (5461884143 : ℕ)^5359*20000000000000^4335 ≤ 9469528401169^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461884143 10000000000 9469528401169 20000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210150873/400000000 : ℝ), (-616800831/5000000000 : ℝ), (5461884143/10000000000 : ℝ)] ![(45127554471171/100000000000000 : ℝ), (376240175259/5000000000000 : ℝ), (9469528401169/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210150873/400000000 : ℝ)|^5359 ≤ (45127554471171/100000000000000 : ℝ)^4335
        have hw : |(210150873/400000000 : ℝ)|=(210150873/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-616800831/5000000000 : ℝ)|^5359 ≤ (376240175259/5000000000000 : ℝ)^4335
        have hw : |(-616800831/5000000000 : ℝ)|=(616800831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5461884143/10000000000 : ℝ)|^5359 ≤ (9469528401169/20000000000000 : ℝ)^4335
        have hw : |(5461884143/10000000000 : ℝ)|=(5461884143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s4_6 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5253772377/10000000000 : ℝ)*x 0 + (2730941309/5000000000 : ℝ)*x 1 + (-1233603053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5253772377/10000000000 : ℝ)^5359 ≤ (45127560332611/100000000000000 : ℝ)^4335 := by
    have hnat : (5253772377 : ℕ)^5359*100000000000000^4335 ≤ 45127560332611^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253772377 10000000000 45127560332611 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2730941309/5000000000 : ℝ)^5359 ≤ (1893905026531/4000000000000 : ℝ)^4335 := by
    have hnat : (2730941309 : ℕ)^5359*4000000000000^4335 ≤ 1893905026531^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730941309 5000000000 1893905026531 4000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1233603053/10000000000 : ℝ)^5359 ≤ (1881203498593/25000000000000 : ℝ)^4335 := by
    have hnat : (1233603053 : ℕ)^5359*25000000000000^4335 ≤ 1881203498593^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1233603053 10000000000 1881203498593 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5253772377/10000000000 : ℝ), (2730941309/5000000000 : ℝ), (-1233603053/10000000000 : ℝ)] ![(45127560332611/100000000000000 : ℝ), (1893905026531/4000000000000 : ℝ), (1881203498593/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5253772377/10000000000 : ℝ)|^5359 ≤ (45127560332611/100000000000000 : ℝ)^4335
        have hw : |(5253772377/10000000000 : ℝ)|=(5253772377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2730941309/5000000000 : ℝ)|^5359 ≤ (1893905026531/4000000000000 : ℝ)^4335
        have hw : |(2730941309/5000000000 : ℝ)|=(2730941309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1233603053/10000000000 : ℝ)|^5359 ≤ (1881203498593/25000000000000 : ℝ)^4335
        have hw : |(-1233603053/10000000000 : ℝ)|=(1233603053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_s4_7 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4096257767/10000000000 : ℝ)*x 0 + (4476006/9765625 : ℝ)*x 1 + (1821717171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4096257767/10000000000 : ℝ)^5359 ≤ (33176198865781/100000000000000 : ℝ)^4335 := by
    have hnat : (4096257767 : ℕ)^5359*100000000000000^4335 ≤ 33176198865781^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4096257767 10000000000 33176198865781 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4476006/9765625 : ℝ)^5359 ≤ (7624092039329/20000000000000 : ℝ)^4335 := by
    have hnat : (4476006 : ℕ)^5359*20000000000000^4335 ≤ 7624092039329^4335*9765625^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476006 9765625 7624092039329 20000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1821717171/5000000000 : ℝ)^5359 ≤ (28703340923039/100000000000000 : ℝ)^4335 := by
    have hnat : (1821717171 : ℕ)^5359*100000000000000^4335 ≤ 28703340923039^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1821717171 5000000000 28703340923039 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4096257767/10000000000 : ℝ), (4476006/9765625 : ℝ), (1821717171/5000000000 : ℝ)] ![(33176198865781/100000000000000 : ℝ), (7624092039329/20000000000000 : ℝ), (28703340923039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4096257767/10000000000 : ℝ)|^5359 ≤ (33176198865781/100000000000000 : ℝ)^4335
        have hw : |(4096257767/10000000000 : ℝ)|=(4096257767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4476006/9765625 : ℝ)|^5359 ≤ (7624092039329/20000000000000 : ℝ)^4335
        have hw : |(4476006/9765625 : ℝ)|=(4476006/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1821717171/5000000000 : ℝ)|^5359 ≤ (28703340923039/100000000000000 : ℝ)^4335
        have hw : |(1821717171/5000000000 : ℝ)|=(1821717171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1717_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39455713/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (629/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (2013/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8521/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17043/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (629/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17043/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (629/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17043/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (629/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17043/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (629/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17043/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (629/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17043/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (629/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (629/6250 : ℝ) ^ (5351/1024 : ℝ) ≤ (307512109200077/50000000000000000000 : ℝ) := by
    have hpowers : (629/6250 : ℝ)^5351 ≤ (307512109200077/50000000000000000000 : ℝ)^1024 := by
      have hnat : (629 : ℕ)^5351*50000000000000000000^1024 ≤ 307512109200077^1024*6250^5351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        629 6250 307512109200077 50000000000000000000 5351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (629/6250 : ℝ)) (X := (307512109200077/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17043/100000 : ℝ) ^ (5351/1024 : ℝ) ≤ (9646678701964683/100000000000000000000 : ℝ) := by
    have hpowers : (17043/100000 : ℝ)^5351 ≤ (9646678701964683/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17043 : ℕ)^5351*100000000000000000000^1024 ≤ 9646678701964683^1024*100000^5351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17043 100000 9646678701964683 100000000000000000000 5351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17043/100000 : ℝ)) (X := (9646678701964683/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000307512109200077/25000000000000000000 : ℝ) ≤ (5000011769420063/5000000000000000 : ℝ) ^ (5351/1024 : ℝ) := by
    have hpowers : (25000307512109200077/25000000000000000000 : ℝ)^1024 ≤ (5000011769420063/5000000000000000 : ℝ)^5351 := by
      have hnat : (25000307512109200077 : ℕ)^1024*5000000000000000^5351 ≤ 5000011769420063^5351*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000307512109200077 25000000000000000000 5000011769420063 5000000000000000 1024 5351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000011769420063/5000000000000000 : ℝ)) (X := (25000307512109200077/25000000000000000000 : ℝ)) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100010261702920364837/100000000000000000000 : ℝ) ≤ (10000196366059489/10000000000000000 : ℝ) ^ (5351/1024 : ℝ) := by
    have hpowers : (100010261702920364837/100000000000000000000 : ℝ)^1024 ≤ (10000196366059489/10000000000000000 : ℝ)^5351 := by
      have hnat : (100010261702920364837 : ℕ)^1024*10000000000000000^5351 ≤ 10000196366059489^5351*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100010261702920364837 100000000000000000000 10000196366059489 10000000000000000 1024 5351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000196366059489/10000000000000000 : ℝ)) (X := (100010261702920364837/100000000000000000000 : ℝ)) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50009646678701964683/50000000000000000000 : ℝ) ≤ (2500092298319713/2500000000000000 : ℝ) ^ (5351/1024 : ℝ) := by
    have hpowers : (50009646678701964683/50000000000000000000 : ℝ)^1024 ≤ (2500092298319713/2500000000000000 : ℝ)^5351 := by
      have hnat : (50009646678701964683 : ℕ)^1024*2500000000000000^5351 ≤ 2500092298319713^5351*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009646678701964683 50000000000000000000 2500092298319713 2500000000000000 1024 5351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500092298319713/2500000000000000 : ℝ)) (X := (50009646678701964683/50000000000000000000 : ℝ)) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(307512109200077/50000000000000000000 : ℝ) ≤ ((6978668561129390089/6979000000000000000 : ℝ)+2*(172827219363/697900000000000 : ℝ)*(629/6250 : ℝ))^(5351/1024 : ℝ) := by
    rw [show (6978668561129390089/6979000000000000000 : ℝ)+2*(172827219363/697900000000000 : ℝ)*(629/6250 : ℝ)=(5000011769420063/5000000000000000 : ℝ) by norm_num, show 1+2*(307512109200077/50000000000000000000 : ℝ)=(25000307512109200077/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9646678701964683/100000000000000000000 : ℝ)+(307512109200077/50000000000000000000 : ℝ) ≤ ((6978668561129390089/6979000000000000000 : ℝ)+(172827219363/697900000000000 : ℝ)*((17043/100000 : ℝ)+(629/6250 : ℝ)))^(5351/1024 : ℝ) := by
    rw [show (6978668561129390089/6979000000000000000 : ℝ)+(172827219363/697900000000000 : ℝ)*((17043/100000 : ℝ)+(629/6250 : ℝ))=(10000196366059489/10000000000000000 : ℝ) by norm_num, show 1+(9646678701964683/100000000000000000000 : ℝ)+(307512109200077/50000000000000000000 : ℝ)=(100010261702920364837/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9646678701964683/100000000000000000000 : ℝ) ≤ ((6978668561129390089/6979000000000000000 : ℝ)+2*(172827219363/697900000000000 : ℝ)*(17043/100000 : ℝ))^(5351/1024 : ℝ) := by
    rw [show (6978668561129390089/6979000000000000000 : ℝ)+2*(172827219363/697900000000000 : ℝ)*(17043/100000 : ℝ)=(2500092298319713/2500000000000000 : ℝ) by norm_num, show 1+2*(9646678701964683/100000000000000000000 : ℝ)=(50009646678701964683/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6978668561129390089/6979000000000000000 : ℝ)*(X 1 0+X 2 0)+(172827219363/697900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5351/1024 : ℝ)) (lo := (629/6250 : ℝ)) (hi := (17043/100000 : ℝ)) (c := (6978668561129390089/6979000000000000000 : ℝ)) (alpha := (172827219363/697900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6978668561129390089/6979000000000000000 : ℝ)*(X 0 1+X 2 1)+(172827219363/697900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5351/1024 : ℝ)) (lo := (629/6250 : ℝ)) (hi := (17043/100000 : ℝ)) (c := (6978668561129390089/6979000000000000000 : ℝ)) (alpha := (172827219363/697900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6978668561129390089/6979000000000000000 : ℝ)*(X 0 2+X 1 2)+(172827219363/697900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5351/1024 : ℝ)) (lo := (629/6250 : ℝ)) (hi := (17043/100000 : ℝ)) (c := (6978668561129390089/6979000000000000000 : ℝ)) (alpha := (172827219363/697900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-21674777/156250000 : ℝ)*X 0 0+(5465576023/10000000000 : ℝ)*X 0 1+(2569562649/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534115953/1000000000 : ℝ)*X 1 0+(-311272047/2000000000 : ℝ)*X 1 1+(80298857/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5341160163/10000000000 : ℝ)*X 2 0+(2569562843/5000000000 : ℝ)*X 2 1+(-1556360929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4095824543/10000000000 : ℝ)*X 0 0+(3632561377/10000000000 : ℝ)*X 0 1+(4594144589/10000000000 : ℝ)*X 0 2+(4095824543/10000000000 : ℝ)*X 1 0+(3632561377/10000000000 : ℝ)*X 1 1+(4594144589/10000000000 : ℝ)*X 1 2+(4095824543/10000000000 : ℝ)*X 2 0+(3632561377/10000000000 : ℝ)*X 2 1+(4594144589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1387332703/10000000000 : ℝ)*X 0 0+(5142762393/10000000000 : ℝ)*X 0 1+(5461884551/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((210150873/400000000 : ℝ)*X 1 0+(-616800831/5000000000 : ℝ)*X 1 1+(5461884143/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5253772377/10000000000 : ℝ)*X 2 0+(2730941309/5000000000 : ℝ)*X 2 1+(-1233603053/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4096257767/10000000000 : ℝ)*X 0 0+(4476006/9765625 : ℝ)*X 0 1+(1821717171/5000000000 : ℝ)*X 0 2+(4096257767/10000000000 : ℝ)*X 1 0+(4476006/9765625 : ℝ)*X 1 1+(1821717171/5000000000 : ℝ)*X 1 2+(4096257767/10000000000 : ℝ)*X 2 0+(4476006/9765625 : ℝ)*X 2 1+(1821717171/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45100998475002171399462489/10904687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (546053107/100000000000000 : ℝ)*(base19) + (97592669/10000000000000 : ℝ)*(base23) + (53244453/100000000000000 : ℝ)*(upper2) + (207500919/100000000000000 : ℝ)*(upper3) + (128226542436953/6250000000000 : ℝ)*(major0) + (128226542436953/6250000000000 : ℝ)*(major1) + (128226542436953/6250000000000 : ℝ)*(major2) + (765817353060317/25000000000000 : ℝ)*(sp0) + (765821342980921/25000000000000 : ℝ)*(sp1) + (191455183373953/6250000000000 : ℝ)*(sp2) + (51997835941621/5000000000000 : ℝ)*(sp3) + (4126433881/25000000000000 : ℝ)*(sp4) + (2008066853/100000000000000 : ℝ)*(sp6) + (6583309021/100000000000000 : ℝ)*(sp7) + (406235664899/39062500000 : ℝ)*(f.failure) + (3063285917976791/100000000000000 : ℝ)*(f.sum) + (40612008697579/34895000000000000000000000000 : ℝ)*base65 + (463228253123426183/43618750000000000000000000000000 : ℝ)*base68 + (366692312570363683/43618750000000000000000000000000 : ℝ)*base70 + (134001396831132433/43618750000000000000000000000000 : ℝ)*base72 + (9393713601807/4361875000000000000000000000 : ℝ)*base74 + (243058474562088683/43618750000000000000000000000000 : ℝ)*base76 + (18776383236226183/43618750000000000000000000000000 : ℝ)*base78 + (182755467717763683/43618750000000000000000000000000 : ℝ)*base80 + (58410205229071/34895000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (7013/781250000000000000 : ℝ)*base90 + (7013/781250000000000000 : ℝ)*base92 + (7013/781250000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33780890872086148462960023/87237500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24446271/1562500000000 : ℝ)*(base19) + (216611621/12500000000000 : ℝ)*(base23) + (5200759/10000000000000 : ℝ)*(lower1) + (40510463/100000000000000 : ℝ)*(upper2) + (68308687/100000000000000 : ℝ)*(upper3) + (189089031/100000000000000 : ℝ)*(upper5) + (524678716387369/25000000000000 : ℝ)*(major0) + (524678716387369/25000000000000 : ℝ)*(major1) + (524678716387369/25000000000000 : ℝ)*(major2) + (44717139/312500000000 : ℝ)*(sp1) + (3133596520930637/100000000000000 : ℝ)*(sp4) + (783395161721203/25000000000000 : ℝ)*(sp5) + (313359478803767/10000000000000 : ℝ)*(sp6) + (531916598630337/50000000000000 : ℝ)*(sp7) + (531916598630337/50000000000000 : ℝ)*(f.failure) + (3133596520930637/100000000000000 : ℝ)*(f.sum) + (110569377960777/34895000000000000000000000000 : ℝ)*base66 + (702350580798719159/174475000000000000000000000000000 : ℝ)*base68 + (1993424421797269159/174475000000000000000000000000000 : ℝ)*base70 + (135167827953305841/174475000000000000000000000000000 : ℝ)*base71 + (44378977202863/8723750000000000000000000000 : ℝ)*base74 + (650785000866455841/174475000000000000000000000000000 : ℝ)*base75 + (1895080027019444159/174475000000000000000000000000000 : ℝ)*base78 + (140032611621244159/174475000000000000000000000000000 : ℝ)*base80 + (56946159463211/17447500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (9765281/1000000000000000000000 : ℝ)*base89 + (9765281/1000000000000000000000 : ℝ)*base91 + (9765281/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1717_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39455713/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (629/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2013/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8521/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1717_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1717_box_0 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-268472403/2500000000 : ℝ)*x 0 + (2706776333/5000000000 : ℝ)*x 1 + (5413552597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268472403/2500000000 : ℝ)^5359 ≤ (253580574633/4000000000000 : ℝ)^4335 := by
    have hnat : (268472403 : ℕ)^5359*4000000000000^4335 ≤ 253580574633^4335*2500000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268472403 2500000000 253580574633 4000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706776333/5000000000 : ℝ)^5359 ≤ (11707560795581/25000000000000 : ℝ)^4335 := by
    have hnat : (2706776333 : ℕ)^5359*25000000000000^4335 ≤ 11707560795581^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706776333 5000000000 11707560795581 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413552597/10000000000 : ℝ)^5359 ≤ (46830242444441/100000000000000 : ℝ)^4335 := by
    have hnat : (5413552597 : ℕ)^5359*100000000000000^4335 ≤ 46830242444441^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413552597 10000000000 46830242444441 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-268472403/2500000000 : ℝ), (2706776333/5000000000 : ℝ), (5413552597/10000000000 : ℝ)] ![(253580574633/4000000000000 : ℝ), (11707560795581/25000000000000 : ℝ), (46830242444441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-268472403/2500000000 : ℝ)|^5359 ≤ (253580574633/4000000000000 : ℝ)^4335
        have hw : |(-268472403/2500000000 : ℝ)|=(268472403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706776333/5000000000 : ℝ)|^5359 ≤ (11707560795581/25000000000000 : ℝ)^4335
        have hw : |(2706776333/5000000000 : ℝ)|=(2706776333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413552597/10000000000 : ℝ)|^5359 ≤ (46830242444441/100000000000000 : ℝ)^4335
        have hw : |(5413552597/10000000000 : ℝ)|=(5413552597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_box_1 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225032817/10000000000 : ℝ)*x 0 + (-1341566397/10000000000 : ℝ)*x 1 + (5413552417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225032817/10000000000 : ℝ)^5359 ≤ (22411292645599/50000000000000 : ℝ)^4335 := by
    have hnat : (5225032817 : ℕ)^5359*50000000000000^4335 ≤ 22411292645599^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225032817 10000000000 22411292645599 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1341566397/10000000000 : ℝ)^5359 ≤ (2086793544711/25000000000000 : ℝ)^4335 := by
    have hnat : (1341566397 : ℕ)^5359*25000000000000^4335 ≤ 2086793544711^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341566397 10000000000 2086793544711 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413552417/10000000000 : ℝ)^5359 ≤ (46830240519527/100000000000000 : ℝ)^4335 := by
    have hnat : (5413552417 : ℕ)^5359*100000000000000^4335 ≤ 46830240519527^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413552417 10000000000 46830240519527 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225032817/10000000000 : ℝ), (-1341566397/10000000000 : ℝ), (5413552417/10000000000 : ℝ)] ![(22411292645599/50000000000000 : ℝ), (2086793544711/25000000000000 : ℝ), (46830240519527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225032817/10000000000 : ℝ)|^5359 ≤ (22411292645599/50000000000000 : ℝ)^4335
        have hw : |(5225032817/10000000000 : ℝ)|=(5225032817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1341566397/10000000000 : ℝ)|^5359 ≤ (2086793544711/25000000000000 : ℝ)^4335
        have hw : |(-1341566397/10000000000 : ℝ)|=(1341566397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413552417/10000000000 : ℝ)|^5359 ≤ (46830240519527/100000000000000 : ℝ)^4335
        have hw : |(5413552417/10000000000 : ℝ)|=(5413552417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_box_2 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (130625809/250000000 : ℝ)*x 0 + (67669411/125000000 : ℝ)*x 1 + (-83847899/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130625809/250000000 : ℝ)^5359 ≤ (11205645111201/25000000000000 : ℝ)^4335 := by
    have hnat : (130625809 : ℕ)^5359*25000000000000^4335 ≤ 11205645111201^4335*250000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130625809 250000000 11205645111201 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67669411/125000000 : ℝ)^5359 ≤ (46830245470833/100000000000000 : ℝ)^4335 := by
    have hnat : (67669411 : ℕ)^5359*100000000000000^4335 ≤ 46830245470833^4335*125000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67669411 125000000 46830245470833 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83847899/625000000 : ℝ)^5359 ≤ (2086793519713/25000000000000 : ℝ)^4335 := by
    have hnat : (83847899 : ℕ)^5359*25000000000000^4335 ≤ 2086793519713^4335*625000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83847899 625000000 2086793519713 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(130625809/250000000 : ℝ), (67669411/125000000 : ℝ), (-83847899/625000000 : ℝ)] ![(11205645111201/25000000000000 : ℝ), (46830245470833/100000000000000 : ℝ), (2086793519713/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(130625809/250000000 : ℝ)|^5359 ≤ (11205645111201/25000000000000 : ℝ)^4335
        have hw : |(130625809/250000000 : ℝ)|=(130625809/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67669411/125000000 : ℝ)|^5359 ≤ (46830245470833/100000000000000 : ℝ)^4335
        have hw : |(67669411/125000000 : ℝ)|=(67669411/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-83847899/625000000 : ℝ)|^5359 ≤ (2086793519713/25000000000000 : ℝ)^4335
        have hw : |(-83847899/625000000 : ℝ)|=(83847899/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_box_3 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (22384813/50000000 : ℝ)*x 0 + (3926565491/10000000000 : ℝ)*x 1 + (3926565291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22384813/50000000 : ℝ)^5359 ≤ (3702882095541/10000000000000 : ℝ)^4335 := by
    have hnat : (22384813 : ℕ)^5359*10000000000000^4335 ≤ 3702882095541^4335*50000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22384813 50000000 3702882095541 10000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3926565491/10000000000 : ℝ)^5359 ≤ (15742795253059/50000000000000 : ℝ)^4335 := by
    have hnat : (3926565491 : ℕ)^5359*50000000000000^4335 ≤ 15742795253059^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3926565491 10000000000 15742795253059 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3926565291/10000000000 : ℝ)^5359 ≤ (3148558852357/10000000000000 : ℝ)^4335 := by
    have hnat : (3926565291 : ℕ)^5359*10000000000000^4335 ≤ 3148558852357^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3926565291 10000000000 3148558852357 10000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(22384813/50000000 : ℝ), (3926565491/10000000000 : ℝ), (3926565291/10000000000 : ℝ)] ![(3702882095541/10000000000000 : ℝ), (15742795253059/50000000000000 : ℝ), (3148558852357/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(22384813/50000000 : ℝ)|^5359 ≤ (3702882095541/10000000000000 : ℝ)^4335
        have hw : |(22384813/50000000 : ℝ)|=(22384813/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3926565491/10000000000 : ℝ)|^5359 ≤ (15742795253059/50000000000000 : ℝ)^4335
        have hw : |(3926565491/10000000000 : ℝ)|=(3926565491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3926565291/10000000000 : ℝ)|^5359 ≤ (3148558852357/10000000000000 : ℝ)^4335
        have hw : |(3926565291/10000000000 : ℝ)|=(3926565291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_box_4 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1721000233/10000000000 : ℝ)*x 0 + (5177736383/10000000000 : ℝ)*x 1 + (323608527/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1721000233/10000000000 : ℝ)^5359 ≤ (11356892511609/100000000000000 : ℝ)^4335 := by
    have hnat : (1721000233 : ℕ)^5359*100000000000000^4335 ≤ 11356892511609^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1721000233 10000000000 11356892511609 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177736383/10000000000 : ℝ)^5359 ≤ (22160776738959/50000000000000 : ℝ)^4335 := by
    have hnat : (5177736383 : ℕ)^5359*50000000000000^4335 ≤ 22160776738959^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177736383 10000000000 22160776738959 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323608527/625000000 : ℝ)^5359 ≤ (22160776998219/50000000000000 : ℝ)^4335 := by
    have hnat : (323608527 : ℕ)^5359*50000000000000^4335 ≤ 22160776998219^4335*625000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323608527 625000000 22160776998219 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1721000233/10000000000 : ℝ), (5177736383/10000000000 : ℝ), (323608527/625000000 : ℝ)] ![(11356892511609/100000000000000 : ℝ), (22160776738959/50000000000000 : ℝ), (22160776998219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1721000233/10000000000 : ℝ)|^5359 ≤ (11356892511609/100000000000000 : ℝ)^4335
        have hw : |(-1721000233/10000000000 : ℝ)|=(1721000233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177736383/10000000000 : ℝ)|^5359 ≤ (22160776738959/50000000000000 : ℝ)^4335
        have hw : |(5177736383/10000000000 : ℝ)|=(5177736383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323608527/625000000 : ℝ)|^5359 ≤ (22160776998219/50000000000000 : ℝ)^4335
        have hw : |(323608527/625000000 : ℝ)|=(323608527/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_box_5 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5384691847/10000000000 : ℝ)*x 0 + (-1445866177/10000000000 : ℝ)*x 1 + (2588868369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5384691847/10000000000 : ℝ)^5359 ≤ (46521801235041/100000000000000 : ℝ)^4335 := by
    have hnat : (5384691847 : ℕ)^5359*100000000000000^4335 ≤ 46521801235041^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384691847 10000000000 46521801235041 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1445866177/10000000000 : ℝ)^5359 ≤ (286145047569/3125000000000 : ℝ)^4335 := by
    have hnat : (1445866177 : ℕ)^5359*3125000000000^4335 ≤ 286145047569^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1445866177 10000000000 286145047569 3125000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588868369/5000000000 : ℝ)^5359 ≤ (8864311446909/20000000000000 : ℝ)^4335 := by
    have hnat : (2588868369 : ℕ)^5359*20000000000000^4335 ≤ 8864311446909^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588868369 5000000000 8864311446909 20000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5384691847/10000000000 : ℝ), (-1445866177/10000000000 : ℝ), (2588868369/5000000000 : ℝ)] ![(46521801235041/100000000000000 : ℝ), (286145047569/3125000000000 : ℝ), (8864311446909/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5384691847/10000000000 : ℝ)|^5359 ≤ (46521801235041/100000000000000 : ℝ)^4335
        have hw : |(5384691847/10000000000 : ℝ)|=(5384691847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1445866177/10000000000 : ℝ)|^5359 ≤ (286145047569/3125000000000 : ℝ)^4335
        have hw : |(-1445866177/10000000000 : ℝ)|=(1445866177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588868369/5000000000 : ℝ)|^5359 ≤ (8864311446909/20000000000000 : ℝ)^4335
        have hw : |(2588868369/5000000000 : ℝ)|=(2588868369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_box_6 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5384692233/10000000000 : ℝ)*x 0 + (1035547267/2000000000 : ℝ)*x 1 + (-722933097/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5384692233/10000000000 : ℝ)^5359 ≤ (23260902678851/50000000000000 : ℝ)^4335 := by
    have hnat : (5384692233 : ℕ)^5359*50000000000000^4335 ≤ 23260902678851^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384692233 10000000000 23260902678851 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035547267/2000000000 : ℝ)^5359 ≤ (44321552969979/100000000000000 : ℝ)^4335 := by
    have hnat : (1035547267 : ℕ)^5359*100000000000000^4335 ≤ 44321552969979^4335*2000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035547267 2000000000 44321552969979 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (722933097/5000000000 : ℝ)^5359 ≤ (91566416553/1000000000000 : ℝ)^4335 := by
    have hnat : (722933097 : ℕ)^5359*1000000000000^4335 ≤ 91566416553^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      722933097 5000000000 91566416553 1000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5384692233/10000000000 : ℝ), (1035547267/2000000000 : ℝ), (-722933097/5000000000 : ℝ)] ![(23260902678851/50000000000000 : ℝ), (44321552969979/100000000000000 : ℝ), (91566416553/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5384692233/10000000000 : ℝ)|^5359 ≤ (23260902678851/50000000000000 : ℝ)^4335
        have hw : |(5384692233/10000000000 : ℝ)|=(5384692233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035547267/2000000000 : ℝ)|^5359 ≤ (44321552969979/100000000000000 : ℝ)^4335
        have hw : |(1035547267/2000000000 : ℝ)|=(1035547267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-722933097/5000000000 : ℝ)|^5359 ≤ (91566416553/1000000000000 : ℝ)^4335
        have hw : |(-722933097/5000000000 : ℝ)|=(722933097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_box_7 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1849337201/5000000000 : ℝ)*x 0 + (539361603/1250000000 : ℝ)*x 1 + (862978617/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1849337201/5000000000 : ℝ)^5359 ≤ (14621142882481/50000000000000 : ℝ)^4335 := by
    have hnat : (1849337201 : ℕ)^5359*50000000000000^4335 ≤ 14621142882481^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1849337201 5000000000 14621142882481 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539361603/1250000000 : ℝ)^5359 ≤ (353788557869/1000000000000 : ℝ)^4335 := by
    have hnat : (539361603 : ℕ)^5359*1000000000000^4335 ≤ 353788557869^4335*1250000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539361603 1250000000 353788557869 1000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (862978617/2000000000 : ℝ)^5359 ≤ (35378858432407/100000000000000 : ℝ)^4335 := by
    have hnat : (862978617 : ℕ)^5359*100000000000000^4335 ≤ 35378858432407^4335*2000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862978617 2000000000 35378858432407 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1849337201/5000000000 : ℝ), (539361603/1250000000 : ℝ), (862978617/2000000000 : ℝ)] ![(14621142882481/50000000000000 : ℝ), (353788557869/1000000000000 : ℝ), (35378858432407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1849337201/5000000000 : ℝ)|^5359 ≤ (14621142882481/50000000000000 : ℝ)^4335
        have hw : |(1849337201/5000000000 : ℝ)|=(1849337201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539361603/1250000000 : ℝ)|^5359 ≤ (353788557869/1000000000000 : ℝ)^4335
        have hw : |(539361603/1250000000 : ℝ)|=(539361603/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(862978617/2000000000 : ℝ)|^5359 ≤ (35378858432407/100000000000000 : ℝ)^4335
        have hw : |(862978617/2000000000 : ℝ)|=(862978617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_box_8 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1581725591/10000000000 : ℝ)*x 0 + (2501671407/5000000000 : ℝ)*x 1 + (2728003743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1581725591/10000000000 : ℝ)^5359 ≤ (10231809139711/100000000000000 : ℝ)^4335 := by
    have hnat : (1581725591 : ℕ)^5359*100000000000000^4335 ≤ 10231809139711^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1581725591 10000000000 10231809139711 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2501671407/5000000000 : ℝ)^5359 ≤ (21241758840539/50000000000000 : ℝ)^4335 := by
    have hnat : (2501671407 : ℕ)^5359*50000000000000^4335 ≤ 21241758840539^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2501671407 5000000000 21241758840539 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2728003743/5000000000 : ℝ)^5359 ≤ (23642336585139/50000000000000 : ℝ)^4335 := by
    have hnat : (2728003743 : ℕ)^5359*50000000000000^4335 ≤ 23642336585139^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728003743 5000000000 23642336585139 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1581725591/10000000000 : ℝ), (2501671407/5000000000 : ℝ), (2728003743/5000000000 : ℝ)] ![(10231809139711/100000000000000 : ℝ), (21241758840539/50000000000000 : ℝ), (23642336585139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1581725591/10000000000 : ℝ)|^5359 ≤ (10231809139711/100000000000000 : ℝ)^4335
        have hw : |(-1581725591/10000000000 : ℝ)|=(1581725591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2501671407/5000000000 : ℝ)|^5359 ≤ (21241758840539/50000000000000 : ℝ)^4335
        have hw : |(2501671407/5000000000 : ℝ)|=(2501671407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2728003743/5000000000 : ℝ)|^5359 ≤ (23642336585139/50000000000000 : ℝ)^4335
        have hw : |(2728003743/5000000000 : ℝ)|=(2728003743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_box_9 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598154381/5000000000 : ℝ)*x 0 + (-264405567/2000000000 : ℝ)*x 1 + (545600817/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598154381/5000000000 : ℝ)^5359 ≤ (4451817045489/10000000000000 : ℝ)^4335 := by
    have hnat : (2598154381 : ℕ)^5359*10000000000000^4335 ≤ 4451817045489^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598154381 5000000000 4451817045489 10000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264405567/2000000000 : ℝ)^5359 ≤ (8197149026017/100000000000000 : ℝ)^4335 := by
    have hnat : (264405567 : ℕ)^5359*100000000000000^4335 ≤ 8197149026017^4335*2000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264405567 2000000000 8197149026017 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545600817/1000000000 : ℝ)^5359 ≤ (47284680498459/100000000000000 : ℝ)^4335 := by
    have hnat : (545600817 : ℕ)^5359*100000000000000^4335 ≤ 47284680498459^4335*1000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545600817 1000000000 47284680498459 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598154381/5000000000 : ℝ), (-264405567/2000000000 : ℝ), (545600817/1000000000 : ℝ)] ![(4451817045489/10000000000000 : ℝ), (8197149026017/100000000000000 : ℝ), (47284680498459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598154381/5000000000 : ℝ)|^5359 ≤ (4451817045489/10000000000000 : ℝ)^4335
        have hw : |(2598154381/5000000000 : ℝ)|=(2598154381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-264405567/2000000000 : ℝ)|^5359 ≤ (8197149026017/100000000000000 : ℝ)^4335
        have hw : |(-264405567/2000000000 : ℝ)|=(264405567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(545600817/1000000000 : ℝ)|^5359 ≤ (47284680498459/100000000000000 : ℝ)^4335
        have hw : |(545600817/1000000000 : ℝ)|=(545600817/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_box_10 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598155149/5000000000 : ℝ)*x 0 + (1364001789/2500000000 : ℝ)*x 1 + (-1322027131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598155149/5000000000 : ℝ)^5359 ≤ (11129546680667/25000000000000 : ℝ)^4335 := by
    have hnat : (2598155149 : ℕ)^5359*25000000000000^4335 ≤ 11129546680667^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598155149 5000000000 11129546680667 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364001789/2500000000 : ℝ)^5359 ≤ (738822963043/1562500000000 : ℝ)^4335 := by
    have hnat : (1364001789 : ℕ)^5359*1562500000000^4335 ≤ 738822963043^4335*2500000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364001789 2500000000 738822963043 1562500000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1322027131/10000000000 : ℝ)^5359 ≤ (8197143629799/100000000000000 : ℝ)^4335 := by
    have hnat : (1322027131 : ℕ)^5359*100000000000000^4335 ≤ 8197143629799^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322027131 10000000000 8197143629799 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598155149/5000000000 : ℝ), (1364001789/2500000000 : ℝ), (-1322027131/10000000000 : ℝ)] ![(11129546680667/25000000000000 : ℝ), (738822963043/1562500000000 : ℝ), (8197143629799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598155149/5000000000 : ℝ)|^5359 ≤ (11129546680667/25000000000000 : ℝ)^4335
        have hw : |(2598155149/5000000000 : ℝ)|=(2598155149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1364001789/2500000000 : ℝ)|^5359 ≤ (738822963043/1562500000000 : ℝ)^4335
        have hw : |(1364001789/2500000000 : ℝ)|=(1364001789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1322027131/10000000000 : ℝ)|^5359 ≤ (8197143629799/100000000000000 : ℝ)^4335
        have hw : |(-1322027131/10000000000 : ℝ)|=(1322027131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_box_11 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1153028223/2500000000 : ℝ)*x 0 + (3856469529/10000000000 : ℝ)*x 1 + (3856467301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1153028223/2500000000 : ℝ)^5359 ≤ (19207791679333/50000000000000 : ℝ)^4335 := by
    have hnat : (1153028223 : ℕ)^5359*50000000000000^4335 ≤ 19207791679333^4335*2500000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153028223 2500000000 19207791679333 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3856469529/10000000000 : ℝ)^5359 ≤ (15396109652653/50000000000000 : ℝ)^4335 := by
    have hnat : (3856469529 : ℕ)^5359*50000000000000^4335 ≤ 15396109652653^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3856469529 10000000000 15396109652653 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3856467301/10000000000 : ℝ)^5359 ≤ (30792197313499/100000000000000 : ℝ)^4335 := by
    have hnat : (3856467301 : ℕ)^5359*100000000000000^4335 ≤ 30792197313499^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3856467301 10000000000 30792197313499 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1153028223/2500000000 : ℝ), (3856469529/10000000000 : ℝ), (3856467301/10000000000 : ℝ)] ![(19207791679333/50000000000000 : ℝ), (15396109652653/50000000000000 : ℝ), (30792197313499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1153028223/2500000000 : ℝ)|^5359 ≤ (19207791679333/50000000000000 : ℝ)^4335
        have hw : |(1153028223/2500000000 : ℝ)|=(1153028223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3856469529/10000000000 : ℝ)|^5359 ≤ (15396109652653/50000000000000 : ℝ)^4335
        have hw : |(3856469529/10000000000 : ℝ)|=(3856469529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3856467301/10000000000 : ℝ)|^5359 ≤ (30792197313499/100000000000000 : ℝ)^4335
        have hw : |(3856467301/10000000000 : ℝ)|=(3856467301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_box_12 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-150939409/1250000000 : ℝ)*x 0 + (5579823501/10000000000 : ℝ)*x 1 + (5152691201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (150939409/1250000000 : ℝ)^5359 ≤ (3664293191217/50000000000000 : ℝ)^4335 := by
    have hnat : (150939409 : ℕ)^5359*50000000000000^4335 ≤ 3664293191217^4335*1250000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150939409 1250000000 3664293191217 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5579823501/10000000000 : ℝ)^5359 ≤ (48614737819251/100000000000000 : ℝ)^4335 := by
    have hnat : (5579823501 : ℕ)^5359*100000000000000^4335 ≤ 48614737819251^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5579823501 10000000000 48614737819251 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5152691201/10000000000 : ℝ)^5359 ≤ (11014168944597/25000000000000 : ℝ)^4335 := by
    have hnat : (5152691201 : ℕ)^5359*25000000000000^4335 ≤ 11014168944597^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152691201 10000000000 11014168944597 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-150939409/1250000000 : ℝ), (5579823501/10000000000 : ℝ), (5152691201/10000000000 : ℝ)] ![(3664293191217/50000000000000 : ℝ), (48614737819251/100000000000000 : ℝ), (11014168944597/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-150939409/1250000000 : ℝ)|^5359 ≤ (3664293191217/50000000000000 : ℝ)^4335
        have hw : |(-150939409/1250000000 : ℝ)|=(150939409/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5579823501/10000000000 : ℝ)|^5359 ≤ (48614737819251/100000000000000 : ℝ)^4335
        have hw : |(5579823501/10000000000 : ℝ)|=(5579823501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5152691201/10000000000 : ℝ)|^5359 ≤ (11014168944597/25000000000000 : ℝ)^4335
        have hw : |(5152691201/10000000000 : ℝ)|=(5152691201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_box_13 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2700840307/5000000000 : ℝ)*x 0 + (-364126369/2500000000 : ℝ)*x 1 + (5152691129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2700840307/5000000000 : ℝ)^5359 ≤ (23351658396457/50000000000000 : ℝ)^4335 := by
    have hnat : (2700840307 : ℕ)^5359*50000000000000^4335 ≤ 23351658396457^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700840307 5000000000 23351658396457 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (364126369/2500000000 : ℝ)^5359 ≤ (577500510843/6250000000000 : ℝ)^4335 := by
    have hnat : (364126369 : ℕ)^5359*6250000000000^4335 ≤ 577500510843^4335*2500000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364126369 2500000000 577500510843 6250000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5152691129/10000000000 : ℝ)^5359 ≤ (5507084377169/12500000000000 : ℝ)^4335 := by
    have hnat : (5152691129 : ℕ)^5359*12500000000000^4335 ≤ 5507084377169^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152691129 10000000000 5507084377169 12500000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2700840307/5000000000 : ℝ), (-364126369/2500000000 : ℝ), (5152691129/10000000000 : ℝ)] ![(23351658396457/50000000000000 : ℝ), (577500510843/6250000000000 : ℝ), (5507084377169/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2700840307/5000000000 : ℝ)|^5359 ≤ (23351658396457/50000000000000 : ℝ)^4335
        have hw : |(2700840307/5000000000 : ℝ)|=(2700840307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-364126369/2500000000 : ℝ)|^5359 ≤ (577500510843/6250000000000 : ℝ)^4335
        have hw : |(-364126369/2500000000 : ℝ)|=(364126369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5152691129/10000000000 : ℝ)|^5359 ≤ (5507084377169/12500000000000 : ℝ)^4335
        have hw : |(5152691129/10000000000 : ℝ)|=(5152691129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_box_14 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5401680433/10000000000 : ℝ)*x 0 + (1288172891/2500000000 : ℝ)*x 1 + (-91031571/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5401680433/10000000000 : ℝ)^5359 ≤ (4670331485831/10000000000000 : ℝ)^4335 := by
    have hnat : (5401680433 : ℕ)^5359*10000000000000^4335 ≤ 4670331485831^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401680433 10000000000 4670331485831 10000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1288172891/2500000000 : ℝ)^5359 ≤ (22028339807637/50000000000000 : ℝ)^4335 := by
    have hnat : (1288172891 : ℕ)^5359*50000000000000^4335 ≤ 22028339807637^4335*2500000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288172891 2500000000 22028339807637 50000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (91031571/625000000 : ℝ)^5359 ≤ (2310001376759/25000000000000 : ℝ)^4335 := by
    have hnat : (91031571 : ℕ)^5359*25000000000000^4335 ≤ 2310001376759^4335*625000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91031571 625000000 2310001376759 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5401680433/10000000000 : ℝ), (1288172891/2500000000 : ℝ), (-91031571/625000000 : ℝ)] ![(4670331485831/10000000000000 : ℝ), (22028339807637/50000000000000 : ℝ), (2310001376759/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5401680433/10000000000 : ℝ)|^5359 ≤ (4670331485831/10000000000000 : ℝ)^4335
        have hw : |(5401680433/10000000000 : ℝ)|=(5401680433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1288172891/2500000000 : ℝ)|^5359 ≤ (22028339807637/50000000000000 : ℝ)^4335
        have hw : |(1288172891/2500000000 : ℝ)|=(1288172891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-91031571/625000000 : ℝ)|^5359 ≤ (2310001376759/25000000000000 : ℝ)^4335
        have hw : |(-91031571/625000000 : ℝ)|=(91031571/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1717_box_15 (p : ℝ) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1806516127/5000000000 : ℝ)*x 0 + (217801227/500000000 : ℝ)*x 1 + (4356022577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1806516127/5000000000 : ℝ)^5359 ≤ (28407546194153/100000000000000 : ℝ)^4335 := by
    have hnat : (1806516127 : ℕ)^5359*100000000000000^4335 ≤ 28407546194153^4335*5000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1806516127 5000000000 28407546194153 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217801227/500000000 : ℝ)^5359 ≤ (35796236865327/100000000000000 : ℝ)^4335 := by
    have hnat : (217801227 : ℕ)^5359*100000000000000^4335 ≤ 35796236865327^4335*500000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217801227 500000000 35796236865327 100000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4356022577/10000000000 : ℝ)^5359 ≤ (8949054230909/25000000000000 : ℝ)^4335 := by
    have hnat : (4356022577 : ℕ)^5359*25000000000000^4335 ≤ 8949054230909^4335*10000000000^5359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356022577 10000000000 8949054230909 25000000000000 5359 4335 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5359/1024 : ℝ)) 5359 4335 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1806516127/5000000000 : ℝ), (217801227/500000000 : ℝ), (4356022577/10000000000 : ℝ)] ![(28407546194153/100000000000000 : ℝ), (35796236865327/100000000000000 : ℝ), (8949054230909/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1806516127/5000000000 : ℝ)|^5359 ≤ (28407546194153/100000000000000 : ℝ)^4335
        have hw : |(1806516127/5000000000 : ℝ)|=(1806516127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217801227/500000000 : ℝ)|^5359 ≤ (35796236865327/100000000000000 : ℝ)^4335
        have hw : |(217801227/500000000 : ℝ)|=(217801227/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4356022577/10000000000 : ℝ)|^5359 ≤ (8949054230909/25000000000000 : ℝ)^4335
        have hw : |(4356022577/10000000000 : ℝ)|=(4356022577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1717_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39455713/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8521/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2013/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(66813/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29283/50000 : ℝ) ∧ (40853/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (45261/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8521/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2013/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8521/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2013/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8521/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2013/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8521/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2013/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8521/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2013/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8521/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2013/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2013/20000 : ℝ) ^ (5351/1024 : ℝ) ≤ (615343627848023/100000000000000000000 : ℝ) := by
    have hpowers : (2013/20000 : ℝ)^5351 ≤ (615343627848023/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2013 : ℕ)^5351*100000000000000000000^1024 ≤ 615343627848023^1024*20000^5351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2013 20000 615343627848023 100000000000000000000 5351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2013/20000 : ℝ)) (X := (615343627848023/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8521/50000 : ℝ) ^ (5351/1024 : ℝ) ≤ (1205465160313699/12500000000000000000 : ℝ) := by
    have hpowers : (8521/50000 : ℝ)^5351 ≤ (1205465160313699/12500000000000000000 : ℝ)^1024 := by
      have hnat : (8521 : ℕ)^5351*12500000000000000000^1024 ≤ 1205465160313699^1024*50000^5351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8521 50000 1205465160313699 12500000000000000000 5351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8521/50000 : ℝ)) (X := (1205465160313699/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000615343627848023/50000000000000000000 : ℝ) ≤ (10000023551064833/10000000000000000 : ℝ) ^ (5351/1024 : ℝ) := by
    have hpowers : (50000615343627848023/50000000000000000000 : ℝ)^1024 ≤ (10000023551064833/10000000000000000 : ℝ)^5351 := by
      have hnat : (50000615343627848023 : ℕ)^1024*10000000000000000^5351 ≤ 10000023551064833^5351*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000615343627848023 50000000000000000000 10000023551064833 10000000000000000 1024 5351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000023551064833/10000000000000000 : ℝ)) (X := (50000615343627848023/50000000000000000000 : ℝ)) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20002051812982071523/20000000000000000000 : ℝ) ≤ (10000196315581109/10000000000000000 : ℝ) ^ (5351/1024 : ℝ) := by
    have hpowers : (20002051812982071523/20000000000000000000 : ℝ)^1024 ≤ (10000196315581109/10000000000000000 : ℝ)^5351 := by
      have hnat : (20002051812982071523 : ℕ)^1024*10000000000000000^5351 ≤ 10000196315581109^5351*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20002051812982071523 20000000000000000000 10000196315581109 10000000000000000 1024 5351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000196315581109/10000000000000000 : ℝ)) (X := (20002051812982071523/20000000000000000000 : ℝ)) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6251205465160313699/6250000000000000000 : ℝ) ≤ (2000073816019477/2000000000000000 : ℝ) ^ (5351/1024 : ℝ) := by
    have hpowers : (6251205465160313699/6250000000000000000 : ℝ)^1024 ≤ (2000073816019477/2000000000000000 : ℝ)^5351 := by
      have hnat : (6251205465160313699 : ℕ)^1024*2000000000000000^5351 ≤ 2000073816019477^5351*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251205465160313699 6250000000000000000 2000073816019477 2000000000000000 1024 5351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000073816019477/2000000000000000 : ℝ)) (X := (6251205465160313699/6250000000000000000 : ℝ)) (by norm_num) 5351 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(615343627848023/100000000000000000000 : ℝ) ≤ ((69766686566066703961/69770000000000000000 : ℝ)+2*(43191129069/174425000000000 : ℝ)*(2013/20000 : ℝ))^(5351/1024 : ℝ) := by
    rw [show (69766686566066703961/69770000000000000000 : ℝ)+2*(43191129069/174425000000000 : ℝ)*(2013/20000 : ℝ)=(10000023551064833/10000000000000000 : ℝ) by norm_num, show 1+2*(615343627848023/100000000000000000000 : ℝ)=(50000615343627848023/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1205465160313699/12500000000000000000 : ℝ)+(615343627848023/100000000000000000000 : ℝ) ≤ ((69766686566066703961/69770000000000000000 : ℝ)+(43191129069/174425000000000 : ℝ)*((8521/50000 : ℝ)+(2013/20000 : ℝ)))^(5351/1024 : ℝ) := by
    rw [show (69766686566066703961/69770000000000000000 : ℝ)+(43191129069/174425000000000 : ℝ)*((8521/50000 : ℝ)+(2013/20000 : ℝ))=(10000196315581109/10000000000000000 : ℝ) by norm_num, show 1+(1205465160313699/12500000000000000000 : ℝ)+(615343627848023/100000000000000000000 : ℝ)=(20002051812982071523/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1205465160313699/12500000000000000000 : ℝ) ≤ ((69766686566066703961/69770000000000000000 : ℝ)+2*(43191129069/174425000000000 : ℝ)*(8521/50000 : ℝ))^(5351/1024 : ℝ) := by
    rw [show (69766686566066703961/69770000000000000000 : ℝ)+2*(43191129069/174425000000000 : ℝ)*(8521/50000 : ℝ)=(2000073816019477/2000000000000000 : ℝ) by norm_num, show 1+2*(1205465160313699/12500000000000000000 : ℝ)=(6251205465160313699/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (69766686566066703961/69770000000000000000 : ℝ)*(X 1 0+X 2 0)+(43191129069/174425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5351/1024 : ℝ)) (lo := (2013/20000 : ℝ)) (hi := (8521/50000 : ℝ)) (c := (69766686566066703961/69770000000000000000 : ℝ)) (alpha := (43191129069/174425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (69766686566066703961/69770000000000000000 : ℝ)*(X 0 1+X 2 1)+(43191129069/174425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5351/1024 : ℝ)) (lo := (2013/20000 : ℝ)) (hi := (8521/50000 : ℝ)) (c := (69766686566066703961/69770000000000000000 : ℝ)) (alpha := (43191129069/174425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (69766686566066703961/69770000000000000000 : ℝ)*(X 0 2+X 1 2)+(43191129069/174425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5351/1024 : ℝ)) (lo := (2013/20000 : ℝ)) (hi := (8521/50000 : ℝ)) (c := (69766686566066703961/69770000000000000000 : ℝ)) (alpha := (43191129069/174425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-268472403/2500000000 : ℝ)*X 0 0+(2706776333/5000000000 : ℝ)*X 0 1+(5413552597/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5225032817/10000000000 : ℝ)*X 1 0+(-1341566397/10000000000 : ℝ)*X 1 1+(5413552417/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((130625809/250000000 : ℝ)*X 2 0+(67669411/125000000 : ℝ)*X 2 1+(-83847899/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((22384813/50000000 : ℝ)*X 0 0+(3926565491/10000000000 : ℝ)*X 0 1+(3926565291/10000000000 : ℝ)*X 0 2+(22384813/50000000 : ℝ)*X 1 0+(3926565491/10000000000 : ℝ)*X 1 1+(3926565291/10000000000 : ℝ)*X 1 2+(22384813/50000000 : ℝ)*X 2 0+(3926565491/10000000000 : ℝ)*X 2 1+(3926565291/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1721000233/10000000000 : ℝ)*X 0 0+(5177736383/10000000000 : ℝ)*X 0 1+(323608527/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5384691847/10000000000 : ℝ)*X 1 0+(-1445866177/10000000000 : ℝ)*X 1 1+(2588868369/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5384692233/10000000000 : ℝ)*X 2 0+(1035547267/2000000000 : ℝ)*X 2 1+(-722933097/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1849337201/5000000000 : ℝ)*X 0 0+(539361603/1250000000 : ℝ)*X 0 1+(862978617/2000000000 : ℝ)*X 0 2+(1849337201/5000000000 : ℝ)*X 1 0+(539361603/1250000000 : ℝ)*X 1 1+(862978617/2000000000 : ℝ)*X 1 2+(1849337201/5000000000 : ℝ)*X 2 0+(539361603/1250000000 : ℝ)*X 2 1+(862978617/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1581725591/10000000000 : ℝ)*X 0 0+(2501671407/5000000000 : ℝ)*X 0 1+(2728003743/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2598154381/5000000000 : ℝ)*X 1 0+(-264405567/2000000000 : ℝ)*X 1 1+(545600817/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2598155149/5000000000 : ℝ)*X 2 0+(1364001789/2500000000 : ℝ)*X 2 1+(-1322027131/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1153028223/2500000000 : ℝ)*X 0 0+(3856469529/10000000000 : ℝ)*X 0 1+(3856467301/10000000000 : ℝ)*X 0 2+(1153028223/2500000000 : ℝ)*X 1 0+(3856469529/10000000000 : ℝ)*X 1 1+(3856467301/10000000000 : ℝ)*X 1 2+(1153028223/2500000000 : ℝ)*X 2 0+(3856469529/10000000000 : ℝ)*X 2 1+(3856467301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-150939409/1250000000 : ℝ)*X 0 0+(5579823501/10000000000 : ℝ)*X 0 1+(5152691201/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2700840307/5000000000 : ℝ)*X 1 0+(-364126369/2500000000 : ℝ)*X 1 1+(5152691129/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5401680433/10000000000 : ℝ)*X 2 0+(1288172891/2500000000 : ℝ)*X 2 1+(-91031571/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1806516127/5000000000 : ℝ)*X 0 0+(217801227/500000000 : ℝ)*X 0 1+(4356022577/10000000000 : ℝ)*X 0 2+(1806516127/5000000000 : ℝ)*X 1 0+(217801227/500000000 : ℝ)*X 1 1+(4356022577/10000000000 : ℝ)*X 1 2+(1806516127/5000000000 : ℝ)*X 2 0+(217801227/500000000 : ℝ)*X 2 1+(4356022577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1717_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66813/100000 : ℝ) ≤ (-233069179590843259143029747862753/348850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11566731/50000000000000 : ℝ)*(upper0) + (45387/100000000000000 : ℝ)*(lower1) + (7714739/25000000000000 : ℝ)*(lower2) + (12235139/100000000000000 : ℝ)*(lower3) + (2514927/25000000000000 : ℝ)*(upper5) + (137434093124109/10000000000000 : ℝ)*(major0) + (137434093124109/10000000000000 : ℝ)*(major1) + (137434093124109/10000000000000 : ℝ)*(major2) + (2074302198084303/100000000000000 : ℝ)*(sp4) + (12964199923993/625000000000 : ℝ)*(sp5) + (518575238367907/25000000000000 : ℝ)*(sp6) + (696649902761149/100000000000000 : ℝ)*(sp7) + (30210245423/100000000000000 : ℝ)*(sp13) + (49784507/4000000000000 : ℝ)*(sp14) + (696649902761149/100000000000000 : ℝ)*(f.failure) + (2074302198084303/100000000000000 : ℝ)*(f.sum) + (5947160901009/1395400000000000000000000000 : ℝ)*base65 + (1495248063859204251/697700000000000000000000000000000 : ℝ)*base68 + (2427159490366404251/697700000000000000000000000000000 : ℝ)*base70 + (183961488602704251/697700000000000000000000000000000 : ℝ)*base72 + (372145614117/1744250000000000000000000000 : ℝ)*base74 + (1000571680111104251/697700000000000000000000000000000 : ℝ)*base76 + (1907873918286395749/697700000000000000000000000000000 : ℝ)*base77 + (1949379840812095749/697700000000000000000000000000000 : ℝ)*base79 + (4720142641927/6977000000000000000000000000 : ℝ)*base81 + (2494237/2000000000000000000000 : ℝ)*base89 + (2494237/2000000000000000000000 : ℝ)*base91 + (2494237/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29283/50000 : ℝ) ≤ (2043169980649777076178255403374159/3488500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27998191/100000000000000 : ℝ)*(lower0) + (47506963/100000000000000 : ℝ)*(upper2) + (449961/5000000000000 : ℝ)*(upper3) + (1307431/12500000000000 : ℝ)*(lower5) + (1481183259535027/100000000000000 : ℝ)*(major0) + (1481183259535027/100000000000000 : ℝ)*(major1) + (1481183259535027/100000000000000 : ℝ)*(major2) + (438407120991621/20000000000000 : ℝ)*(sp0) + (2192024191696519/100000000000000 : ℝ)*(sp1) + (1712526843331/78125000000 : ℝ)*(sp2) + (375403901812403/50000000000000 : ℝ)*(sp3) + (49819777/4000000000000 : ℝ)*(sp6) + (40413513/20000000000000 : ℝ)*(sp7) + (2282652317/20000000000000 : ℝ)*(sp9) + (75080800569237/10000000000000 : ℝ)*(f.failure) + (438407120991621/20000000000000 : ℝ)*(f.sum) + (49502363559251/17442500000000000000000000000 : ℝ)*base65 + (47737088664307658053/6977000000000000000000000000000000 : ℝ)*base68 + (44686085968152341947/6977000000000000000000000000000000 : ℝ)*base69 + (29821913524293341947/6977000000000000000000000000000000 : ℝ)*base71 + (22225145713741/4360625000000000000000000000 : ℝ)*base74 + (41398961807476341947/6977000000000000000000000000000000 : ℝ)*base75 + (36981613023029341947/6977000000000000000000000000000000 : ℝ)*base77 + (29183660803872658053/6977000000000000000000000000000000 : ℝ)*base80 + (81978281989567/34885000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2299019/200000000000000000000 : ℝ)*base90 + (2299019/200000000000000000000 : ℝ)*base92 + (2299019/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (40853/50000 : ℝ) ≤ (712599115087813345307610642314169/872125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37366401/50000000000000 : ℝ)*(upper0) + (8683597/50000000000000 : ℝ)*(upper1) + (4702459/5000000000000 : ℝ)*(upper3) + (186603937/50000000000000 : ℝ)*(upper4) + (748903560300443/50000000000000 : ℝ)*(major0) + (748903560300443/50000000000000 : ℝ)*(major1) + (748903560300443/50000000000000 : ℝ)*(major2) + (701185827/4000000000000 : ℝ)*(sp1) + (2932786631/10000000000000 : ℝ)*(sp2) + (10469584361/50000000000000 : ℝ)*(sp3) + (2209143519781167/100000000000000 : ℝ)*(sp8) + (552281497533873/25000000000000 : ℝ)*(sp9) + (276139273989357/12500000000000 : ℝ)*(sp10) + (759213659177473/100000000000000 : ℝ)*(sp11) + (379617299173097/50000000000000 : ℝ)*(f.failure) + (2209143519781167/100000000000000 : ℝ)*(f.sum) + (228972634186279/34885000000000000000000000000 : ℝ)*base66 + (27460375187019545277/3488500000000000000000000000000000 : ℝ)*base68 + (29818175520249545277/3488500000000000000000000000000000 : ℝ)*base70 + (50059924171882545277/3488500000000000000000000000000000 : ℝ)*base72 + (22483408505449/8721250000000000000000000000 : ℝ)*base73 + (31824062856290045277/3488500000000000000000000000000000 : ℝ)*base76 + (12286032118329045277/3488500000000000000000000000000000 : ℝ)*base78 + (8568160701557454723/3488500000000000000000000000000000 : ℝ)*base79 + (183724098855079/34885000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (7446839/1000000000000000000000 : ℝ)*base90 + (7446839/1000000000000000000000 : ℝ)*base92 + (7446839/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-45261/50000 : ℝ) ≤ (-157888269748489174817055185270277/174425000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40839321/25000000000000 : ℝ)*(lower0) + (22213851/100000000000000 : ℝ)*(upper1) + (600729/4000000000000 : ℝ)*(lower2) + (855759/1000000000000 : ℝ)*(upper3) + (80396281/50000000000000 : ℝ)*(upper5) + (154779585091519/10000000000000 : ℝ)*(major0) + (154779585091519/10000000000000 : ℝ)*(major1) + (154779585091519/10000000000000 : ℝ)*(major2) + (1754380803/100000000000000 : ℝ)*(sp4) + (3378337169/10000000000000 : ℝ)*(sp5) + (1170594642942127/50000000000000 : ℝ)*(sp12) + (292644657111671/12500000000000 : ℝ)*(sp13) + (1170595520132529/50000000000000 : ℝ)*(sp14) + (98071719735187/12500000000000 : ℝ)*(sp15) + (98071719735187/12500000000000 : ℝ)*(f.failure) + (1170595520132529/50000000000000 : ℝ)*(f.sum) + (30133795943181/6977000000000000000000000000 : ℝ)*base66 + (6586020588568106759/697700000000000000000000000000000 : ℝ)*base67 + (5570463469815806759/697700000000000000000000000000000 : ℝ)*base69 + (98365933131006759/697700000000000000000000000000000 : ℝ)*base71 + (6342787910977/3488500000000000000000000000 : ℝ)*base73 + (1502931256622406759/697700000000000000000000000000000 : ℝ)*base75 + (1176911568585393241/697700000000000000000000000000000 : ℝ)*base78 + (1481883274658806759/697700000000000000000000000000000 : ℝ)*base79 + (109560640397/43606250000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (726669/250000000000000000000 : ℝ)*base90 + (726669/250000000000000000000 : ℝ)*base92 + (726669/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1717_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39455713/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8521/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2013/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66813/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29283/50000 : ℝ) else (40853/50000 : ℝ) ≤ X j i ∧ X j i ≤ (45261/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1717_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1717_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39455713/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10057/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66813/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29283/50000 : ℝ) else (40853/50000 : ℝ) ≤ X j i ∧ X j i ≤ (45261/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1717_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1717_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1717_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5351/1024 : ℝ) ≤ p) (hpb : p ≤ (5359/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39455713/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10057/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66813/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29283/50000 : ℝ) else (40853/50000 : ℝ) ≤ X j i ∧ X j i ≤ (45261/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1717_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
