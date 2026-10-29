-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1521_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:57:45.876552+00:00
-- url     : https://prove2.me/submissions/755d0f19-56b8-4de2-b647-ac2ffdab6fd2

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
theorem support_rectangle_w1521_s3_0 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-370871231/2000000000 : ℝ)*x 0 + (543501963/1000000000 : ℝ)*x 1 + (5215419103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (370871231/2000000000 : ℝ)^4539 ≤ (5675067864987/50000000000000 : ℝ)^3515 := by
    have hnat : (370871231 : ℕ)^4539*50000000000000^3515 ≤ 5675067864987^3515*2000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370871231 2000000000 5675067864987 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543501963/1000000000 : ℝ)^4539 ≤ (22752501010407/50000000000000 : ℝ)^3515 := by
    have hnat : (543501963 : ℕ)^4539*50000000000000^3515 ≤ 22752501010407^3515*1000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543501963 1000000000 22752501010407 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215419103/10000000000 : ℝ)^4539 ≤ (43144862241851/100000000000000 : ℝ)^3515 := by
    have hnat : (5215419103 : ℕ)^4539*100000000000000^3515 ≤ 43144862241851^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215419103 10000000000 43144862241851 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-370871231/2000000000 : ℝ), (543501963/1000000000 : ℝ), (5215419103/10000000000 : ℝ)] ![(5675067864987/50000000000000 : ℝ), (22752501010407/50000000000000 : ℝ), (43144862241851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-370871231/2000000000 : ℝ)|^4539 ≤ (5675067864987/50000000000000 : ℝ)^3515
        have hw : |(-370871231/2000000000 : ℝ)|=(370871231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543501963/1000000000 : ℝ)|^4539 ≤ (22752501010407/50000000000000 : ℝ)^3515
        have hw : |(543501963/1000000000 : ℝ)|=(543501963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215419103/10000000000 : ℝ)|^4539 ≤ (43144862241851/100000000000000 : ℝ)^3515
        have hw : |(5215419103/10000000000 : ℝ)|=(5215419103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s3_1 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214074397/400000000 : ℝ)*x 0 + (-1966873811/10000000000 : ℝ)*x 1 + (2607709689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214074397/400000000 : ℝ)^4539 ≤ (11151979416883/25000000000000 : ℝ)^3515 := by
    have hnat : (214074397 : ℕ)^4539*25000000000000^3515 ≤ 11151979416883^3515*400000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214074397 400000000 11151979416883 25000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1966873811/10000000000 : ℝ)^4539 ≤ (6123608567783/50000000000000 : ℝ)^3515 := by
    have hnat : (1966873811 : ℕ)^4539*50000000000000^3515 ≤ 6123608567783^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966873811 10000000000 6123608567783 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607709689/5000000000 : ℝ)^4539 ≤ (43144865179551/100000000000000 : ℝ)^3515 := by
    have hnat : (2607709689 : ℕ)^4539*100000000000000^3515 ≤ 43144865179551^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607709689 5000000000 43144865179551 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214074397/400000000 : ℝ), (-1966873811/10000000000 : ℝ), (2607709689/5000000000 : ℝ)] ![(11151979416883/25000000000000 : ℝ), (6123608567783/50000000000000 : ℝ), (43144865179551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214074397/400000000 : ℝ)|^4539 ≤ (11151979416883/25000000000000 : ℝ)^3515
        have hw : |(214074397/400000000 : ℝ)|=(214074397/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1966873811/10000000000 : ℝ)|^4539 ≤ (6123608567783/50000000000000 : ℝ)^3515
        have hw : |(-1966873811/10000000000 : ℝ)|=(1966873811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607709689/5000000000 : ℝ)|^4539 ≤ (43144865179551/100000000000000 : ℝ)^3515
        have hw : |(2607709689/5000000000 : ℝ)|=(2607709689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s3_2 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675929981/5000000000 : ℝ)*x 0 + (5215419303/10000000000 : ℝ)*x 1 + (-1966873861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675929981/5000000000 : ℝ)^4539 ≤ (44607918065771/100000000000000 : ℝ)^3515 := by
    have hnat : (2675929981 : ℕ)^4539*100000000000000^3515 ≤ 44607918065771^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675929981 5000000000 44607918065771 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215419303/10000000000 : ℝ)^4539 ≤ (1078621609459/2500000000000 : ℝ)^3515 := by
    have hnat : (5215419303 : ℕ)^4539*2500000000000^3515 ≤ 1078621609459^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215419303 10000000000 1078621609459 2500000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1966873861/10000000000 : ℝ)^4539 ≤ (6123608768801/50000000000000 : ℝ)^3515 := by
    have hnat : (1966873861 : ℕ)^4539*50000000000000^3515 ≤ 6123608768801^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966873861 10000000000 6123608768801 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675929981/5000000000 : ℝ), (5215419303/10000000000 : ℝ), (-1966873861/10000000000 : ℝ)] ![(44607918065771/100000000000000 : ℝ), (1078621609459/2500000000000 : ℝ), (6123608768801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675929981/5000000000 : ℝ)|^4539 ≤ (44607918065771/100000000000000 : ℝ)^3515
        have hw : |(2675929981/5000000000 : ℝ)|=(2675929981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215419303/10000000000 : ℝ)|^4539 ≤ (1078621609459/2500000000000 : ℝ)^3515
        have hw : |(5215419303/10000000000 : ℝ)|=(5215419303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1966873861/10000000000 : ℝ)|^4539 ≤ (6123608768801/50000000000000 : ℝ)^3515
        have hw : |(-1966873861/10000000000 : ℝ)|=(1966873861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s3_3 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (853063763/2000000000 : ℝ)*x 0 + (125654951/312500000 : ℝ)*x 1 + (141315037/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (853063763/2000000000 : ℝ)^4539 ≤ (8319321421247/25000000000000 : ℝ)^3515 := by
    have hnat : (853063763 : ℕ)^4539*25000000000000^3515 ≤ 8319321421247^3515*2000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853063763 2000000000 8319321421247 25000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125654951/312500000 : ℝ)^4539 ≤ (15418131090409/50000000000000 : ℝ)^3515 := by
    have hnat : (125654951 : ℕ)^4539*50000000000000^3515 ≤ 15418131090409^3515*312500000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125654951 312500000 15418131090409 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141315037/312500000 : ℝ)^4539 ≤ (7177290422723/20000000000000 : ℝ)^3515 := by
    have hnat : (141315037 : ℕ)^4539*20000000000000^3515 ≤ 7177290422723^3515*312500000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141315037 312500000 7177290422723 20000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(853063763/2000000000 : ℝ), (125654951/312500000 : ℝ), (141315037/312500000 : ℝ)] ![(8319321421247/25000000000000 : ℝ), (15418131090409/50000000000000 : ℝ), (7177290422723/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(853063763/2000000000 : ℝ)|^4539 ≤ (8319321421247/25000000000000 : ℝ)^3515
        have hw : |(853063763/2000000000 : ℝ)|=(853063763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(125654951/312500000 : ℝ)|^4539 ≤ (15418131090409/50000000000000 : ℝ)^3515
        have hw : |(125654951/312500000 : ℝ)|=(125654951/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(141315037/312500000 : ℝ)|^4539 ≤ (7177290422723/20000000000000 : ℝ)^3515
        have hw : |(141315037/312500000 : ℝ)|=(141315037/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s3_4 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1854386921/10000000000 : ℝ)*x 0 + (5216581119/10000000000 : ℝ)*x 1 + (2716924463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1854386921/10000000000 : ℝ)^4539 ≤ (11350378902689/100000000000000 : ℝ)^3515 := by
    have hnat : (1854386921 : ℕ)^4539*100000000000000^3515 ≤ 11350378902689^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1854386921 10000000000 11350378902689 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216581119/10000000000 : ℝ)^4539 ≤ (43157275932777/100000000000000 : ℝ)^3515 := by
    have hnat : (5216581119 : ℕ)^4539*100000000000000^3515 ≤ 43157275932777^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216581119 10000000000 43157275932777 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716924463/5000000000 : ℝ)^4539 ≤ (22746172574969/50000000000000 : ℝ)^3515 := by
    have hnat : (2716924463 : ℕ)^4539*50000000000000^3515 ≤ 22746172574969^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716924463 5000000000 22746172574969 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1854386921/10000000000 : ℝ), (5216581119/10000000000 : ℝ), (2716924463/5000000000 : ℝ)] ![(11350378902689/100000000000000 : ℝ), (43157275932777/100000000000000 : ℝ), (22746172574969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1854386921/10000000000 : ℝ)|^4539 ≤ (11350378902689/100000000000000 : ℝ)^3515
        have hw : |(-1854386921/10000000000 : ℝ)|=(1854386921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216581119/10000000000 : ℝ)|^4539 ≤ (43157275932777/100000000000000 : ℝ)^3515
        have hw : |(5216581119/10000000000 : ℝ)|=(5216581119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716924463/5000000000 : ℝ)|^4539 ≤ (22746172574969/50000000000000 : ℝ)^3515
        have hw : |(2716924463/5000000000 : ℝ)|=(2716924463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s3_5 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294134273/10000000000 : ℝ)*x 0 + (-1748443781/10000000000 : ℝ)*x 1 + (1086769767/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294134273/10000000000 : ℝ)^4539 ≤ (43987582647833/100000000000000 : ℝ)^3515 := by
    have hnat : (5294134273 : ℕ)^4539*100000000000000^3515 ≤ 43987582647833^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294134273 10000000000 43987582647833 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1748443781/10000000000 : ℝ)^4539 ≤ (10520073164871/100000000000000 : ℝ)^3515 := by
    have hnat : (1748443781 : ℕ)^4539*100000000000000^3515 ≤ 10520073164871^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1748443781 10000000000 10520073164871 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086769767/2000000000 : ℝ)^4539 ≤ (22746172083069/50000000000000 : ℝ)^3515 := by
    have hnat : (1086769767 : ℕ)^4539*50000000000000^3515 ≤ 22746172083069^3515*2000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086769767 2000000000 22746172083069 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294134273/10000000000 : ℝ), (-1748443781/10000000000 : ℝ), (1086769767/2000000000 : ℝ)] ![(43987582647833/100000000000000 : ℝ), (10520073164871/100000000000000 : ℝ), (22746172083069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294134273/10000000000 : ℝ)|^4539 ≤ (43987582647833/100000000000000 : ℝ)^3515
        have hw : |(5294134273/10000000000 : ℝ)|=(5294134273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1748443781/10000000000 : ℝ)|^4539 ≤ (10520073164871/100000000000000 : ℝ)^3515
        have hw : |(-1748443781/10000000000 : ℝ)|=(1748443781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086769767/2000000000 : ℝ)|^4539 ≤ (22746172083069/50000000000000 : ℝ)^3515
        have hw : |(1086769767/2000000000 : ℝ)|=(1086769767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s3_6 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529413417/1000000000 : ℝ)*x 0 + (679231109/1250000000 : ℝ)*x 1 + (-1748443873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529413417/1000000000 : ℝ)^4539 ≤ (21993790771359/50000000000000 : ℝ)^3515 := by
    have hnat : (529413417 : ℕ)^4539*50000000000000^3515 ≤ 21993790771359^3515*1000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529413417 1000000000 21993790771359 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679231109/1250000000 : ℝ)^4539 ≤ (9098468913229/20000000000000 : ℝ)^3515 := by
    have hnat : (679231109 : ℕ)^4539*20000000000000^3515 ≤ 9098468913229^3515*1250000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679231109 1250000000 9098468913229 20000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1748443873/10000000000 : ℝ)^4539 ≤ (16437615437/156250000000 : ℝ)^3515 := by
    have hnat : (1748443873 : ℕ)^4539*156250000000^3515 ≤ 16437615437^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1748443873 10000000000 16437615437 156250000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529413417/1000000000 : ℝ), (679231109/1250000000 : ℝ), (-1748443873/10000000000 : ℝ)] ![(21993790771359/50000000000000 : ℝ), (9098468913229/20000000000000 : ℝ), (16437615437/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529413417/1000000000 : ℝ)|^4539 ≤ (21993790771359/50000000000000 : ℝ)^3515
        have hw : |(529413417/1000000000 : ℝ)|=(529413417/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679231109/1250000000 : ℝ)|^4539 ≤ (9098468913229/20000000000000 : ℝ)^3515
        have hw : |(679231109/1250000000 : ℝ)|=(679231109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1748443873/10000000000 : ℝ)|^4539 ≤ (16437615437/156250000000 : ℝ)^3515
        have hw : |(-1748443873/10000000000 : ℝ)|=(1748443873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s3_7 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4265389403/10000000000 : ℝ)*x 0 + (2259714801/5000000000 : ℝ)*x 1 + (4023630007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4265389403/10000000000 : ℝ)^4539 ≤ (33277996838197/100000000000000 : ℝ)^3515 := by
    have hnat : (4265389403 : ℕ)^4539*100000000000000^3515 ≤ 33277996838197^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4265389403 10000000000 33277996838197 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2259714801/5000000000 : ℝ)^4539 ≤ (35859281779129/100000000000000 : ℝ)^3515 := by
    have hnat : (2259714801 : ℕ)^4539*100000000000000^3515 ≤ 35859281779129^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259714801 5000000000 35859281779129 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4023630007/10000000000 : ℝ)^4539 ≤ (30862721361521/100000000000000 : ℝ)^3515 := by
    have hnat : (4023630007 : ℕ)^4539*100000000000000^3515 ≤ 30862721361521^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023630007 10000000000 30862721361521 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4265389403/10000000000 : ℝ), (2259714801/5000000000 : ℝ), (4023630007/10000000000 : ℝ)] ![(33277996838197/100000000000000 : ℝ), (35859281779129/100000000000000 : ℝ), (30862721361521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4265389403/10000000000 : ℝ)|^4539 ≤ (33277996838197/100000000000000 : ℝ)^3515
        have hw : |(4265389403/10000000000 : ℝ)|=(4265389403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2259714801/5000000000 : ℝ)|^4539 ≤ (35859281779129/100000000000000 : ℝ)^3515
        have hw : |(2259714801/5000000000 : ℝ)|=(2259714801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4023630007/10000000000 : ℝ)|^4539 ≤ (30862721361521/100000000000000 : ℝ)^3515
        have hw : |(4023630007/10000000000 : ℝ)|=(4023630007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1521_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164098667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15963/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2627/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10893/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3109/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15963/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2627/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15963/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2627/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15963/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2627/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15963/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2627/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15963/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2627/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15963/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2627/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2627/25000 : ℝ) ^ (4537/1024 : ℝ) ≤ (288778016805617/6250000000000000000 : ℝ) := by
    have hpowers : (2627/25000 : ℝ)^4537 ≤ (288778016805617/6250000000000000000 : ℝ)^1024 := by
      have hnat : (2627 : ℕ)^4537*6250000000000000000^1024 ≤ 288778016805617^1024*25000^4537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2627 25000 288778016805617 6250000000000000000 4537 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2627/25000 : ℝ)) (X := (288778016805617/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15963/100000 : ℝ) ^ (4537/1024 : ℝ) ≤ (14731199735593171/50000000000000000000 : ℝ) := by
    have hpowers : (15963/100000 : ℝ)^4537 ≤ (14731199735593171/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15963 : ℕ)^4537*50000000000000000000^1024 ≤ 14731199735593171^1024*100000^4537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15963 100000 14731199735593171 50000000000000000000 4537 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15963/100000 : ℝ)) (X := (14731199735593171/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125288778016805617/3125000000000000000 : ℝ) ≤ (5000104279695119/5000000000000000 : ℝ) ^ (4537/1024 : ℝ) := by
    have hpowers : (3125288778016805617/3125000000000000000 : ℝ)^1024 ≤ (5000104279695119/5000000000000000 : ℝ)^4537 := by
      have hnat : (3125288778016805617 : ℕ)^1024*5000000000000000^4537 ≤ 5000104279695119^4537*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125288778016805617 3125000000000000000 5000104279695119 5000000000000000 1024 4537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000104279695119/5000000000000000 : ℝ)) (X := (3125288778016805617/3125000000000000000 : ℝ)) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017041423870038107/50000000000000000000 : ℝ) ≤ (2500192286928513/2500000000000000 : ℝ) ^ (4537/1024 : ℝ) := by
    have hpowers : (50017041423870038107/50000000000000000000 : ℝ)^1024 ≤ (2500192286928513/2500000000000000 : ℝ)^4537 := by
      have hnat : (50017041423870038107 : ℕ)^1024*2500000000000000^4537 ≤ 2500192286928513^4537*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017041423870038107 50000000000000000000 2500192286928513 2500000000000000 1024 4537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500192286928513/2500000000000000 : ℝ)) (X := (50017041423870038107/50000000000000000000 : ℝ)) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014731199735593171/25000000000000000000 : ℝ) ≤ (5000664868018933/5000000000000000 : ℝ) ^ (4537/1024 : ℝ) := by
    have hpowers : (25014731199735593171/25000000000000000000 : ℝ)^1024 ≤ (5000664868018933/5000000000000000 : ℝ)^4537 := by
      have hnat : (25014731199735593171 : ℕ)^1024*5000000000000000^4537 ≤ 5000664868018933^4537*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014731199735593171 25000000000000000000 5000664868018933 5000000000000000 1024 4537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000664868018933/5000000000000000 : ℝ)) (X := (25014731199735593171/25000000000000000000 : ℝ)) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(288778016805617/6250000000000000000 : ℝ) ≤ ((27269678183630236633/27275000000000000000 : ℝ)+2*(280294161907/272750000000000 : ℝ)*(2627/25000 : ℝ))^(4537/1024 : ℝ) := by
    rw [show (27269678183630236633/27275000000000000000 : ℝ)+2*(280294161907/272750000000000 : ℝ)*(2627/25000 : ℝ)=(5000104279695119/5000000000000000 : ℝ) by norm_num, show 1+2*(288778016805617/6250000000000000000 : ℝ)=(3125288778016805617/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14731199735593171/50000000000000000000 : ℝ)+(288778016805617/6250000000000000000 : ℝ) ≤ ((27269678183630236633/27275000000000000000 : ℝ)+(280294161907/272750000000000 : ℝ)*((15963/100000 : ℝ)+(2627/25000 : ℝ)))^(4537/1024 : ℝ) := by
    rw [show (27269678183630236633/27275000000000000000 : ℝ)+(280294161907/272750000000000 : ℝ)*((15963/100000 : ℝ)+(2627/25000 : ℝ))=(2500192286928513/2500000000000000 : ℝ) by norm_num, show 1+(14731199735593171/50000000000000000000 : ℝ)+(288778016805617/6250000000000000000 : ℝ)=(50017041423870038107/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14731199735593171/50000000000000000000 : ℝ) ≤ ((27269678183630236633/27275000000000000000 : ℝ)+2*(280294161907/272750000000000 : ℝ)*(15963/100000 : ℝ))^(4537/1024 : ℝ) := by
    rw [show (27269678183630236633/27275000000000000000 : ℝ)+2*(280294161907/272750000000000 : ℝ)*(15963/100000 : ℝ)=(5000664868018933/5000000000000000 : ℝ) by norm_num, show 1+2*(14731199735593171/50000000000000000000 : ℝ)=(25014731199735593171/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27269678183630236633/27275000000000000000 : ℝ)*(X 1 0+X 2 0)+(280294161907/272750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4537/1024 : ℝ)) (lo := (2627/25000 : ℝ)) (hi := (15963/100000 : ℝ)) (c := (27269678183630236633/27275000000000000000 : ℝ)) (alpha := (280294161907/272750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27269678183630236633/27275000000000000000 : ℝ)*(X 0 1+X 2 1)+(280294161907/272750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4537/1024 : ℝ)) (lo := (2627/25000 : ℝ)) (hi := (15963/100000 : ℝ)) (c := (27269678183630236633/27275000000000000000 : ℝ)) (alpha := (280294161907/272750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27269678183630236633/27275000000000000000 : ℝ)*(X 0 2+X 1 2)+(280294161907/272750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4537/1024 : ℝ)) (lo := (2627/25000 : ℝ)) (hi := (15963/100000 : ℝ)) (c := (27269678183630236633/27275000000000000000 : ℝ)) (alpha := (280294161907/272750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-370871231/2000000000 : ℝ)*X 0 0+(543501963/1000000000 : ℝ)*X 0 1+(5215419103/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((214074397/400000000 : ℝ)*X 1 0+(-1966873811/10000000000 : ℝ)*X 1 1+(2607709689/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675929981/5000000000 : ℝ)*X 2 0+(5215419303/10000000000 : ℝ)*X 2 1+(-1966873861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((853063763/2000000000 : ℝ)*X 0 0+(125654951/312500000 : ℝ)*X 0 1+(141315037/312500000 : ℝ)*X 0 2+(853063763/2000000000 : ℝ)*X 1 0+(125654951/312500000 : ℝ)*X 1 1+(141315037/312500000 : ℝ)*X 1 2+(853063763/2000000000 : ℝ)*X 2 0+(125654951/312500000 : ℝ)*X 2 1+(141315037/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1854386921/10000000000 : ℝ)*X 0 0+(5216581119/10000000000 : ℝ)*X 0 1+(2716924463/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294134273/10000000000 : ℝ)*X 1 0+(-1748443781/10000000000 : ℝ)*X 1 1+(1086769767/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((529413417/1000000000 : ℝ)*X 2 0+(679231109/1250000000 : ℝ)*X 2 1+(-1748443873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4265389403/10000000000 : ℝ)*X 0 0+(2259714801/5000000000 : ℝ)*X 0 1+(4023630007/10000000000 : ℝ)*X 0 2+(4265389403/10000000000 : ℝ)*X 1 0+(2259714801/5000000000 : ℝ)*X 1 1+(4023630007/10000000000 : ℝ)*X 1 2+(4265389403/10000000000 : ℝ)*X 2 0+(2259714801/5000000000 : ℝ)*X 2 1+(4023630007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13883699933994348304806451731/1363750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (405642927/25000000000000 : ℝ)*(base19) + (307915547/20000000000000 : ℝ)*(base23) + (30633093/50000000000000 : ℝ)*(lower2) + (63527823/20000000000000 : ℝ)*(upper3) + (95444279/50000000000000 : ℝ)*(upper5) + (3274661719117123/100000000000000 : ℝ)*(major0) + (3274661719117123/100000000000000 : ℝ)*(major1) + (3274661719117123/100000000000000 : ℝ)*(major2) + (2276875995475711/50000000000000 : ℝ)*(sp0) + (4553777101099017/100000000000000 : ℝ)*(sp1) + (4553777184092989/100000000000000 : ℝ)*(sp2) + (399106153542131/20000000000000 : ℝ)*(sp3) + (13366359651/50000000000000 : ℝ)*(sp4) + (3401875451/25000000000000 : ℝ)*(sp7) + (1995544375212459/100000000000000 : ℝ)*(f.failure) + (182151148946829/4000000000000 : ℝ)*(f.sum) + (27268645581253/27275000000000000000000000000 : ℝ)*base66 + (28413544152076733141/2727500000000000000000000000000000 : ℝ)*base68 + (14961962825826733141/2727500000000000000000000000000000 : ℝ)*base70 + (16920903228166733141/2727500000000000000000000000000000 : ℝ)*base72 + (46951537394653/27275000000000000000000000000 : ℝ)*base74 + (44098665158396733141/2727500000000000000000000000000000 : ℝ)*base76 + (40308704848324233141/2727500000000000000000000000000000 : ℝ)*base78 + (23207002679774233141/2727500000000000000000000000000000 : ℝ)*base80 + (127989318758897/27275000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (63692153/10000000000000000000000 : ℝ)*base89 + (63692153/10000000000000000000000 : ℝ)*base91 + (63692153/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6609505627182024252143022003/681875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5233967/250000000000 : ℝ)*(base19) + (2287723277/100000000000000 : ℝ)*(base23) + (238560089/100000000000000 : ℝ)*(upper3) + (135029573/100000000000000 : ℝ)*(lower4) + (200949067/100000000000000 : ℝ)*(upper5) + (1654888613106099/50000000000000 : ℝ)*(major0) + (1654888613106099/50000000000000 : ℝ)*(major1) + (1654888613106099/50000000000000 : ℝ)*(major2) + (7731552599/25000000000000 : ℝ)*(sp1) + (838790213/2500000000000 : ℝ)*(sp2) + (2301305366894071/50000000000000 : ℝ)*(sp4) + (4602577713990947/100000000000000 : ℝ)*(sp5) + (920514978891269/20000000000000 : ℝ)*(sp6) + (1008471697765893/50000000000000 : ℝ)*(sp7) + (1008471697765893/50000000000000 : ℝ)*(f.failure) + (2301305366894071/50000000000000 : ℝ)*(f.sum) + (13653956940693/6818750000000000000000000000 : ℝ)*base65 + (17109790083877675333/1363750000000000000000000000000000 : ℝ)*base68 + (11427750152732675333/1363750000000000000000000000000000 : ℝ)*base70 + (13204488104163925333/1363750000000000000000000000000000 : ℝ)*base72 + (70717336697303/27275000000000000000000000000 : ℝ)*base74 + (12302888903521425333/1363750000000000000000000000000000 : ℝ)*base76 + (4924722807125175333/1363750000000000000000000000000000 : ℝ)*base78 + (9384778434730175333/1363750000000000000000000000000000 : ℝ)*base80 + (80434080349997/27275000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (19364631/5000000000000000000000 : ℝ)*base89 + (19364631/5000000000000000000000 : ℝ)*base91 + (19364631/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1521_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164098667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15963/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2627/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10893/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3109/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1521_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1521_s4_0 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-927375181/5000000000 : ℝ)*x 0 + (5432414523/10000000000 : ℝ)*x 1 + (2608881841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (927375181/5000000000 : ℝ)^4539 ≤ (5676625804319/50000000000000 : ℝ)^3515 := by
    have hnat : (927375181 : ℕ)^4539*50000000000000^3515 ≤ 5676625804319^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      927375181 5000000000 5676625804319 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432414523/10000000000 : ℝ)^4539 ≤ (22738419212141/50000000000000 : ℝ)^3515 := by
    have hnat : (5432414523 : ℕ)^4539*50000000000000^3515 ≤ 22738419212141^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432414523 10000000000 22738419212141 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608881841/5000000000 : ℝ)^4539 ≤ (43169909952163/100000000000000 : ℝ)^3515 := by
    have hnat : (2608881841 : ℕ)^4539*100000000000000^3515 ≤ 43169909952163^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608881841 5000000000 43169909952163 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-927375181/5000000000 : ℝ), (5432414523/10000000000 : ℝ), (2608881841/5000000000 : ℝ)] ![(5676625804319/50000000000000 : ℝ), (22738419212141/50000000000000 : ℝ), (43169909952163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-927375181/5000000000 : ℝ)|^4539 ≤ (5676625804319/50000000000000 : ℝ)^3515
        have hw : |(-927375181/5000000000 : ℝ)|=(927375181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432414523/10000000000 : ℝ)|^4539 ≤ (22738419212141/50000000000000 : ℝ)^3515
        have hw : |(5432414523/10000000000 : ℝ)|=(5432414523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608881841/5000000000 : ℝ)|^4539 ≤ (43169909952163/100000000000000 : ℝ)^3515
        have hw : |(2608881841/5000000000 : ℝ)|=(2608881841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s4_1 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (21404707/40000000 : ℝ)*x 0 + (-1964672527/10000000000 : ℝ)*x 1 + (5217764179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21404707/40000000 : ℝ)^4539 ≤ (22300282322001/50000000000000 : ℝ)^3515 := by
    have hnat : (21404707 : ℕ)^4539*50000000000000^3515 ≤ 22300282322001^3515*40000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21404707 40000000 22300282322001 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1964672527/10000000000 : ℝ)^4539 ≤ (12229520079509/100000000000000 : ℝ)^3515 := by
    have hnat : (1964672527 : ℕ)^4539*100000000000000^3515 ≤ 12229520079509^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1964672527 10000000000 12229520079509 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217764179/10000000000 : ℝ)^4539 ≤ (43169915262083/100000000000000 : ℝ)^3515 := by
    have hnat : (5217764179 : ℕ)^4539*100000000000000^3515 ≤ 43169915262083^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217764179 10000000000 43169915262083 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21404707/40000000 : ℝ), (-1964672527/10000000000 : ℝ), (5217764179/10000000000 : ℝ)] ![(22300282322001/50000000000000 : ℝ), (12229520079509/100000000000000 : ℝ), (43169915262083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21404707/40000000 : ℝ)|^4539 ≤ (22300282322001/50000000000000 : ℝ)^3515
        have hw : |(21404707/40000000 : ℝ)|=(21404707/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1964672527/10000000000 : ℝ)|^4539 ≤ (12229520079509/100000000000000 : ℝ)^3515
        have hw : |(-1964672527/10000000000 : ℝ)|=(1964672527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217764179/10000000000 : ℝ)|^4539 ≤ (43169915262083/100000000000000 : ℝ)^3515
        have hw : |(5217764179/10000000000 : ℝ)|=(5217764179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s4_2 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337794213/2500000000 : ℝ)*x 0 + (2608882009/5000000000 : ℝ)*x 1 + (-491168151/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337794213/2500000000 : ℝ)^4539 ≤ (44600565741809/100000000000000 : ℝ)^3515 := by
    have hnat : (1337794213 : ℕ)^4539*100000000000000^3515 ≤ 44600565741809^3515*2500000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337794213 2500000000 44600565741809 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608882009/5000000000 : ℝ)^4539 ≤ (2698119596373/6250000000000 : ℝ)^3515 := by
    have hnat : (2608882009 : ℕ)^4539*6250000000000^3515 ≤ 2698119596373^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608882009 5000000000 2698119596373 6250000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (491168151/2500000000 : ℝ)^4539 ≤ (12229520698443/100000000000000 : ℝ)^3515 := by
    have hnat : (491168151 : ℕ)^4539*100000000000000^3515 ≤ 12229520698443^3515*2500000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491168151 2500000000 12229520698443 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337794213/2500000000 : ℝ), (2608882009/5000000000 : ℝ), (-491168151/2500000000 : ℝ)] ![(44600565741809/100000000000000 : ℝ), (2698119596373/6250000000000 : ℝ), (12229520698443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337794213/2500000000 : ℝ)|^4539 ≤ (44600565741809/100000000000000 : ℝ)^3515
        have hw : |(1337794213/2500000000 : ℝ)|=(1337794213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608882009/5000000000 : ℝ)|^4539 ≤ (2698119596373/6250000000000 : ℝ)^3515
        have hw : |(2608882009/5000000000 : ℝ)|=(2608882009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-491168151/2500000000 : ℝ)|^4539 ≤ (12229520698443/100000000000000 : ℝ)^3515
        have hw : |(-491168151/2500000000 : ℝ)|=(491168151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s4_3 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (853113241/2000000000 : ℝ)*x 0 + (2013289241/5000000000 : ℝ)*x 1 + (2258202411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (853113241/2000000000 : ℝ)^4539 ≤ (33279778081069/100000000000000 : ℝ)^3515 := by
    have hnat : (853113241 : ℕ)^4539*100000000000000^3515 ≤ 33279778081069^3515*2000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853113241 2000000000 33279778081069 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2013289241/5000000000 : ℝ)^4539 ≤ (30891928891323/100000000000000 : ℝ)^3515 := by
    have hnat : (2013289241 : ℕ)^4539*100000000000000^3515 ≤ 30891928891323^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013289241 5000000000 30891928891323 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2258202411/5000000000 : ℝ)^4539 ≤ (35828293014773/100000000000000 : ℝ)^3515 := by
    have hnat : (2258202411 : ℕ)^4539*100000000000000^3515 ≤ 35828293014773^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258202411 5000000000 35828293014773 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(853113241/2000000000 : ℝ), (2013289241/5000000000 : ℝ), (2258202411/5000000000 : ℝ)] ![(33279778081069/100000000000000 : ℝ), (30891928891323/100000000000000 : ℝ), (35828293014773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(853113241/2000000000 : ℝ)|^4539 ≤ (33279778081069/100000000000000 : ℝ)^3515
        have hw : |(853113241/2000000000 : ℝ)|=(853113241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2013289241/5000000000 : ℝ)|^4539 ≤ (30891928891323/100000000000000 : ℝ)^3515
        have hw : |(2013289241/5000000000 : ℝ)|=(2013289241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2258202411/5000000000 : ℝ)|^4539 ≤ (35828293014773/100000000000000 : ℝ)^3515
        have hw : |(2258202411/5000000000 : ℝ)|=(2258202411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s4_4 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1854779261/10000000000 : ℝ)*x 0 + (2609437041/5000000000 : ℝ)*x 1 + (5431295889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1854779261/10000000000 : ℝ)^4539 ≤ (5676740019401/50000000000000 : ℝ)^3515 := by
    have hnat : (1854779261 : ℕ)^4539*50000000000000^3515 ≤ 5676740019401^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1854779261 10000000000 5676740019401 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609437041/5000000000 : ℝ)^4539 ≤ (43181773770971/100000000000000 : ℝ)^3515 := by
    have hnat : (2609437041 : ℕ)^4539*100000000000000^3515 ≤ 43181773770971^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609437041 5000000000 43181773770971 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431295889/10000000000 : ℝ)^4539 ≤ (2841546635741/6250000000000 : ℝ)^3515 := by
    have hnat : (5431295889 : ℕ)^4539*6250000000000^3515 ≤ 2841546635741^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431295889 10000000000 2841546635741 6250000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1854779261/10000000000 : ℝ), (2609437041/5000000000 : ℝ), (5431295889/10000000000 : ℝ)] ![(5676740019401/50000000000000 : ℝ), (43181773770971/100000000000000 : ℝ), (2841546635741/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1854779261/10000000000 : ℝ)|^4539 ≤ (5676740019401/50000000000000 : ℝ)^3515
        have hw : |(-1854779261/10000000000 : ℝ)|=(1854779261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609437041/5000000000 : ℝ)|^4539 ≤ (43181773770971/100000000000000 : ℝ)^3515
        have hw : |(2609437041/5000000000 : ℝ)|=(2609437041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431295889/10000000000 : ℝ)|^4539 ≤ (2841546635741/6250000000000 : ℝ)^3515
        have hw : |(5431295889/10000000000 : ℝ)|=(5431295889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s4_5 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323688367/2500000000 : ℝ)*x 0 + (-14009121/80000000 : ℝ)*x 1 + (5431295889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323688367/2500000000 : ℝ)^4539 ≤ (43994226268639/100000000000000 : ℝ)^3515 := by
    have hnat : (1323688367 : ℕ)^4539*100000000000000^3515 ≤ 43994226268639^3515*2500000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323688367 2500000000 43994226268639 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (14009121/80000000 : ℝ)^4539 ≤ (10541027541663/100000000000000 : ℝ)^3515 := by
    have hnat : (14009121 : ℕ)^4539*100000000000000^3515 ≤ 10541027541663^3515*80000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14009121 80000000 10541027541663 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431295889/10000000000 : ℝ)^4539 ≤ (2841546635741/6250000000000 : ℝ)^3515 := by
    have hnat : (5431295889 : ℕ)^4539*6250000000000^3515 ≤ 2841546635741^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431295889 10000000000 2841546635741 6250000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323688367/2500000000 : ℝ), (-14009121/80000000 : ℝ), (5431295889/10000000000 : ℝ)] ![(43994226268639/100000000000000 : ℝ), (10541027541663/100000000000000 : ℝ), (2841546635741/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323688367/2500000000 : ℝ)|^4539 ≤ (43994226268639/100000000000000 : ℝ)^3515
        have hw : |(1323688367/2500000000 : ℝ)|=(1323688367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-14009121/80000000 : ℝ)|^4539 ≤ (10541027541663/100000000000000 : ℝ)^3515
        have hw : |(-14009121/80000000 : ℝ)|=(14009121/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431295889/10000000000 : ℝ)|^4539 ≤ (2841546635741/6250000000000 : ℝ)^3515
        have hw : |(5431295889/10000000000 : ℝ)|=(5431295889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s4_6 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647376741/5000000000 : ℝ)*x 0 + (2715647941/5000000000 : ℝ)*x 1 + (-437785029/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647376741/5000000000 : ℝ)^4539 ≤ (21997113209427/50000000000000 : ℝ)^3515 := by
    have hnat : (2647376741 : ℕ)^4539*50000000000000^3515 ≤ 21997113209427^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647376741 5000000000 21997113209427 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715647941/5000000000 : ℝ)^4539 ≤ (4546474609619/10000000000000 : ℝ)^3515 := by
    have hnat : (2715647941 : ℕ)^4539*10000000000000^3515 ≤ 4546474609619^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715647941 5000000000 4546474609619 10000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (437785029/2500000000 : ℝ)^4539 ≤ (2108205494341/20000000000000 : ℝ)^3515 := by
    have hnat : (437785029 : ℕ)^4539*20000000000000^3515 ≤ 2108205494341^3515*2500000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437785029 2500000000 2108205494341 20000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647376741/5000000000 : ℝ), (2715647941/5000000000 : ℝ), (-437785029/2500000000 : ℝ)] ![(21997113209427/50000000000000 : ℝ), (4546474609619/10000000000000 : ℝ), (2108205494341/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647376741/5000000000 : ℝ)|^4539 ≤ (21997113209427/50000000000000 : ℝ)^3515
        have hw : |(2647376741/5000000000 : ℝ)|=(2647376741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715647941/5000000000 : ℝ)|^4539 ≤ (4546474609619/10000000000000 : ℝ)^3515
        have hw : |(2715647941/5000000000 : ℝ)|=(2715647941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-437785029/2500000000 : ℝ)|^4539 ≤ (2108205494341/20000000000000 : ℝ)^3515
        have hw : |(-437785029/2500000000 : ℝ)|=(437785029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s4_7 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (533204033/1250000000 : ℝ)*x 0 + (4513871353/10000000000 : ℝ)*x 1 + (1007282621/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533204033/1250000000 : ℝ)^4539 ≤ (6656088723417/20000000000000 : ℝ)^3515 := by
    have hnat : (533204033 : ℕ)^4539*20000000000000^3515 ≤ 6656088723417^3515*1250000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533204033 1250000000 6656088723417 20000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4513871353/10000000000 : ℝ)^4539 ≤ (8950585591629/25000000000000 : ℝ)^3515 := by
    have hnat : (4513871353 : ℕ)^4539*25000000000000^3515 ≤ 8950585591629^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513871353 10000000000 8950585591629 25000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1007282621/2500000000 : ℝ)^4539 ≤ (30917213999009/100000000000000 : ℝ)^3515 := by
    have hnat : (1007282621 : ℕ)^4539*100000000000000^3515 ≤ 30917213999009^3515*2500000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007282621 2500000000 30917213999009 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(533204033/1250000000 : ℝ), (4513871353/10000000000 : ℝ), (1007282621/2500000000 : ℝ)] ![(6656088723417/20000000000000 : ℝ), (8950585591629/25000000000000 : ℝ), (30917213999009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(533204033/1250000000 : ℝ)|^4539 ≤ (6656088723417/20000000000000 : ℝ)^3515
        have hw : |(533204033/1250000000 : ℝ)|=(533204033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4513871353/10000000000 : ℝ)|^4539 ≤ (8950585591629/25000000000000 : ℝ)^3515
        have hw : |(4513871353/10000000000 : ℝ)|=(4513871353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1007282621/2500000000 : ℝ)|^4539 ≤ (30917213999009/100000000000000 : ℝ)^3515
        have hw : |(1007282621/2500000000 : ℝ)|=(1007282621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1521_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164098667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3109/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10893/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10943/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3109/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10893/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3109/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10893/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3109/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10893/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3109/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10893/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3109/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10893/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3109/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10893/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10893/100000 : ℝ) ^ (4537/1024 : ℝ) ≤ (135476527231467/2500000000000000000 : ℝ) := by
    have hpowers : (10893/100000 : ℝ)^4537 ≤ (135476527231467/2500000000000000000 : ℝ)^1024 := by
      have hnat : (10893 : ℕ)^4537*2500000000000000000^1024 ≤ 135476527231467^1024*100000^4537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10893 100000 135476527231467 2500000000000000000 4537 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10893/100000 : ℝ)) (X := (135476527231467/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3109/20000 : ℝ) ^ (4537/1024 : ℝ) ≤ (6548624555423927/25000000000000000000 : ℝ) := by
    have hpowers : (3109/20000 : ℝ)^4537 ≤ (6548624555423927/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3109 : ℕ)^4537*25000000000000000000^1024 ≤ 6548624555423927^1024*20000^4537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3109 20000 6548624555423927 25000000000000000000 4537 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3109/20000 : ℝ)) (X := (6548624555423927/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250135476527231467/1250000000000000000 : ℝ) ≤ (5000122302969593/5000000000000000 : ℝ) ^ (4537/1024 : ℝ) := by
    have hpowers : (1250135476527231467/1250000000000000000 : ℝ)^1024 ≤ (5000122302969593/5000000000000000 : ℝ)^4537 := by
      have hnat : (1250135476527231467 : ℕ)^1024*5000000000000000^4537 ≤ 5000122302969593^4537*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250135476527231467 1250000000000000000 5000122302969593 5000000000000000 1024 4537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000122302969593/5000000000000000 : ℝ)) (X := (1250135476527231467/1250000000000000000 : ℝ)) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25007903389827738597/25000000000000000000 : ℝ) ≤ (10000713430094089/10000000000000000 : ℝ) ^ (4537/1024 : ℝ) := by
    have hpowers : (25007903389827738597/25000000000000000000 : ℝ)^1024 ≤ (10000713430094089/10000000000000000 : ℝ)^4537 := by
      have hnat : (25007903389827738597 : ℕ)^1024*10000000000000000^4537 ≤ 10000713430094089^4537*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007903389827738597 25000000000000000000 10000713430094089 10000000000000000 1024 4537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000713430094089/10000000000000000 : ℝ)) (X := (25007903389827738597/25000000000000000000 : ℝ)) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506548624555423927/12500000000000000000 : ℝ) ≤ (312536945445281/312500000000000 : ℝ) ^ (4537/1024 : ℝ) := by
    have hpowers : (12506548624555423927/12500000000000000000 : ℝ)^1024 ≤ (312536945445281/312500000000000 : ℝ)^4537 := by
      have hnat : (12506548624555423927 : ℕ)^1024*312500000000000^4537 ≤ 312536945445281^4537*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506548624555423927 12500000000000000000 312536945445281 312500000000000 1024 4537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312536945445281/312500000000000 : ℝ)) (X := (12506548624555423927/12500000000000000000 : ℝ)) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(135476527231467/2500000000000000000 : ℝ) ≤ ((23255462051895188257/23260000000000000000 : ℝ)+2*(468824154903/465200000000000 : ℝ)*(10893/100000 : ℝ))^(4537/1024 : ℝ) := by
    rw [show (23255462051895188257/23260000000000000000 : ℝ)+2*(468824154903/465200000000000 : ℝ)*(10893/100000 : ℝ)=(5000122302969593/5000000000000000 : ℝ) by norm_num, show 1+2*(135476527231467/2500000000000000000 : ℝ)=(1250135476527231467/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6548624555423927/25000000000000000000 : ℝ)+(135476527231467/2500000000000000000 : ℝ) ≤ ((23255462051895188257/23260000000000000000 : ℝ)+(468824154903/465200000000000 : ℝ)*((3109/20000 : ℝ)+(10893/100000 : ℝ)))^(4537/1024 : ℝ) := by
    rw [show (23255462051895188257/23260000000000000000 : ℝ)+(468824154903/465200000000000 : ℝ)*((3109/20000 : ℝ)+(10893/100000 : ℝ))=(10000713430094089/10000000000000000 : ℝ) by norm_num, show 1+(6548624555423927/25000000000000000000 : ℝ)+(135476527231467/2500000000000000000 : ℝ)=(25007903389827738597/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6548624555423927/25000000000000000000 : ℝ) ≤ ((23255462051895188257/23260000000000000000 : ℝ)+2*(468824154903/465200000000000 : ℝ)*(3109/20000 : ℝ))^(4537/1024 : ℝ) := by
    rw [show (23255462051895188257/23260000000000000000 : ℝ)+2*(468824154903/465200000000000 : ℝ)*(3109/20000 : ℝ)=(312536945445281/312500000000000 : ℝ) by norm_num, show 1+2*(6548624555423927/25000000000000000000 : ℝ)=(12506548624555423927/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23255462051895188257/23260000000000000000 : ℝ)*(X 1 0+X 2 0)+(468824154903/465200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4537/1024 : ℝ)) (lo := (10893/100000 : ℝ)) (hi := (3109/20000 : ℝ)) (c := (23255462051895188257/23260000000000000000 : ℝ)) (alpha := (468824154903/465200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23255462051895188257/23260000000000000000 : ℝ)*(X 0 1+X 2 1)+(468824154903/465200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4537/1024 : ℝ)) (lo := (10893/100000 : ℝ)) (hi := (3109/20000 : ℝ)) (c := (23255462051895188257/23260000000000000000 : ℝ)) (alpha := (468824154903/465200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23255462051895188257/23260000000000000000 : ℝ)*(X 0 2+X 1 2)+(468824154903/465200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4537/1024 : ℝ)) (lo := (10893/100000 : ℝ)) (hi := (3109/20000 : ℝ)) (c := (23255462051895188257/23260000000000000000 : ℝ)) (alpha := (468824154903/465200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-927375181/5000000000 : ℝ)*X 0 0+(5432414523/10000000000 : ℝ)*X 0 1+(2608881841/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((21404707/40000000 : ℝ)*X 1 0+(-1964672527/10000000000 : ℝ)*X 1 1+(5217764179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337794213/2500000000 : ℝ)*X 2 0+(2608882009/5000000000 : ℝ)*X 2 1+(-491168151/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((853113241/2000000000 : ℝ)*X 0 0+(2013289241/5000000000 : ℝ)*X 0 1+(2258202411/5000000000 : ℝ)*X 0 2+(853113241/2000000000 : ℝ)*X 1 0+(2013289241/5000000000 : ℝ)*X 1 1+(2258202411/5000000000 : ℝ)*X 1 2+(853113241/2000000000 : ℝ)*X 2 0+(2013289241/5000000000 : ℝ)*X 2 1+(2258202411/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1854779261/10000000000 : ℝ)*X 0 0+(2609437041/5000000000 : ℝ)*X 0 1+(5431295889/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323688367/2500000000 : ℝ)*X 1 0+(-14009121/80000000 : ℝ)*X 1 1+(5431295889/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647376741/5000000000 : ℝ)*X 2 0+(2715647941/5000000000 : ℝ)*X 2 1+(-437785029/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((533204033/1250000000 : ℝ)*X 0 0+(4513871353/10000000000 : ℝ)*X 0 1+(1007282621/2500000000 : ℝ)*X 0 2+(533204033/1250000000 : ℝ)*X 1 0+(4513871353/10000000000 : ℝ)*X 1 1+(1007282621/2500000000 : ℝ)*X 1 2+(533204033/1250000000 : ℝ)*X 2 0+(4513871353/10000000000 : ℝ)*X 2 1+(1007282621/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (344133237759491504644323/23260000000000000000000000000 : ℝ) := by norm_num
    linear_combination (329214527/25000000000000 : ℝ)*(base19) + (634530031/50000000000000 : ℝ)*(base23) + (73097107/100000000000000 : ℝ)*(lower2) + (89386597/25000000000000 : ℝ)*(upper3) + (197502187/100000000000000 : ℝ)*(upper5) + (3350167985139833/100000000000000 : ℝ)*(major0) + (3350167985139833/100000000000000 : ℝ)*(major1) + (3350167985139833/100000000000000 : ℝ)*(major2) + (4658754787160213/100000000000000 : ℝ)*(sp0) + (931755412294783/20000000000000 : ℝ)*(sp1) + (4658777109271961/100000000000000 : ℝ)*(sp2) + (2041547259124401/100000000000000 : ℝ)*(sp3) + (2359117181/10000000000000 : ℝ)*(sp4) + (307489199/3125000000000 : ℝ)*(sp7) + (2041557098778769/100000000000000 : ℝ)*(f.failure) + (4658778378332023/100000000000000 : ℝ)*(f.sum) + (76584880569539/23260000000000000000000000000 : ℝ)*base65 + (124717691934491081/2326000000000000000000000000000000 : ℝ)*base67 + (2107799966224491081/2326000000000000000000000000000000 : ℝ)*base69 + (7097309020317508919/2326000000000000000000000000000000 : ℝ)*base72 + (104387412766861/23260000000000000000000000000 : ℝ)*base74 + (14121672973629508919/2326000000000000000000000000000000 : ℝ)*base76 + (21753533145510491081/2326000000000000000000000000000000 : ℝ)*base77 + (9260919044219508919/2326000000000000000000000000000000 : ℝ)*base80 + (65221406465799/23260000000000000000000000000 : ℝ)*base81 + (20800923/10000000000000000000000 : ℝ)*base89 + (20800923/10000000000000000000000 : ℝ)*base91 + (20800923/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (622287072698806110296436627/145375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (85844543/12500000000000 : ℝ)*(base19) + (38448757/5000000000000 : ℝ)*(base23) + (43674533/50000000000000 : ℝ)*(upper3) + (3882427/12500000000000 : ℝ)*(lower4) + (23315439/25000000000000 : ℝ)*(upper5) + (423160759278137/12500000000000 : ℝ)*(major0) + (423160759278137/12500000000000 : ℝ)*(major1) + (423160759278137/12500000000000 : ℝ)*(major2) + (5301544833/50000000000000 : ℝ)*(sp1) + (11645682023/100000000000000 : ℝ)*(sp2) + (470761431322897/10000000000000 : ℝ)*(sp4) + (58845037792287/1250000000000 : ℝ)*(sp5) + (2353800949285903/50000000000000 : ℝ)*(sp6) + (2062957692535733/100000000000000 : ℝ)*(sp7) + (2062957692535733/100000000000000 : ℝ)*(f.failure) + (470761431322897/10000000000000 : ℝ)*(f.sum) + (2642247836827/1453750000000000000000000000 : ℝ)*base66 + (286870956201962791/290750000000000000000000000000000 : ℝ)*base68 + (585755214581712791/290750000000000000000000000000000 : ℝ)*base70 + (516315738074212791/290750000000000000000000000000000 : ℝ)*base72 + (18449377148683/5815000000000000000000000000 : ℝ)*base74 + (1871981264534712791/290750000000000000000000000000000 : ℝ)*base76 + (513204045624787209/290750000000000000000000000000000 : ℝ)*base77 + (1160076724833537209/290750000000000000000000000000000 : ℝ)*base79 + (4864998788269/2907500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (35167911/10000000000000000000000 : ℝ)*base89 + (35167911/10000000000000000000000 : ℝ)*base91 + (35167911/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1521_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164098667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3109/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10893/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10943/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1521_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1521_s5_0 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-463699791/2500000000 : ℝ)*x 0 + (2716050601/5000000000 : ℝ)*x 1 + (5218044593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (463699791/2500000000 : ℝ)^4539 ≤ (1419204670163/12500000000000 : ℝ)^3515 := by
    have hnat : (463699791 : ℕ)^4539*12500000000000^3515 ≤ 1419204670163^3515*2500000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463699791 2500000000 1419204670163 12500000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716050601/5000000000 : ℝ)^4539 ≤ (45473451401859/100000000000000 : ℝ)^3515 := by
    have hnat : (2716050601 : ℕ)^4539*100000000000000^3515 ≤ 45473451401859^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716050601 5000000000 45473451401859 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218044593/10000000000 : ℝ)^4539 ≤ (8634582242601/20000000000000 : ℝ)^3515 := by
    have hnat : (5218044593 : ℕ)^4539*20000000000000^3515 ≤ 8634582242601^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218044593 10000000000 8634582242601 20000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-463699791/2500000000 : ℝ), (2716050601/5000000000 : ℝ), (5218044593/10000000000 : ℝ)] ![(1419204670163/12500000000000 : ℝ), (45473451401859/100000000000000 : ℝ), (8634582242601/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-463699791/2500000000 : ℝ)|^4539 ≤ (1419204670163/12500000000000 : ℝ)^3515
        have hw : |(-463699791/2500000000 : ℝ)|=(463699791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716050601/5000000000 : ℝ)|^4539 ≤ (45473451401859/100000000000000 : ℝ)^3515
        have hw : |(2716050601/5000000000 : ℝ)|=(2716050601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218044593/10000000000 : ℝ)|^4539 ≤ (8634582242601/20000000000000 : ℝ)^3515
        have hw : |(5218044593/10000000000 : ℝ)|=(5218044593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s5_1 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535109471/1000000000 : ℝ)*x 0 + (-49110241/250000000 : ℝ)*x 1 + (5218044603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535109471/1000000000 : ℝ)^4539 ≤ (5574960208069/12500000000000 : ℝ)^3515 := by
    have hnat : (535109471 : ℕ)^4539*12500000000000^3515 ≤ 5574960208069^3515*1000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535109471 1000000000 5574960208069 12500000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49110241/250000000 : ℝ)^4539 ≤ (611370350267/5000000000000 : ℝ)^3515 := by
    have hnat : (49110241 : ℕ)^4539*5000000000000^3515 ≤ 611370350267^3515*250000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49110241 250000000 611370350267 5000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218044603/10000000000 : ℝ)^4539 ≤ (43172911319847/100000000000000 : ℝ)^3515 := by
    have hnat : (5218044603 : ℕ)^4539*100000000000000^3515 ≤ 43172911319847^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218044603 10000000000 43172911319847 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535109471/1000000000 : ℝ), (-49110241/250000000 : ℝ), (5218044603/10000000000 : ℝ)] ![(5574960208069/12500000000000 : ℝ), (611370350267/5000000000000 : ℝ), (43172911319847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535109471/1000000000 : ℝ)|^4539 ≤ (5574960208069/12500000000000 : ℝ)^3515
        have hw : |(535109471/1000000000 : ℝ)|=(535109471/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-49110241/250000000 : ℝ)|^4539 ≤ (611370350267/5000000000000 : ℝ)^3515
        have hw : |(-49110241/250000000 : ℝ)|=(49110241/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218044603/10000000000 : ℝ)|^4539 ≤ (43172911319847/100000000000000 : ℝ)^3515
        have hw : |(5218044603/10000000000 : ℝ)|=(5218044603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s5_2 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668886839/1250000000 : ℝ)*x 0 + (5218044601/10000000000 : ℝ)*x 1 + (-49110241/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668886839/1250000000 : ℝ)^4539 ≤ (44599681686077/100000000000000 : ℝ)^3515 := by
    have hnat : (668886839 : ℕ)^4539*100000000000000^3515 ≤ 44599681686077^3515*1250000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668886839 1250000000 44599681686077 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218044601/10000000000 : ℝ)^4539 ≤ (21586455649239/50000000000000 : ℝ)^3515 := by
    have hnat : (5218044601 : ℕ)^4539*50000000000000^3515 ≤ 21586455649239^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218044601 10000000000 21586455649239 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49110241/250000000 : ℝ)^4539 ≤ (611370350267/5000000000000 : ℝ)^3515 := by
    have hnat : (49110241 : ℕ)^4539*5000000000000^3515 ≤ 611370350267^3515*250000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49110241 250000000 611370350267 5000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668886839/1250000000 : ℝ), (5218044601/10000000000 : ℝ), (-49110241/250000000 : ℝ)] ![(44599681686077/100000000000000 : ℝ), (21586455649239/50000000000000 : ℝ), (611370350267/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668886839/1250000000 : ℝ)|^4539 ≤ (44599681686077/100000000000000 : ℝ)^3515
        have hw : |(668886839/1250000000 : ℝ)|=(668886839/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218044601/10000000000 : ℝ)|^4539 ≤ (21586455649239/50000000000000 : ℝ)^3515
        have hw : |(5218044601/10000000000 : ℝ)|=(5218044601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-49110241/250000000 : ℝ)|^4539 ≤ (611370350267/5000000000000 : ℝ)^3515
        have hw : |(-49110241/250000000 : ℝ)|=(49110241/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s5_3 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2132797867/5000000000 : ℝ)*x 0 + (3146291/7812500 : ℝ)*x 1 + (56446549/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132797867/5000000000 : ℝ)^4539 ≤ (16640037790807/50000000000000 : ℝ)^3515 := by
    have hnat : (2132797867 : ℕ)^4539*50000000000000^3515 ≤ 16640037790807^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132797867 5000000000 16640037790807 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3146291/7812500 : ℝ)^4539 ≤ (30898606376117/100000000000000 : ℝ)^3515 := by
    have hnat : (3146291 : ℕ)^4539*100000000000000^3515 ≤ 30898606376117^3515*7812500^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3146291 7812500 30898606376117 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56446549/125000000 : ℝ)^4539 ≤ (17910659015669/50000000000000 : ℝ)^3515 := by
    have hnat : (56446549 : ℕ)^4539*50000000000000^3515 ≤ 17910659015669^3515*125000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56446549 125000000 17910659015669 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2132797867/5000000000 : ℝ), (3146291/7812500 : ℝ), (56446549/125000000 : ℝ)] ![(16640037790807/50000000000000 : ℝ), (30898606376117/100000000000000 : ℝ), (17910659015669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2132797867/5000000000 : ℝ)|^4539 ≤ (16640037790807/50000000000000 : ℝ)^3515
        have hw : |(2132797867/5000000000 : ℝ)|=(2132797867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3146291/7812500 : ℝ)|^4539 ≤ (30898606376117/100000000000000 : ℝ)^3515
        have hw : |(3146291/7812500 : ℝ)|=(3146291/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(56446549/125000000 : ℝ)|^4539 ≤ (17910659015669/50000000000000 : ℝ)^3515
        have hw : |(56446549/125000000 : ℝ)|=(56446549/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s5_4 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-463706947/2500000000 : ℝ)*x 0 + (5219148809/10000000000 : ℝ)*x 1 + (5430988847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (463706947/2500000000 : ℝ)^4539 ≤ (11353863619479/100000000000000 : ℝ)^3515 := by
    have hnat : (463706947 : ℕ)^4539*100000000000000^3515 ≤ 11353863619479^3515*2500000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463706947 2500000000 11353863619479 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219148809/10000000000 : ℝ)^4539 ≤ (10796177285809/25000000000000 : ℝ)^3515 := by
    have hnat : (5219148809 : ℕ)^4539*25000000000000^3515 ≤ 10796177285809^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219148809 10000000000 10796177285809 25000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5430988847/10000000000 : ℝ)^4539 ≤ (22730713612223/50000000000000 : ℝ)^3515 := by
    have hnat : (5430988847 : ℕ)^4539*50000000000000^3515 ≤ 22730713612223^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430988847 10000000000 22730713612223 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-463706947/2500000000 : ℝ), (5219148809/10000000000 : ℝ), (5430988847/10000000000 : ℝ)] ![(11353863619479/100000000000000 : ℝ), (10796177285809/25000000000000 : ℝ), (22730713612223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-463706947/2500000000 : ℝ)|^4539 ≤ (11353863619479/100000000000000 : ℝ)^3515
        have hw : |(-463706947/2500000000 : ℝ)|=(463706947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219148809/10000000000 : ℝ)|^4539 ≤ (10796177285809/25000000000000 : ℝ)^3515
        have hw : |(5219148809/10000000000 : ℝ)|=(5219148809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5430988847/10000000000 : ℝ)|^4539 ≤ (22730713612223/50000000000000 : ℝ)^3515
        have hw : |(5430988847/10000000000 : ℝ)|=(5430988847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s5_5 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323706797/2500000000 : ℝ)*x 0 + (-875732663/5000000000 : ℝ)*x 1 + (1357747213/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323706797/2500000000 : ℝ)^4539 ≤ (8799003451731/20000000000000 : ℝ)^3515 := by
    have hnat : (1323706797 : ℕ)^4539*20000000000000^3515 ≤ 8799003451731^3515*2500000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323706797 2500000000 8799003451731 20000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (875732663/5000000000 : ℝ)^4539 ≤ (10543555445341/100000000000000 : ℝ)^3515 := by
    have hnat : (875732663 : ℕ)^4539*100000000000000^3515 ≤ 10543555445341^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875732663 5000000000 10543555445341 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357747213/2500000000 : ℝ)^4539 ≤ (11365356819623/25000000000000 : ℝ)^3515 := by
    have hnat : (1357747213 : ℕ)^4539*25000000000000^3515 ≤ 11365356819623^3515*2500000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357747213 2500000000 11365356819623 25000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323706797/2500000000 : ℝ), (-875732663/5000000000 : ℝ), (1357747213/2500000000 : ℝ)] ![(8799003451731/20000000000000 : ℝ), (10543555445341/100000000000000 : ℝ), (11365356819623/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323706797/2500000000 : ℝ)|^4539 ≤ (8799003451731/20000000000000 : ℝ)^3515
        have hw : |(1323706797/2500000000 : ℝ)|=(1323706797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-875732663/5000000000 : ℝ)|^4539 ≤ (10543555445341/100000000000000 : ℝ)^3515
        have hw : |(-875732663/5000000000 : ℝ)|=(875732663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357747213/2500000000 : ℝ)|^4539 ≤ (11365356819623/25000000000000 : ℝ)^3515
        have hw : |(1357747213/2500000000 : ℝ)|=(1357747213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s5_6 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323706783/2500000000 : ℝ)*x 0 + (5430988909/10000000000 : ℝ)*x 1 + (-437866331/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323706783/2500000000 : ℝ)^4539 ≤ (43995016657793/100000000000000 : ℝ)^3515 := by
    have hnat : (1323706783 : ℕ)^4539*100000000000000^3515 ≤ 43995016657793^3515*2500000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323706783 2500000000 43995016657793 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430988909/10000000000 : ℝ)^4539 ≤ (1420669621707/3125000000000 : ℝ)^3515 := by
    have hnat : (5430988909 : ℕ)^4539*3125000000000^3515 ≤ 1420669621707^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430988909 10000000000 1420669621707 3125000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (437866331/2500000000 : ℝ)^4539 ≤ (5271777714897/50000000000000 : ℝ)^3515 := by
    have hnat : (437866331 : ℕ)^4539*50000000000000^3515 ≤ 5271777714897^3515*2500000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437866331 2500000000 5271777714897 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323706783/2500000000 : ℝ), (5430988909/10000000000 : ℝ), (-437866331/2500000000 : ℝ)] ![(43995016657793/100000000000000 : ℝ), (1420669621707/3125000000000 : ℝ), (5271777714897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323706783/2500000000 : ℝ)|^4539 ≤ (43995016657793/100000000000000 : ℝ)^3515
        have hw : |(1323706783/2500000000 : ℝ)|=(1323706783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5430988909/10000000000 : ℝ)|^4539 ≤ (1420669621707/3125000000000 : ℝ)^3515
        have hw : |(5430988909/10000000000 : ℝ)|=(5430988909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-437866331/2500000000 : ℝ)|^4539 ≤ (5271777714897/50000000000000 : ℝ)^3515
        have hw : |(-437866331/2500000000 : ℝ)|=(437866331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s5_7 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1066415247/2500000000 : ℝ)*x 0 + (4513204257/10000000000 : ℝ)*x 1 + (503723849/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066415247/2500000000 : ℝ)^4539 ≤ (16640366504333/50000000000000 : ℝ)^3515 := by
    have hnat : (1066415247 : ℕ)^4539*50000000000000^3515 ≤ 16640366504333^3515*2500000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066415247 2500000000 16640366504333 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4513204257/10000000000 : ℝ)^4539 ≤ (7159101984429/20000000000000 : ℝ)^3515 := by
    have hnat : (4513204257 : ℕ)^4539*20000000000000^3515 ≤ 7159101984429^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513204257 10000000000 7159101984429 20000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (503723849/1250000000 : ℝ)^4539 ≤ (30923757057443/100000000000000 : ℝ)^3515 := by
    have hnat : (503723849 : ℕ)^4539*100000000000000^3515 ≤ 30923757057443^3515*1250000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503723849 1250000000 30923757057443 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1066415247/2500000000 : ℝ), (4513204257/10000000000 : ℝ), (503723849/1250000000 : ℝ)] ![(16640366504333/50000000000000 : ℝ), (7159101984429/20000000000000 : ℝ), (30923757057443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1066415247/2500000000 : ℝ)|^4539 ≤ (16640366504333/50000000000000 : ℝ)^3515
        have hw : |(1066415247/2500000000 : ℝ)|=(1066415247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4513204257/10000000000 : ℝ)|^4539 ≤ (7159101984429/20000000000000 : ℝ)^3515
        have hw : |(4513204257/10000000000 : ℝ)|=(4513204257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(503723849/1250000000 : ℝ)|^4539 ≤ (30923757057443/100000000000000 : ℝ)^3515
        have hw : |(503723849/1250000000 : ℝ)|=(503723849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1521_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164098667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10943/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (219/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10943/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10943/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10943/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10943/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10943/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10943/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10943/100000 : ℝ) ^ (4537/1024 : ℝ) ≤ (5530140625302861/100000000000000000000 : ℝ) := by
    have hpowers : (10943/100000 : ℝ)^4537 ≤ (5530140625302861/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10943 : ℕ)^4537*100000000000000000000^1024 ≤ 5530140625302861^1024*100000^4537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10943 100000 5530140625302861 100000000000000000000 4537 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10943/100000 : ℝ)) (X := (5530140625302861/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4537/1024 : ℝ) ≤ (25786353034929923/100000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4537 ≤ (25786353034929923/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4537*100000000000000000000^1024 ≤ 25786353034929923^1024*10000^4537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 25786353034929923 100000000000000000000 4537 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (25786353034929923/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005530140625302861/50000000000000000000 : ℝ) ≤ (10000249619639981/10000000000000000 : ℝ) ^ (4537/1024 : ℝ) := by
    have hpowers : (50005530140625302861/50000000000000000000 : ℝ)^1024 ≤ (10000249619639981/10000000000000000 : ℝ)^4537 := by
      have hnat : (50005530140625302861 : ℕ)^1024*10000000000000000^4537 ≤ 10000249619639981^4537*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005530140625302861 50000000000000000000 10000249619639981 10000000000000000 1024 4537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000249619639981/10000000000000000 : ℝ)) (X := (50005530140625302861/50000000000000000000 : ℝ)) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6251957280853764549/6250000000000000000 : ℝ) ≤ (625044170435081/625000000000000 : ℝ) ^ (4537/1024 : ℝ) := by
    have hpowers : (6251957280853764549/6250000000000000000 : ℝ)^1024 ≤ (625044170435081/625000000000000 : ℝ)^4537 := by
      have hnat : (6251957280853764549 : ℕ)^1024*625000000000000^4537 ≤ 625044170435081^4537*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251957280853764549 6250000000000000000 625044170435081 625000000000000 1024 4537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625044170435081/625000000000000 : ℝ)) (X := (6251957280853764549/6250000000000000000 : ℝ)) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025786353034929923/50000000000000000000 : ℝ) ≤ (10001163834282611/10000000000000000 : ℝ) ^ (4537/1024 : ℝ) := by
    have hpowers : (50025786353034929923/50000000000000000000 : ℝ)^1024 ≤ (10001163834282611/10000000000000000 : ℝ)^4537 := by
      have hnat : (50025786353034929923 : ℕ)^1024*10000000000000000^4537 ≤ 10001163834282611^4537*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025786353034929923 50000000000000000000 10001163834282611 10000000000000000 1024 4537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001163834282611/10000000000000000 : ℝ)) (X := (50025786353034929923/50000000000000000000 : ℝ)) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5530140625302861/100000000000000000000 : ℝ) ≤ ((45461130769668693517/45470000000000000000 : ℝ)+2*(91421464263/90940000000000 : ℝ)*(10943/100000 : ℝ))^(4537/1024 : ℝ) := by
    rw [show (45461130769668693517/45470000000000000000 : ℝ)+2*(91421464263/90940000000000 : ℝ)*(10943/100000 : ℝ)=(10000249619639981/10000000000000000 : ℝ) by norm_num, show 1+2*(5530140625302861/100000000000000000000 : ℝ)=(50005530140625302861/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25786353034929923/100000000000000000000 : ℝ)+(5530140625302861/100000000000000000000 : ℝ) ≤ ((45461130769668693517/45470000000000000000 : ℝ)+(91421464263/90940000000000 : ℝ)*((1549/10000 : ℝ)+(10943/100000 : ℝ)))^(4537/1024 : ℝ) := by
    rw [show (45461130769668693517/45470000000000000000 : ℝ)+(91421464263/90940000000000 : ℝ)*((1549/10000 : ℝ)+(10943/100000 : ℝ))=(625044170435081/625000000000000 : ℝ) by norm_num, show 1+(25786353034929923/100000000000000000000 : ℝ)+(5530140625302861/100000000000000000000 : ℝ)=(6251957280853764549/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25786353034929923/100000000000000000000 : ℝ) ≤ ((45461130769668693517/45470000000000000000 : ℝ)+2*(91421464263/90940000000000 : ℝ)*(1549/10000 : ℝ))^(4537/1024 : ℝ) := by
    rw [show (45461130769668693517/45470000000000000000 : ℝ)+2*(91421464263/90940000000000 : ℝ)*(1549/10000 : ℝ)=(10001163834282611/10000000000000000 : ℝ) by norm_num, show 1+2*(25786353034929923/100000000000000000000 : ℝ)=(50025786353034929923/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (45461130769668693517/45470000000000000000 : ℝ)*(X 1 0+X 2 0)+(91421464263/90940000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4537/1024 : ℝ)) (lo := (10943/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (45461130769668693517/45470000000000000000 : ℝ)) (alpha := (91421464263/90940000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (45461130769668693517/45470000000000000000 : ℝ)*(X 0 1+X 2 1)+(91421464263/90940000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4537/1024 : ℝ)) (lo := (10943/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (45461130769668693517/45470000000000000000 : ℝ)) (alpha := (91421464263/90940000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (45461130769668693517/45470000000000000000 : ℝ)*(X 0 2+X 1 2)+(91421464263/90940000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4537/1024 : ℝ)) (lo := (10943/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (45461130769668693517/45470000000000000000 : ℝ)) (alpha := (91421464263/90940000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-463699791/2500000000 : ℝ)*X 0 0+(2716050601/5000000000 : ℝ)*X 0 1+(5218044593/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535109471/1000000000 : ℝ)*X 1 0+(-49110241/250000000 : ℝ)*X 1 1+(5218044603/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668886839/1250000000 : ℝ)*X 2 0+(5218044601/10000000000 : ℝ)*X 2 1+(-49110241/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2132797867/5000000000 : ℝ)*X 0 0+(3146291/7812500 : ℝ)*X 0 1+(56446549/125000000 : ℝ)*X 0 2+(2132797867/5000000000 : ℝ)*X 1 0+(3146291/7812500 : ℝ)*X 1 1+(56446549/125000000 : ℝ)*X 1 2+(2132797867/5000000000 : ℝ)*X 2 0+(3146291/7812500 : ℝ)*X 2 1+(56446549/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-463706947/2500000000 : ℝ)*X 0 0+(5219148809/10000000000 : ℝ)*X 0 1+(5430988847/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323706797/2500000000 : ℝ)*X 1 0+(-875732663/5000000000 : ℝ)*X 1 1+(1357747213/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323706783/2500000000 : ℝ)*X 2 0+(5430988909/10000000000 : ℝ)*X 2 1+(-437866331/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1066415247/2500000000 : ℝ)*X 0 0+(4513204257/10000000000 : ℝ)*X 0 1+(503723849/1250000000 : ℝ)*X 0 2+(1066415247/2500000000 : ℝ)*X 1 0+(4513204257/10000000000 : ℝ)*X 1 1+(503723849/1250000000 : ℝ)*X 1 2+(1066415247/2500000000 : ℝ)*X 2 0+(4513204257/10000000000 : ℝ)*X 2 1+(503723849/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (581012557977377123395480083/284187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (361789547/100000000000000 : ℝ)*(base19) + (85020239/25000000000000 : ℝ)*(base23) + (1568851/12500000000000 : ℝ)*(lower2) + (645857/1250000000000 : ℝ)*(upper3) + (34858349/100000000000000 : ℝ)*(upper5) + (419930078776933/12500000000000 : ℝ)*(major0) + (419930078776933/12500000000000 : ℝ)*(major1) + (419930078776933/12500000000000 : ℝ)*(major2) + (1167916880935549/25000000000000 : ℝ)*(sp0) + (2335836539714579/50000000000000 : ℝ)*(sp1) + (4671673101137749/100000000000000 : ℝ)*(sp2) + (409441006197909/20000000000000 : ℝ)*(sp3) + (5917476509/100000000000000 : ℝ)*(sp4) + (2720073701/100000000000000 : ℝ)*(sp7) + (409441550212649/20000000000000 : ℝ)*(f.failure) + (934334688243741/20000000000000 : ℝ)*(f.sum) + (3888745680461/2273500000000000000000000000 : ℝ)*base66 + (2975371297063006639/568375000000000000000000000000000 : ℝ)*base68 + (2705168557651881639/568375000000000000000000000000000 : ℝ)*base70 + (2921613064112506639/568375000000000000000000000000000 : ℝ)*base72 + (17879389634407/4547000000000000000000000000 : ℝ)*base74 + (2696955652237993361/568375000000000000000000000000000 : ℝ)*base75 + (1248026229127993361/568375000000000000000000000000000 : ℝ)*base77 + (7217833571247006639/568375000000000000000000000000000 : ℝ)*base80 + (1884857901359/568375000000000000000000000 : ℝ)*base82 + (12561117/2000000000000000000000 : ℝ)*base90 + (12561117/2000000000000000000000 : ℝ)*base92 + (12561117/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5603253411339877417272884223/568375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1664420589/100000000000000 : ℝ)*(base19) + (1725012607/100000000000000 : ℝ)*(base23) + (110631659/20000000000000 : ℝ)*(lower1) + (10483879/5000000000000 : ℝ)*(upper3) + (11843097/25000000000000 : ℝ)*(lower4) + (181998513/100000000000000 : ℝ)*(upper5) + (1697281585304073/50000000000000 : ℝ)*(major0) + (1697281585304073/50000000000000 : ℝ)*(major1) + (1697281585304073/50000000000000 : ℝ)*(major2) + (247587307/12500000000000 : ℝ)*(sp2) + (4720514955203723/100000000000000 : ℝ)*(sp4) + (4720513290783133/100000000000000 : ℝ)*(sp5) + (236025562474633/5000000000000 : ℝ)*(sp6) + (1034305528700043/50000000000000 : ℝ)*(sp7) + (1034305528700043/50000000000000 : ℝ)*(f.failure) + (4720514955203723/100000000000000 : ℝ)*(f.sum) + (640516015307/454700000000000000000000000 : ℝ)*base66 + (34624248922773205259/2273500000000000000000000000000000 : ℝ)*base68 + (649323006352794741/2273500000000000000000000000000000 : ℝ)*base69 + (41175527789153705259/2273500000000000000000000000000000 : ℝ)*base72 + (1420612748957/454700000000000000000000000 : ℝ)*base74 + (102673876611869705259/2273500000000000000000000000000000 : ℝ)*base76 + (16055162013171705259/2273500000000000000000000000000000 : ℝ)*base78 + (20139616933114705259/2273500000000000000000000000000000 : ℝ)*base80 + (2244316266047/2273500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (857319/5000000000000000000000 : ℝ)*base90 + (857319/5000000000000000000000 : ℝ)*base92 + (857319/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1521_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164098667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10943/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (219/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1521_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1521_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164098667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15963/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2627/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (219/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1521_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1521_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1521_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164098667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15963/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2627/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (219/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1521_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
