-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1431_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:54:25.209091+00:00
-- url     : https://prove2.me/submissions/a67dfc52-90a7-4036-b0c7-df304404c782

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
theorem support_rectangle_w1431_s6_0 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-492376583/2500000000 : ℝ)*x 0 + (540811921/1000000000 : ℝ)*x 1 + (209877979/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (492376583/2500000000 : ℝ)^4391 ≤ (1501970841263/12500000000000 : ℝ)^3367 := by
    have hnat : (492376583 : ℕ)^4391*12500000000000^3367 ≤ 1501970841263^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492376583 2500000000 1501970841263 12500000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540811921/1000000000 : ℝ)^4391 ≤ (44859875782749/100000000000000 : ℝ)^3367 := by
    have hnat : (540811921 : ℕ)^4391*100000000000000^3367 ≤ 44859875782749^3367*1000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540811921 1000000000 44859875782749 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209877979/400000000 : ℝ)^4391 ≤ (43124357464083/100000000000000 : ℝ)^3367 := by
    have hnat : (209877979 : ℕ)^4391*100000000000000^3367 ≤ 43124357464083^3367*400000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209877979 400000000 43124357464083 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-492376583/2500000000 : ℝ), (540811921/1000000000 : ℝ), (209877979/400000000 : ℝ)] ![(1501970841263/12500000000000 : ℝ), (44859875782749/100000000000000 : ℝ), (43124357464083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-492376583/2500000000 : ℝ)|^4391 ≤ (1501970841263/12500000000000 : ℝ)^3367
        have hw : |(-492376583/2500000000 : ℝ)|=(492376583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540811921/1000000000 : ℝ)|^4391 ≤ (44859875782749/100000000000000 : ℝ)^3367
        have hw : |(540811921/1000000000 : ℝ)|=(540811921/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209877979/400000000 : ℝ)|^4391 ≤ (43124357464083/100000000000000 : ℝ)^3367
        have hw : |(209877979/400000000 : ℝ)|=(209877979/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s6_1 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336821623/2500000000 : ℝ)*x 0 + (-512889769/2500000000 : ℝ)*x 1 + (1311737357/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336821623/2500000000 : ℝ)^4391 ≤ (44202938493899/100000000000000 : ℝ)^3367 := by
    have hnat : (1336821623 : ℕ)^4391*100000000000000^3367 ≤ 44202938493899^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336821623 2500000000 44202938493899 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (512889769/2500000000 : ℝ)^4391 ≤ (6336352263599/50000000000000 : ℝ)^3367 := by
    have hnat : (512889769 : ℕ)^4391*50000000000000^3367 ≤ 6336352263599^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512889769 2500000000 6336352263599 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311737357/2500000000 : ℝ)^4391 ≤ (43124356960311/100000000000000 : ℝ)^3367 := by
    have hnat : (1311737357 : ℕ)^4391*100000000000000^3367 ≤ 43124356960311^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311737357 2500000000 43124356960311 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336821623/2500000000 : ℝ), (-512889769/2500000000 : ℝ), (1311737357/2500000000 : ℝ)] ![(44202938493899/100000000000000 : ℝ), (6336352263599/50000000000000 : ℝ), (43124356960311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336821623/2500000000 : ℝ)|^4391 ≤ (44202938493899/100000000000000 : ℝ)^3367
        have hw : |(1336821623/2500000000 : ℝ)|=(1336821623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-512889769/2500000000 : ℝ)|^4391 ≤ (6336352263599/50000000000000 : ℝ)^3367
        have hw : |(-512889769/2500000000 : ℝ)|=(512889769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311737357/2500000000 : ℝ)|^4391 ≤ (43124356960311/100000000000000 : ℝ)^3367
        have hw : |(1311737357/2500000000 : ℝ)|=(1311737357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s6_2 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336821611/2500000000 : ℝ)*x 0 + (5246949477/10000000000 : ℝ)*x 1 + (-512889769/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336821611/2500000000 : ℝ)^4391 ≤ (11050734494109/25000000000000 : ℝ)^3367 := by
    have hnat : (1336821611 : ℕ)^4391*25000000000000^3367 ≤ 11050734494109^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336821611 2500000000 11050734494109 25000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246949477/10000000000 : ℝ)^4391 ≤ (539054468569/1250000000000 : ℝ)^3367 := by
    have hnat : (5246949477 : ℕ)^4391*1250000000000^3367 ≤ 539054468569^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246949477 10000000000 539054468569 1250000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (512889769/2500000000 : ℝ)^4391 ≤ (6336352263599/50000000000000 : ℝ)^3367 := by
    have hnat : (512889769 : ℕ)^4391*50000000000000^3367 ≤ 6336352263599^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512889769 2500000000 6336352263599 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336821611/2500000000 : ℝ), (5246949477/10000000000 : ℝ), (-512889769/2500000000 : ℝ)] ![(11050734494109/25000000000000 : ℝ), (539054468569/1250000000000 : ℝ), (6336352263599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336821611/2500000000 : ℝ)|^4391 ≤ (11050734494109/25000000000000 : ℝ)^3367
        have hw : |(1336821611/2500000000 : ℝ)|=(1336821611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246949477/10000000000 : ℝ)|^4391 ≤ (539054468569/1250000000000 : ℝ)^3367
        have hw : |(5246949477/10000000000 : ℝ)|=(5246949477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-512889769/2500000000 : ℝ)|^4391 ≤ (6336352263599/50000000000000 : ℝ)^3367
        have hw : |(-512889769/2500000000 : ℝ)|=(512889769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s6_3 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2151936639/5000000000 : ℝ)*x 0 + (2066295591/5000000000 : ℝ)*x 1 + (1120377703/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151936639/5000000000 : ℝ)^4391 ≤ (33304719390211/100000000000000 : ℝ)^3367 := by
    have hnat : (2151936639 : ℕ)^4391*100000000000000^3367 ≤ 33304719390211^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151936639 5000000000 33304719390211 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2066295591/5000000000 : ℝ)^4391 ≤ (3158674160017/10000000000000 : ℝ)^3367 := by
    have hnat : (2066295591 : ℕ)^4391*10000000000000^3367 ≤ 3158674160017^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066295591 5000000000 3158674160017 10000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1120377703/2500000000 : ℝ)^4391 ≤ (7021707800111/20000000000000 : ℝ)^3367 := by
    have hnat : (1120377703 : ℕ)^4391*20000000000000^3367 ≤ 7021707800111^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120377703 2500000000 7021707800111 20000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2151936639/5000000000 : ℝ), (2066295591/5000000000 : ℝ), (1120377703/2500000000 : ℝ)] ![(33304719390211/100000000000000 : ℝ), (3158674160017/10000000000000 : ℝ), (7021707800111/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2151936639/5000000000 : ℝ)|^4391 ≤ (33304719390211/100000000000000 : ℝ)^3367
        have hw : |(2151936639/5000000000 : ℝ)|=(2151936639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2066295591/5000000000 : ℝ)|^4391 ≤ (3158674160017/10000000000000 : ℝ)^3367
        have hw : |(2066295591/5000000000 : ℝ)|=(2066295591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1120377703/2500000000 : ℝ)|^4391 ≤ (7021707800111/20000000000000 : ℝ)^3367
        have hw : |(1120377703/2500000000 : ℝ)|=(1120377703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s6_4 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-393903509/2000000000 : ℝ)*x 0 + (655941371/1250000000 : ℝ)*x 1 + (5407534777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393903509/2000000000 : ℝ)^4391 ≤ (12015855944847/100000000000000 : ℝ)^3367 := by
    have hnat : (393903509 : ℕ)^4391*100000000000000^3367 ≤ 12015855944847^3367*2000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393903509 2000000000 12015855944847 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655941371/1250000000 : ℝ)^4391 ≤ (43130590331453/100000000000000 : ℝ)^3367 := by
    have hnat : (655941371 : ℕ)^4391*100000000000000^3367 ≤ 43130590331453^3367*1250000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655941371 1250000000 43130590331453 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407534777/10000000000 : ℝ)^4391 ≤ (44853553706569/100000000000000 : ℝ)^3367 := by
    have hnat : (5407534777 : ℕ)^4391*100000000000000^3367 ≤ 44853553706569^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407534777 10000000000 44853553706569 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-393903509/2000000000 : ℝ), (655941371/1250000000 : ℝ), (5407534777/10000000000 : ℝ)] ![(12015855944847/100000000000000 : ℝ), (43130590331453/100000000000000 : ℝ), (44853553706569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-393903509/2000000000 : ℝ)|^4391 ≤ (12015855944847/100000000000000 : ℝ)^3367
        have hw : |(-393903509/2000000000 : ℝ)|=(393903509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655941371/1250000000 : ℝ)|^4391 ≤ (43130590331453/100000000000000 : ℝ)^3367
        have hw : |(655941371/1250000000 : ℝ)|=(655941371/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407534777/10000000000 : ℝ)|^4391 ≤ (44853553706569/100000000000000 : ℝ)^3367
        have hw : |(5407534777/10000000000 : ℝ)|=(5407534777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s6_5 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326344601/2500000000 : ℝ)*x 0 + (-378194733/2000000000 : ℝ)*x 1 + (1081506969/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326344601/2500000000 : ℝ)^4391 ≤ (21875844345889/50000000000000 : ℝ)^3367 := by
    have hnat : (1326344601 : ℕ)^4391*50000000000000^3367 ≤ 21875844345889^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326344601 2500000000 21875844345889 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (378194733/2000000000 : ℝ)^4391 ≤ (11394756854177/100000000000000 : ℝ)^3367 := by
    have hnat : (378194733 : ℕ)^4391*100000000000000^3367 ≤ 11394756854177^3367*2000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378194733 2000000000 11394756854177 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081506969/2000000000 : ℝ)^4391 ≤ (1401673576317/3125000000000 : ℝ)^3367 := by
    have hnat : (1081506969 : ℕ)^4391*3125000000000^3367 ≤ 1401673576317^3367*2000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081506969 2000000000 1401673576317 3125000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326344601/2500000000 : ℝ), (-378194733/2000000000 : ℝ), (1081506969/2000000000 : ℝ)] ![(21875844345889/50000000000000 : ℝ), (11394756854177/100000000000000 : ℝ), (1401673576317/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326344601/2500000000 : ℝ)|^4391 ≤ (21875844345889/50000000000000 : ℝ)^3367
        have hw : |(1326344601/2500000000 : ℝ)|=(1326344601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-378194733/2000000000 : ℝ)|^4391 ≤ (11394756854177/100000000000000 : ℝ)^3367
        have hw : |(-378194733/2000000000 : ℝ)|=(378194733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081506969/2000000000 : ℝ)|^4391 ≤ (1401673576317/3125000000000 : ℝ)^3367
        have hw : |(1081506969/2000000000 : ℝ)|=(1081506969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s6_6 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305378757/10000000000 : ℝ)*x 0 + (5407534489/10000000000 : ℝ)*x 1 + (-1890973671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305378757/10000000000 : ℝ)^4391 ≤ (43751692488191/100000000000000 : ℝ)^3367 := by
    have hnat : (5305378757 : ℕ)^4391*100000000000000^3367 ≤ 43751692488191^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305378757 10000000000 43751692488191 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407534489/10000000000 : ℝ)^4391 ≤ (22426775295597/50000000000000 : ℝ)^3367 := by
    have hnat : (5407534489 : ℕ)^4391*50000000000000^3367 ≤ 22426775295597^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407534489 10000000000 22426775295597 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1890973671/10000000000 : ℝ)^4391 ≤ (712172306333/6250000000000 : ℝ)^3367 := by
    have hnat : (1890973671 : ℕ)^4391*6250000000000^3367 ≤ 712172306333^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1890973671 10000000000 712172306333 6250000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305378757/10000000000 : ℝ), (5407534489/10000000000 : ℝ), (-1890973671/10000000000 : ℝ)] ![(43751692488191/100000000000000 : ℝ), (22426775295597/50000000000000 : ℝ), (712172306333/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305378757/10000000000 : ℝ)|^4391 ≤ (43751692488191/100000000000000 : ℝ)^3367
        have hw : |(5305378757/10000000000 : ℝ)|=(5305378757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407534489/10000000000 : ℝ)|^4391 ≤ (22426775295597/50000000000000 : ℝ)^3367
        have hw : |(5407534489/10000000000 : ℝ)|=(5407534489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1890973671/10000000000 : ℝ)|^4391 ≤ (712172306333/6250000000000 : ℝ)^3367
        have hw : |(-1890973671/10000000000 : ℝ)|=(1890973671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s6_7 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075974361/2500000000 : ℝ)*x 0 + (4480252361/10000000000 : ℝ)*x 1 + (206692823/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075974361/2500000000 : ℝ)^4391 ≤ (33304963267729/100000000000000 : ℝ)^3367 := by
    have hnat : (1075974361 : ℕ)^4391*100000000000000^3367 ≤ 33304963267729^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075974361 2500000000 33304963267729 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4480252361/10000000000 : ℝ)^4391 ≤ (35095682392829/100000000000000 : ℝ)^3367 := by
    have hnat : (4480252361 : ℕ)^4391*100000000000000^3367 ≤ 35095682392829^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480252361 10000000000 35095682392829 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206692823/500000000 : ℝ)^4391 ≤ (31599354323761/100000000000000 : ℝ)^3367 := by
    have hnat : (206692823 : ℕ)^4391*100000000000000^3367 ≤ 31599354323761^3367*500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206692823 500000000 31599354323761 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075974361/2500000000 : ℝ), (4480252361/10000000000 : ℝ), (206692823/500000000 : ℝ)] ![(33304963267729/100000000000000 : ℝ), (35095682392829/100000000000000 : ℝ), (31599354323761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075974361/2500000000 : ℝ)|^4391 ≤ (33304963267729/100000000000000 : ℝ)^3367
        have hw : |(1075974361/2500000000 : ℝ)|=(1075974361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4480252361/10000000000 : ℝ)|^4391 ≤ (35095682392829/100000000000000 : ℝ)^3367
        have hw : |(4480252361/10000000000 : ℝ)|=(4480252361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(206692823/500000000 : ℝ)|^4391 ≤ (31599354323761/100000000000000 : ℝ)^3367
        have hw : |(206692823/500000000 : ℝ)|=(206692823/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1431_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15824599/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (709/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7379/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7381/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11341/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7381/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11341/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7381/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11341/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7381/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11341/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7381/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11341/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7381/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11341/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11341/100000 : ℝ) ^ (2195/512 : ℝ) ≤ (8854966893993413/100000000000000000000 : ℝ) := by
    have hpowers : (11341/100000 : ℝ)^2195 ≤ (8854966893993413/100000000000000000000 : ℝ)^512 := by
      have hnat : (11341 : ℕ)^2195*100000000000000000000^512 ≤ 8854966893993413^512*100000^2195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11341 100000 8854966893993413 100000000000000000000 2195 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11341/100000 : ℝ)) (X := (8854966893993413/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7381/50000 : ℝ) ^ (2195/512 : ℝ) ≤ (342724076543747/1250000000000000000 : ℝ) := by
    have hpowers : (7381/50000 : ℝ)^2195 ≤ (342724076543747/1250000000000000000 : ℝ)^512 := by
      have hnat : (7381 : ℕ)^2195*1250000000000000000^512 ≤ 342724076543747^512*50000^2195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7381 50000 342724076543747 1250000000000000000 2195 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7381/50000 : ℝ)) (X := (342724076543747/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008854966893993413/50000000000000000000 : ℝ) ≤ (625025816829523/625000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (50008854966893993413/50000000000000000000 : ℝ)^512 ≤ (625025816829523/625000000000000 : ℝ)^2195 := by
      have hnat : (50008854966893993413 : ℕ)^512*625000000000000^2195 ≤ 625025816829523^2195*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008854966893993413 50000000000000000000 625025816829523 625000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625025816829523/625000000000000 : ℝ)) (X := (50008854966893993413/50000000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036272893017493173/100000000000000000000 : ℝ) ≤ (5000422987225411/5000000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (100036272893017493173/100000000000000000000 : ℝ)^512 ≤ (5000422987225411/5000000000000000 : ℝ)^2195 := by
      have hnat : (100036272893017493173 : ℕ)^512*5000000000000000^2195 ≤ 5000422987225411^2195*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036272893017493173 100000000000000000000 5000422987225411 5000000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000422987225411/5000000000000000 : ℝ)) (X := (100036272893017493173/100000000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (625342724076543747/625000000000000000 : ℝ) ≤ (2500319719907319/2500000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (625342724076543747/625000000000000000 : ℝ)^512 ≤ (2500319719907319/2500000000000000 : ℝ)^2195 := by
      have hnat : (625342724076543747 : ℕ)^512*2500000000000000^2195 ≤ 2500319719907319^2195*625000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625342724076543747 625000000000000000 2500319719907319 2500000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500319719907319/2500000000000000 : ℝ)) (X := (625342724076543747/625000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8854966893993413/100000000000000000000 : ℝ) ≤ ((31092358140657343/31100000000000000 : ℝ)+2*(216452589227/171050000000000 : ℝ)*(11341/100000 : ℝ))^(2195/512 : ℝ) := by
    rw [show (31092358140657343/31100000000000000 : ℝ)+2*(216452589227/171050000000000 : ℝ)*(11341/100000 : ℝ)=(625025816829523/625000000000000 : ℝ) by norm_num, show 1+2*(8854966893993413/100000000000000000000 : ℝ)=(50008854966893993413/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(342724076543747/1250000000000000000 : ℝ)+(8854966893993413/100000000000000000000 : ℝ) ≤ ((31092358140657343/31100000000000000 : ℝ)+(216452589227/171050000000000 : ℝ)*((7381/50000 : ℝ)+(11341/100000 : ℝ)))^(2195/512 : ℝ) := by
    rw [show (31092358140657343/31100000000000000 : ℝ)+(216452589227/171050000000000 : ℝ)*((7381/50000 : ℝ)+(11341/100000 : ℝ))=(5000422987225411/5000000000000000 : ℝ) by norm_num, show 1+(342724076543747/1250000000000000000 : ℝ)+(8854966893993413/100000000000000000000 : ℝ)=(100036272893017493173/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(342724076543747/1250000000000000000 : ℝ) ≤ ((31092358140657343/31100000000000000 : ℝ)+2*(216452589227/171050000000000 : ℝ)*(7381/50000 : ℝ))^(2195/512 : ℝ) := by
    rw [show (31092358140657343/31100000000000000 : ℝ)+2*(216452589227/171050000000000 : ℝ)*(7381/50000 : ℝ)=(2500319719907319/2500000000000000 : ℝ) by norm_num, show 1+2*(342724076543747/1250000000000000000 : ℝ)=(625342724076543747/625000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (31092358140657343/31100000000000000 : ℝ)*(X 1 0+X 2 0)+(216452589227/171050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (11341/100000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (31092358140657343/31100000000000000 : ℝ)) (alpha := (216452589227/171050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (31092358140657343/31100000000000000 : ℝ)*(X 0 1+X 2 1)+(216452589227/171050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (11341/100000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (31092358140657343/31100000000000000 : ℝ)) (alpha := (216452589227/171050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (31092358140657343/31100000000000000 : ℝ)*(X 0 2+X 1 2)+(216452589227/171050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (11341/100000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (31092358140657343/31100000000000000 : ℝ)) (alpha := (216452589227/171050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-492376583/2500000000 : ℝ)*X 0 0+(540811921/1000000000 : ℝ)*X 0 1+(209877979/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336821623/2500000000 : ℝ)*X 1 0+(-512889769/2500000000 : ℝ)*X 1 1+(1311737357/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336821611/2500000000 : ℝ)*X 2 0+(5246949477/10000000000 : ℝ)*X 2 1+(-512889769/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2151936639/5000000000 : ℝ)*X 0 0+(2066295591/5000000000 : ℝ)*X 0 1+(1120377703/2500000000 : ℝ)*X 0 2+(2151936639/5000000000 : ℝ)*X 1 0+(2066295591/5000000000 : ℝ)*X 1 1+(1120377703/2500000000 : ℝ)*X 1 2+(2151936639/5000000000 : ℝ)*X 2 0+(2066295591/5000000000 : ℝ)*X 2 1+(1120377703/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-393903509/2000000000 : ℝ)*X 0 0+(655941371/1250000000 : ℝ)*X 0 1+(5407534777/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326344601/2500000000 : ℝ)*X 1 0+(-378194733/2000000000 : ℝ)*X 1 1+(1081506969/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305378757/10000000000 : ℝ)*X 2 0+(5407534489/10000000000 : ℝ)*X 2 1+(-1890973671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1075974361/2500000000 : ℝ)*X 0 0+(4480252361/10000000000 : ℝ)*X 0 1+(206692823/500000000 : ℝ)*X 0 2+(1075974361/2500000000 : ℝ)*X 1 0+(4480252361/10000000000 : ℝ)*X 1 1+(206692823/500000000 : ℝ)*X 1 2+(1075974361/2500000000 : ℝ)*X 2 0+(4480252361/10000000000 : ℝ)*X 2 1+(206692823/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31618044987197239530963507/4276250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1365373739/100000000000000 : ℝ)*(base19) + (600535729/50000000000000 : ℝ)*(base23) + (29037307/50000000000000 : ℝ)*(lower2) + (19778927/10000000000000 : ℝ)*(upper3) + (55010421/50000000000000 : ℝ)*(upper5) + (1133838696929297/25000000000000 : ℝ)*(major0) + (1133838696929297/25000000000000 : ℝ)*(major1) + (1133838696929297/25000000000000 : ℝ)*(major2) + (1551166857835731/25000000000000 : ℝ)*(sp0) + (6204692345940441/100000000000000 : ℝ)*(sp1) + (3102346255121361/50000000000000 : ℝ)*(sp2) + (573200347958341/20000000000000 : ℝ)*(sp3) + (26279971257/100000000000000 : ℝ)*(sp4) + (13877866087/100000000000000 : ℝ)*(sp7) + (44781494025903/1562500000000 : ℝ)*(f.failure) + (310234685565709/5000000000000 : ℝ)*(f.sum) + (58360105834927/17105000000000000000000000000 : ℝ)*base65 + (13596908725487919/8552500000000000000000000000000 : ℝ)*base68 + (18274217410372081/8552500000000000000000000000000 : ℝ)*base69 + (74481130412980419/8552500000000000000000000000000 : ℝ)*base72 + (34413863440753/17105000000000000000000000000 : ℝ)*base74 + (13037109780524581/8552500000000000000000000000000 : ℝ)*base75 + (34097667047229581/8552500000000000000000000000000 : ℝ)*base77 + (31717660883667081/8552500000000000000000000000000 : ℝ)*base79 + (3163542210157/1069062500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (37103/15625000000000000000 : ℝ)*base90 + (37103/15625000000000000000 : ℝ)*base92 + (37103/15625000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (95281845318600675691173/17105000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8536279/1000000000000 : ℝ)*(base19) + (1334716851/100000000000000 : ℝ)*(base23) + (70674903/20000000000000 : ℝ)*(lower1) + (81149961/100000000000000 : ℝ)*(upper3) + (2925911/20000000000000 : ℝ)*(lower4) + (4568346585060793/100000000000000 : ℝ)*(major0) + (4568346585060793/100000000000000 : ℝ)*(major1) + (4568346585060793/100000000000000 : ℝ)*(major2) + (953878539/20000000000000 : ℝ)*(sp2) + (350351401/50000000000000 : ℝ)*(sp3) + (6249828941276083/100000000000000 : ℝ)*(sp4) + (6249828087648183/100000000000000 : ℝ)*(sp5) + (3124911418583269/50000000000000 : ℝ)*(sp6) + (721715835615599/25000000000000 : ℝ)*(sp7) + (2886864043165197/100000000000000 : ℝ)*(f.failure) + (6249828941276083/100000000000000 : ℝ)*(f.sum) + (120217263288203/17105000000000000000000000000 : ℝ)*base66 + (123163404142035011/34210000000000000000000000000000 : ℝ)*base68 + (141878484484345011/34210000000000000000000000000000 : ℝ)*base70 + (2560622601884989/34210000000000000000000000000000 : ℝ)*base71 + (88433499434603/17105000000000000000000000000 : ℝ)*base74 + (60213733009414989/34210000000000000000000000000000 : ℝ)*base75 + (494345796343944989/34210000000000000000000000000000 : ℝ)*base77 + (223376852607165011/34210000000000000000000000000000 : ℝ)*base80 + (411945348193/66816406250000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (3281003/1000000000000000000000 : ℝ)*base89 + (3281003/1000000000000000000000 : ℝ)*base91 + (3281003/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1431_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15824599/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (709/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1431_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1431_s7_0 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-393902171/2000000000 : ℝ)*x 0 + (338005911/625000000 : ℝ)*x 1 + (262348549/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393902171/2000000000 : ℝ)^4391 ≤ (6007901358367/50000000000000 : ℝ)^3367 := by
    have hnat : (393902171 : ℕ)^4391*50000000000000^3367 ≤ 6007901358367^3367*2000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393902171 2000000000 6007901358367 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338005911/625000000 : ℝ)^4391 ≤ (44859609301431/100000000000000 : ℝ)^3367 := by
    have hnat : (338005911 : ℕ)^4391*100000000000000^3367 ≤ 44859609301431^3367*625000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338005911 625000000 44859609301431 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262348549/500000000 : ℝ)^4391 ≤ (8624917593333/20000000000000 : ℝ)^3367 := by
    have hnat : (262348549 : ℕ)^4391*20000000000000^3367 ≤ 8624917593333^3367*500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262348549 500000000 8624917593333 20000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-393902171/2000000000 : ℝ), (338005911/625000000 : ℝ), (262348549/500000000 : ℝ)] ![(6007901358367/50000000000000 : ℝ), (44859609301431/100000000000000 : ℝ), (8624917593333/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-393902171/2000000000 : ℝ)|^4391 ≤ (6007901358367/50000000000000 : ℝ)^3367
        have hw : |(-393902171/2000000000 : ℝ)|=(393902171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338005911/625000000 : ℝ)|^4391 ≤ (44859609301431/100000000000000 : ℝ)^3367
        have hw : |(338005911/625000000 : ℝ)|=(338005911/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262348549/500000000 : ℝ)|^4391 ≤ (8624917593333/20000000000000 : ℝ)^3367
        have hw : |(262348549/500000000 : ℝ)|=(262348549/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s7_1 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347278283/10000000000 : ℝ)*x 0 + (-2051537497/10000000000 : ℝ)*x 1 + (2623486951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347278283/10000000000 : ℝ)^4391 ≤ (44202849996977/100000000000000 : ℝ)^3367 := by
    have hnat : (5347278283 : ℕ)^4391*100000000000000^3367 ≤ 44202849996977^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347278283 10000000000 44202849996977 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2051537497/10000000000 : ℝ)^4391 ≤ (6336265346299/50000000000000 : ℝ)^3367 := by
    have hnat : (2051537497 : ℕ)^4391*50000000000000^3367 ≤ 6336265346299^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051537497 10000000000 6336265346299 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623486951/5000000000 : ℝ)^4391 ≤ (5390577410789/12500000000000 : ℝ)^3367 := by
    have hnat : (2623486951 : ℕ)^4391*12500000000000^3367 ≤ 5390577410789^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623486951 5000000000 5390577410789 12500000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347278283/10000000000 : ℝ), (-2051537497/10000000000 : ℝ), (2623486951/5000000000 : ℝ)] ![(44202849996977/100000000000000 : ℝ), (6336265346299/50000000000000 : ℝ), (5390577410789/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347278283/10000000000 : ℝ)|^4391 ≤ (44202849996977/100000000000000 : ℝ)^3367
        have hw : |(5347278283/10000000000 : ℝ)|=(5347278283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2051537497/10000000000 : ℝ)|^4391 ≤ (6336265346299/50000000000000 : ℝ)^3367
        have hw : |(-2051537497/10000000000 : ℝ)|=(2051537497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623486951/5000000000 : ℝ)|^4391 ≤ (5390577410789/12500000000000 : ℝ)^3367
        have hw : |(2623486951/5000000000 : ℝ)|=(2623486951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s7_2 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673640213/5000000000 : ℝ)*x 0 + (2623485373/5000000000 : ℝ)*x 1 + (-2051538829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673640213/5000000000 : ℝ)^4391 ≤ (11050718274883/25000000000000 : ℝ)^3367 := by
    have hnat : (2673640213 : ℕ)^4391*25000000000000^3367 ≤ 11050718274883^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673640213 5000000000 11050718274883 25000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623485373/5000000000 : ℝ)^4391 ≤ (43124585458521/100000000000000 : ℝ)^3367 := by
    have hnat : (2623485373 : ℕ)^4391*100000000000000^3367 ≤ 43124585458521^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623485373 5000000000 43124585458521 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2051538829/10000000000 : ℝ)^4391 ≤ (6336270711407/50000000000000 : ℝ)^3367 := by
    have hnat : (2051538829 : ℕ)^4391*50000000000000^3367 ≤ 6336270711407^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051538829 10000000000 6336270711407 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673640213/5000000000 : ℝ), (2623485373/5000000000 : ℝ), (-2051538829/10000000000 : ℝ)] ![(11050718274883/25000000000000 : ℝ), (43124585458521/100000000000000 : ℝ), (6336270711407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673640213/5000000000 : ℝ)|^4391 ≤ (11050718274883/25000000000000 : ℝ)^3367
        have hw : |(2673640213/5000000000 : ℝ)|=(2673640213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623485373/5000000000 : ℝ)|^4391 ≤ (43124585458521/100000000000000 : ℝ)^3367
        have hw : |(2623485373/5000000000 : ℝ)|=(2623485373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2051538829/10000000000 : ℝ)|^4391 ≤ (6336270711407/50000000000000 : ℝ)^3367
        have hw : |(-2051538829/10000000000 : ℝ)|=(2051538829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s7_3 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4303874983/10000000000 : ℝ)*x 0 + (4132645499/10000000000 : ℝ)*x 1 + (4481456133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4303874983/10000000000 : ℝ)^4391 ≤ (33304736596651/100000000000000 : ℝ)^3367 := by
    have hnat : (4303874983 : ℕ)^4391*100000000000000^3367 ≤ 33304736596651^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303874983 10000000000 33304736596651 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4132645499/10000000000 : ℝ)^4391 ≤ (7896820756617/25000000000000 : ℝ)^3367 := by
    have hnat : (4132645499 : ℕ)^4391*25000000000000^3367 ≤ 7896820756617^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4132645499 10000000000 7896820756617 25000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4481456133/10000000000 : ℝ)^4391 ≤ (877699509131/2500000000000 : ℝ)^3367 := by
    have hnat : (4481456133 : ℕ)^4391*2500000000000^3367 ≤ 877699509131^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481456133 10000000000 877699509131 2500000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4303874983/10000000000 : ℝ), (4132645499/10000000000 : ℝ), (4481456133/10000000000 : ℝ)] ![(33304736596651/100000000000000 : ℝ), (7896820756617/25000000000000 : ℝ), (877699509131/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4303874983/10000000000 : ℝ)|^4391 ≤ (33304736596651/100000000000000 : ℝ)^3367
        have hw : |(4303874983/10000000000 : ℝ)|=(4303874983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4132645499/10000000000 : ℝ)|^4391 ≤ (7896820756617/25000000000000 : ℝ)^3367
        have hw : |(4132645499/10000000000 : ℝ)|=(4132645499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4481456133/10000000000 : ℝ)|^4391 ≤ (877699509131/2500000000000 : ℝ)^3367
        have hw : |(4481456133/10000000000 : ℝ)|=(4481456133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s7_4 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-492380591/2500000000 : ℝ)*x 0 + (2623776737/5000000000 : ℝ)*x 1 + (5407508931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (492380591/2500000000 : ℝ)^4391 ≤ (12015894286627/100000000000000 : ℝ)^3367 := by
    have hnat : (492380591 : ℕ)^4391*100000000000000^3367 ≤ 12015894286627^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492380591 2500000000 12015894286627 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623776737/5000000000 : ℝ)^4391 ≤ (5391353946431/12500000000000 : ℝ)^3367 := by
    have hnat : (2623776737 : ℕ)^4391*12500000000000^3367 ≤ 5391353946431^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623776737 5000000000 5391353946431 12500000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407508931/10000000000 : ℝ)^4391 ≤ (44853274123491/100000000000000 : ℝ)^3367 := by
    have hnat : (5407508931 : ℕ)^4391*100000000000000^3367 ≤ 44853274123491^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407508931 10000000000 44853274123491 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-492380591/2500000000 : ℝ), (2623776737/5000000000 : ℝ), (5407508931/10000000000 : ℝ)] ![(12015894286627/100000000000000 : ℝ), (5391353946431/12500000000000 : ℝ), (44853274123491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-492380591/2500000000 : ℝ)|^4391 ≤ (12015894286627/100000000000000 : ℝ)^3367
        have hw : |(-492380591/2500000000 : ℝ)|=(492380591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623776737/5000000000 : ℝ)|^4391 ≤ (5391353946431/12500000000000 : ℝ)^3367
        have hw : |(2623776737/5000000000 : ℝ)|=(2623776737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407508931/10000000000 : ℝ)|^4391 ≤ (44853274123491/100000000000000 : ℝ)^3367
        have hw : |(5407508931/10000000000 : ℝ)|=(5407508931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s7_5 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652691937/5000000000 : ℝ)*x 0 + (5407508909/10000000000 : ℝ)*x 1 + (-47275047/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652691937/5000000000 : ℝ)^4391 ≤ (43751747520061/100000000000000 : ℝ)^3367 := by
    have hnat : (2652691937 : ℕ)^4391*100000000000000^3367 ≤ 43751747520061^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652691937 5000000000 43751747520061 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407508909/10000000000 : ℝ)^4391 ≤ (44853273885511/100000000000000 : ℝ)^3367 := by
    have hnat : (5407508909 : ℕ)^4391*100000000000000^3367 ≤ 44853273885511^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407508909 10000000000 44853273885511 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47275047/250000000 : ℝ)^4391 ≤ (5697489291191/50000000000000 : ℝ)^3367 := by
    have hnat : (47275047 : ℕ)^4391*50000000000000^3367 ≤ 5697489291191^3367*250000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47275047 250000000 5697489291191 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652691937/5000000000 : ℝ), (5407508909/10000000000 : ℝ), (-47275047/250000000 : ℝ)] ![(43751747520061/100000000000000 : ℝ), (44853273885511/100000000000000 : ℝ), (5697489291191/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652691937/5000000000 : ℝ)|^4391 ≤ (43751747520061/100000000000000 : ℝ)^3367
        have hw : |(2652691937/5000000000 : ℝ)|=(2652691937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407508909/10000000000 : ℝ)|^4391 ≤ (44853273885511/100000000000000 : ℝ)^3367
        have hw : |(5407508909/10000000000 : ℝ)|=(5407508909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-47275047/250000000 : ℝ)|^4391 ≤ (5697489291191/50000000000000 : ℝ)^3367
        have hw : |(-47275047/250000000 : ℝ)|=(47275047/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s7_6 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075974873/2500000000 : ℝ)*x 0 + (4480199339/10000000000 : ℝ)*x 1 + (2066954361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075974873/2500000000 : ℝ)^4391 ≤ (8326245983919/25000000000000 : ℝ)^3367 := by
    have hnat : (1075974873 : ℕ)^4391*25000000000000^3367 ≤ 8326245983919^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075974873 2500000000 8326245983919 25000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4480199339/10000000000 : ℝ)^4391 ≤ (35095140732713/100000000000000 : ℝ)^3367 := by
    have hnat : (4480199339 : ℕ)^4391*100000000000000^3367 ≤ 35095140732713^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480199339 10000000000 35095140732713 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2066954361/5000000000 : ℝ)^4391 ≤ (31599875314493/100000000000000 : ℝ)^3367 := by
    have hnat : (2066954361 : ℕ)^4391*100000000000000^3367 ≤ 31599875314493^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066954361 5000000000 31599875314493 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075974873/2500000000 : ℝ), (4480199339/10000000000 : ℝ), (2066954361/5000000000 : ℝ)] ![(8326245983919/25000000000000 : ℝ), (35095140732713/100000000000000 : ℝ), (31599875314493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075974873/2500000000 : ℝ)|^4391 ≤ (8326245983919/25000000000000 : ℝ)^3367
        have hw : |(1075974873/2500000000 : ℝ)|=(1075974873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4480199339/10000000000 : ℝ)|^4391 ≤ (35095140732713/100000000000000 : ℝ)^3367
        have hw : |(4480199339/10000000000 : ℝ)|=(4480199339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2066954361/5000000000 : ℝ)|^4391 ≤ (31599875314493/100000000000000 : ℝ)^3367
        have hw : |(2066954361/5000000000 : ℝ)|=(2066954361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1431_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15824599/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (709/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (2269/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7379/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7379/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (709/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7379/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (709/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7379/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (709/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7379/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (709/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7379/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (709/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7379/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (709/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (709/6250 : ℝ) ^ (2195/512 : ℝ) ≤ (4432506644184359/50000000000000000000 : ℝ) := by
    have hpowers : (709/6250 : ℝ)^2195 ≤ (4432506644184359/50000000000000000000 : ℝ)^512 := by
      have hnat : (709 : ℕ)^2195*50000000000000000000^512 ≤ 4432506644184359^512*6250^2195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        709 6250 4432506644184359 50000000000000000000 2195 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (709/6250 : ℝ)) (X := (4432506644184359/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7379/50000 : ℝ) ^ (2195/512 : ℝ) ≤ (3423261246700901/12500000000000000000 : ℝ) := by
    have hpowers : (7379/50000 : ℝ)^2195 ≤ (3423261246700901/12500000000000000000 : ℝ)^512 := by
      have hnat : (7379 : ℕ)^2195*12500000000000000000^512 ≤ 3423261246700901^512*50000^2195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7379 50000 3423261246700901 12500000000000000000 2195 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7379/50000 : ℝ)) (X := (3423261246700901/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004432506644184359/25000000000000000000 : ℝ) ≤ (10000413537887873/10000000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (25004432506644184359/25000000000000000000 : ℝ)^512 ≤ (10000413537887873/10000000000000000 : ℝ)^2195 := by
      have hnat : (25004432506644184359 : ℕ)^512*10000000000000000^2195 ≤ 10000413537887873^2195*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004432506644184359 25000000000000000000 10000413537887873 10000000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000413537887873/10000000000000000 : ℝ)) (X := (25004432506644184359/25000000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018125551630987963/50000000000000000000 : ℝ) ≤ (10000845466329913/10000000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (50018125551630987963/50000000000000000000 : ℝ)^512 ≤ (10000845466329913/10000000000000000 : ℝ)^2195 := by
      have hnat : (50018125551630987963 : ℕ)^512*10000000000000000^2195 ≤ 10000845466329913^2195*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018125551630987963 50000000000000000000 10000845466329913 10000000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000845466329913/10000000000000000 : ℝ)) (X := (50018125551630987963/50000000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253423261246700901/6250000000000000000 : ℝ) ≤ (10001277394771953/10000000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (6253423261246700901/6250000000000000000 : ℝ)^512 ≤ (10001277394771953/10000000000000000 : ℝ)^2195 := by
      have hnat : (6253423261246700901 : ℕ)^512*10000000000000000^2195 ≤ 10001277394771953^2195*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253423261246700901 6250000000000000000 10001277394771953 10000000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001277394771953/10000000000000000 : ℝ)) (X := (6253423261246700901/6250000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4432506644184359/50000000000000000000 : ℝ) ≤ ((17065806112928097451/17070000000000000000 : ℝ)+2*(10798211051/8535000000000 : ℝ)*(709/6250 : ℝ))^(2195/512 : ℝ) := by
    rw [show (17065806112928097451/17070000000000000000 : ℝ)+2*(10798211051/8535000000000 : ℝ)*(709/6250 : ℝ)=(10000413537887873/10000000000000000 : ℝ) by norm_num, show 1+2*(4432506644184359/50000000000000000000 : ℝ)=(25004432506644184359/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3423261246700901/12500000000000000000 : ℝ)+(4432506644184359/50000000000000000000 : ℝ) ≤ ((17065806112928097451/17070000000000000000 : ℝ)+(10798211051/8535000000000 : ℝ)*((7379/50000 : ℝ)+(709/6250 : ℝ)))^(2195/512 : ℝ) := by
    rw [show (17065806112928097451/17070000000000000000 : ℝ)+(10798211051/8535000000000 : ℝ)*((7379/50000 : ℝ)+(709/6250 : ℝ))=(10000845466329913/10000000000000000 : ℝ) by norm_num, show 1+(3423261246700901/12500000000000000000 : ℝ)+(4432506644184359/50000000000000000000 : ℝ)=(50018125551630987963/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3423261246700901/12500000000000000000 : ℝ) ≤ ((17065806112928097451/17070000000000000000 : ℝ)+2*(10798211051/8535000000000 : ℝ)*(7379/50000 : ℝ))^(2195/512 : ℝ) := by
    rw [show (17065806112928097451/17070000000000000000 : ℝ)+2*(10798211051/8535000000000 : ℝ)*(7379/50000 : ℝ)=(10001277394771953/10000000000000000 : ℝ) by norm_num, show 1+2*(3423261246700901/12500000000000000000 : ℝ)=(6253423261246700901/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17065806112928097451/17070000000000000000 : ℝ)*(X 1 0+X 2 0)+(10798211051/8535000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (709/6250 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (17065806112928097451/17070000000000000000 : ℝ)) (alpha := (10798211051/8535000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17065806112928097451/17070000000000000000 : ℝ)*(X 0 1+X 2 1)+(10798211051/8535000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (709/6250 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (17065806112928097451/17070000000000000000 : ℝ)) (alpha := (10798211051/8535000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17065806112928097451/17070000000000000000 : ℝ)*(X 0 2+X 1 2)+(10798211051/8535000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (709/6250 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (17065806112928097451/17070000000000000000 : ℝ)) (alpha := (10798211051/8535000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-393902171/2000000000 : ℝ)*X 0 0+(338005911/625000000 : ℝ)*X 0 1+(262348549/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347278283/10000000000 : ℝ)*X 1 0+(-2051537497/10000000000 : ℝ)*X 1 1+(2623486951/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673640213/5000000000 : ℝ)*X 2 0+(2623485373/5000000000 : ℝ)*X 2 1+(-2051538829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4303874983/10000000000 : ℝ)*X 0 0+(4132645499/10000000000 : ℝ)*X 0 1+(4481456133/10000000000 : ℝ)*X 0 2+(4303874983/10000000000 : ℝ)*X 1 0+(4132645499/10000000000 : ℝ)*X 1 1+(4481456133/10000000000 : ℝ)*X 1 2+(4303874983/10000000000 : ℝ)*X 2 0+(4132645499/10000000000 : ℝ)*X 2 1+(4481456133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-492380591/2500000000 : ℝ)*X 0 0+(2623776737/5000000000 : ℝ)*X 0 1+(5407508931/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652691937/5000000000 : ℝ)*X 2 0+(5407508909/10000000000 : ℝ)*X 2 1+(-47275047/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s7_5 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1075974873/2500000000 : ℝ)*X 0 0+(4480199339/10000000000 : ℝ)*X 0 1+(2066954361/5000000000 : ℝ)*X 0 2+(1075974873/2500000000 : ℝ)*X 1 0+(4480199339/10000000000 : ℝ)*X 1 1+(2066954361/5000000000 : ℝ)*X 1 2+(1075974873/2500000000 : ℝ)*X 2 0+(4480199339/10000000000 : ℝ)*X 2 1+(2066954361/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s7_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (218715074145740881809580323/142250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (210988461/20000000000000 : ℝ)*(base23) + (156641941/50000000000000 : ℝ)*(lower2) + (195457059/100000000000000 : ℝ)*(upper4) + (36117309/100000000000000 : ℝ)*(lower5) + (4536758058463527/100000000000000 : ℝ)*(major0) + (4536758058463527/100000000000000 : ℝ)*(major1) + (4536758058463527/100000000000000 : ℝ)*(major2) + (3103250357059701/50000000000000 : ℝ)*(sp0) + (3103306841289959/50000000000000 : ℝ)*(sp1) + (775818903922967/12500000000000 : ℝ)*(sp2) + (716721944345549/25000000000000 : ℝ)*(sp3) + (28242115129/25000000000000 : ℝ)*(sp4) + (30698126939/50000000000000 : ℝ)*(sp5) + (2921142719/20000000000000 : ℝ)*(sp6) + (2866902383095791/100000000000000 : ℝ)*(f.failure) + (3103306841289959/50000000000000 : ℝ)*(f.sum) + (1443507553553/56900000000000000000000000 : ℝ)*base65 + (5599622896708056559/569000000000000000000000000000000 : ℝ)*base67 + (1943535946747056559/569000000000000000000000000000000 : ℝ)*base69 + (13781915980775056559/569000000000000000000000000000000 : ℝ)*base71 + (2329966750189/569000000000000000000000000 : ℝ)*base73 + (1012949146827056559/569000000000000000000000000000000 : ℝ)*base75 + (6602733270090943441/569000000000000000000000000000000 : ℝ)*base78 + (1808495374190056559/569000000000000000000000000000000 : ℝ)*base79 + (32307893553/56900000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1162809/1000000000000000000000 : ℝ)*base89 + (1162809/1000000000000000000000 : ℝ)*base91 + (1162809/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1431_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15824599/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (709/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1431_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1431_box_0 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1808991993/10000000000 : ℝ)*x 0 + (2693085857/5000000000 : ℝ)*x 1 + (1077234353/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1808991993/10000000000 : ℝ)^4391 ≤ (10754794355859/100000000000000 : ℝ)^3367 := by
    have hnat : (1808991993 : ℕ)^4391*100000000000000^3367 ≤ 10754794355859^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1808991993 10000000000 10754794355859 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693085857/5000000000 : ℝ)^4391 ≤ (44622602540413/100000000000000 : ℝ)^3367 := by
    have hnat : (2693085857 : ℕ)^4391*100000000000000^3367 ≤ 44622602540413^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693085857 5000000000 44622602540413 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077234353/2000000000 : ℝ)^4391 ≤ (4462260309143/10000000000000 : ℝ)^3367 := by
    have hnat : (1077234353 : ℕ)^4391*10000000000000^3367 ≤ 4462260309143^3367*2000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077234353 2000000000 4462260309143 10000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1808991993/10000000000 : ℝ), (2693085857/5000000000 : ℝ), (1077234353/2000000000 : ℝ)] ![(10754794355859/100000000000000 : ℝ), (44622602540413/100000000000000 : ℝ), (4462260309143/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1808991993/10000000000 : ℝ)|^4391 ≤ (10754794355859/100000000000000 : ℝ)^3367
        have hw : |(-1808991993/10000000000 : ℝ)|=(1808991993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693085857/5000000000 : ℝ)|^4391 ≤ (44622602540413/100000000000000 : ℝ)^3367
        have hw : |(2693085857/5000000000 : ℝ)|=(2693085857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077234353/2000000000 : ℝ)|^4391 ≤ (4462260309143/10000000000000 : ℝ)^3367
        have hw : |(1077234353/2000000000 : ℝ)|=(1077234353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_box_1 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286079197/10000000000 : ℝ)*x 0 + (-1946513217/10000000000 : ℝ)*x 1 + (1346542937/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286079197/10000000000 : ℝ)^4391 ≤ (4354424619233/10000000000000 : ℝ)^3367 := by
    have hnat : (5286079197 : ℕ)^4391*10000000000000^3367 ≤ 4354424619233^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286079197 10000000000 4354424619233 10000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1946513217/10000000000 : ℝ)^4391 ≤ (11833150885169/100000000000000 : ℝ)^3367 := by
    have hnat : (1946513217 : ℕ)^4391*100000000000000^3367 ≤ 11833150885169^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1946513217 10000000000 11833150885169 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346542937/2500000000 : ℝ)^4391 ≤ (22311301453879/50000000000000 : ℝ)^3367 := by
    have hnat : (1346542937 : ℕ)^4391*50000000000000^3367 ≤ 22311301453879^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346542937 2500000000 22311301453879 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286079197/10000000000 : ℝ), (-1946513217/10000000000 : ℝ), (1346542937/2500000000 : ℝ)] ![(4354424619233/10000000000000 : ℝ), (11833150885169/100000000000000 : ℝ), (22311301453879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286079197/10000000000 : ℝ)|^4391 ≤ (4354424619233/10000000000000 : ℝ)^3367
        have hw : |(5286079197/10000000000 : ℝ)|=(5286079197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1946513217/10000000000 : ℝ)|^4391 ≤ (11833150885169/100000000000000 : ℝ)^3367
        have hw : |(-1946513217/10000000000 : ℝ)|=(1946513217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346542937/2500000000 : ℝ)|^4391 ≤ (22311301453879/50000000000000 : ℝ)^3367
        have hw : |(1346542937/2500000000 : ℝ)|=(1346542937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_box_2 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286079171/10000000000 : ℝ)*x 0 + (168317867/312500000 : ℝ)*x 1 + (-973256629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286079171/10000000000 : ℝ)^4391 ≤ (43544245913017/100000000000000 : ℝ)^3367 := by
    have hnat : (5286079171 : ℕ)^4391*100000000000000^3367 ≤ 43544245913017^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286079171 10000000000 43544245913017 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168317867/312500000 : ℝ)^4391 ≤ (44622602864541/100000000000000 : ℝ)^3367 := by
    have hnat : (168317867 : ℕ)^4391*100000000000000^3367 ≤ 44622602864541^3367*312500000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168317867 312500000 44622602864541 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (973256629/5000000000 : ℝ)^4391 ≤ (11833151210217/100000000000000 : ℝ)^3367 := by
    have hnat : (973256629 : ℕ)^4391*100000000000000^3367 ≤ 11833151210217^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973256629 5000000000 11833151210217 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286079171/10000000000 : ℝ), (168317867/312500000 : ℝ), (-973256629/5000000000 : ℝ)] ![(43544245913017/100000000000000 : ℝ), (44622602864541/100000000000000 : ℝ), (11833151210217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286079171/10000000000 : ℝ)|^4391 ≤ (43544245913017/100000000000000 : ℝ)^3367
        have hw : |(5286079171/10000000000 : ℝ)|=(5286079171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168317867/312500000 : ℝ)|^4391 ≤ (44622602864541/100000000000000 : ℝ)^3367
        have hw : |(168317867/312500000 : ℝ)|=(168317867/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-973256629/5000000000 : ℝ)|^4391 ≤ (11833151210217/100000000000000 : ℝ)^3367
        have hw : |(-973256629/5000000000 : ℝ)|=(973256629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_box_3 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4450133067/10000000000 : ℝ)*x 0 + (846890109/2000000000 : ℝ)*x 1 + (1058612641/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4450133067/10000000000 : ℝ)^4391 ≤ (34788305348423/100000000000000 : ℝ)^3367 := by
    have hnat : (4450133067 : ℕ)^4391*100000000000000^3367 ≤ 34788305348423^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4450133067 10000000000 34788305348423 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846890109/2000000000 : ℝ)^4391 ≤ (6521169444721/20000000000000 : ℝ)^3367 := by
    have hnat : (846890109 : ℕ)^4391*20000000000000^3367 ≤ 6521169444721^3367*2000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846890109 2000000000 6521169444721 20000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058612641/2500000000 : ℝ)^4391 ≤ (16302923707201/50000000000000 : ℝ)^3367 := by
    have hnat : (1058612641 : ℕ)^4391*50000000000000^3367 ≤ 16302923707201^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058612641 2500000000 16302923707201 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4450133067/10000000000 : ℝ), (846890109/2000000000 : ℝ), (1058612641/2500000000 : ℝ)] ![(34788305348423/100000000000000 : ℝ), (6521169444721/20000000000000 : ℝ), (16302923707201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4450133067/10000000000 : ℝ)|^4391 ≤ (34788305348423/100000000000000 : ℝ)^3367
        have hw : |(4450133067/10000000000 : ℝ)|=(4450133067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846890109/2000000000 : ℝ)|^4391 ≤ (6521169444721/20000000000000 : ℝ)^3367
        have hw : |(846890109/2000000000 : ℝ)|=(846890109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1058612641/2500000000 : ℝ)|^4391 ≤ (16302923707201/50000000000000 : ℝ)^3367
        have hw : |(1058612641/2500000000 : ℝ)|=(1058612641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_box_4 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-533189997/2500000000 : ℝ)*x 0 + (164579871/312500000 : ℝ)*x 1 + (5266556097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533189997/2500000000 : ℝ)^4391 ≤ (3332684924399/25000000000000 : ℝ)^3367 := by
    have hnat : (533189997 : ℕ)^4391*25000000000000^3367 ≤ 3332684924399^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533189997 2500000000 3332684924399 25000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164579871/312500000 : ℝ)^4391 ≤ (21667314469257/50000000000000 : ℝ)^3367 := by
    have hnat : (164579871 : ℕ)^4391*50000000000000^3367 ≤ 21667314469257^3367*312500000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164579871 312500000 21667314469257 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266556097/10000000000 : ℝ)^4391 ≤ (1733385254117/4000000000000 : ℝ)^3367 := by
    have hnat : (5266556097 : ℕ)^4391*4000000000000^3367 ≤ 1733385254117^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266556097 10000000000 1733385254117 4000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-533189997/2500000000 : ℝ), (164579871/312500000 : ℝ), (5266556097/10000000000 : ℝ)] ![(3332684924399/25000000000000 : ℝ), (21667314469257/50000000000000 : ℝ), (1733385254117/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-533189997/2500000000 : ℝ)|^4391 ≤ (3332684924399/25000000000000 : ℝ)^3367
        have hw : |(-533189997/2500000000 : ℝ)|=(533189997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164579871/312500000 : ℝ)|^4391 ≤ (21667314469257/50000000000000 : ℝ)^3367
        have hw : |(164579871/312500000 : ℝ)|=(164579871/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266556097/10000000000 : ℝ)|^4391 ≤ (1733385254117/4000000000000 : ℝ)^3367
        have hw : |(5266556097/10000000000 : ℝ)|=(5266556097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_box_5 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369785879/10000000000 : ℝ)*x 0 + (-124693181/625000000 : ℝ)*x 1 + (210662219/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369785879/10000000000 : ℝ)^4391 ≤ (4444564767757/10000000000000 : ℝ)^3367 := by
    have hnat : (5369785879 : ℕ)^4391*10000000000000^3367 ≤ 4444564767757^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369785879 10000000000 4444564767757 10000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124693181/625000000 : ℝ)^4391 ≤ (12219727633311/100000000000000 : ℝ)^3367 := by
    have hnat : (124693181 : ℕ)^4391*100000000000000^3367 ≤ 12219727633311^3367*625000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124693181 625000000 12219727633311 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210662219/400000000 : ℝ)^4391 ≤ (2166731233921/5000000000000 : ℝ)^3367 := by
    have hnat : (210662219 : ℕ)^4391*5000000000000^3367 ≤ 2166731233921^3367*400000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210662219 400000000 2166731233921 5000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369785879/10000000000 : ℝ), (-124693181/625000000 : ℝ), (210662219/400000000 : ℝ)] ![(4444564767757/10000000000000 : ℝ), (12219727633311/100000000000000 : ℝ), (2166731233921/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369785879/10000000000 : ℝ)|^4391 ≤ (4444564767757/10000000000000 : ℝ)^3367
        have hw : |(5369785879/10000000000 : ℝ)|=(5369785879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-124693181/625000000 : ℝ)|^4391 ≤ (12219727633311/100000000000000 : ℝ)^3367
        have hw : |(-124693181/625000000 : ℝ)|=(124693181/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210662219/400000000 : ℝ)|^4391 ≤ (2166731233921/5000000000000 : ℝ)^3367
        have hw : |(210662219/400000000 : ℝ)|=(210662219/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_box_6 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1342446301/2500000000 : ℝ)*x 0 + (5266556717/10000000000 : ℝ)*x 1 + (-1995090139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342446301/2500000000 : ℝ)^4391 ≤ (888912807829/2000000000000 : ℝ)^3367 := by
    have hnat : (1342446301 : ℕ)^4391*2000000000000^3367 ≤ 888912807829^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342446301 2500000000 888912807829 2000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266556717/10000000000 : ℝ)^4391 ≤ (4333463800597/10000000000000 : ℝ)^3367 := by
    have hnat : (5266556717 : ℕ)^4391*10000000000000^3367 ≤ 4333463800597^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266556717 10000000000 4333463800597 10000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1995090139/10000000000 : ℝ)^4391 ≤ (6109860793329/50000000000000 : ℝ)^3367 := by
    have hnat : (1995090139 : ℕ)^4391*50000000000000^3367 ≤ 6109860793329^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1995090139 10000000000 6109860793329 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342446301/2500000000 : ℝ), (5266556717/10000000000 : ℝ), (-1995090139/10000000000 : ℝ)] ![(888912807829/2000000000000 : ℝ), (4333463800597/10000000000000 : ℝ), (6109860793329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342446301/2500000000 : ℝ)|^4391 ≤ (888912807829/2000000000000 : ℝ)^3367
        have hw : |(1342446301/2500000000 : ℝ)|=(1342446301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266556717/10000000000 : ℝ)|^4391 ≤ (4333463800597/10000000000000 : ℝ)^3367
        have hw : |(5266556717/10000000000 : ℝ)|=(5266556717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1995090139/10000000000 : ℝ)|^4391 ≤ (6109860793329/50000000000000 : ℝ)^3367
        have hw : |(-1995090139/10000000000 : ℝ)|=(1995090139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_box_7 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2078282801/5000000000 : ℝ)*x 0 + (4381183159/10000000000 : ℝ)*x 1 + (4381183743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2078282801/5000000000 : ℝ)^4391 ≤ (31825926221113/100000000000000 : ℝ)^3367 := by
    have hnat : (2078282801 : ℕ)^4391*100000000000000^3367 ≤ 31825926221113^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078282801 5000000000 31825926221113 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4381183159/10000000000 : ℝ)^4391 ≤ (34087033922781/100000000000000 : ℝ)^3367 := by
    have hnat : (4381183159 : ℕ)^4391*100000000000000^3367 ≤ 34087033922781^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4381183159 10000000000 34087033922781 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4381183743/10000000000 : ℝ)^4391 ≤ (17043519924181/50000000000000 : ℝ)^3367 := by
    have hnat : (4381183743 : ℕ)^4391*50000000000000^3367 ≤ 17043519924181^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4381183743 10000000000 17043519924181 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2078282801/5000000000 : ℝ), (4381183159/10000000000 : ℝ), (4381183743/10000000000 : ℝ)] ![(31825926221113/100000000000000 : ℝ), (34087033922781/100000000000000 : ℝ), (17043519924181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2078282801/5000000000 : ℝ)|^4391 ≤ (31825926221113/100000000000000 : ℝ)^3367
        have hw : |(2078282801/5000000000 : ℝ)|=(2078282801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4381183159/10000000000 : ℝ)|^4391 ≤ (34087033922781/100000000000000 : ℝ)^3367
        have hw : |(4381183159/10000000000 : ℝ)|=(4381183159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4381183743/10000000000 : ℝ)|^4391 ≤ (17043519924181/50000000000000 : ℝ)^3367
        have hw : |(4381183743/10000000000 : ℝ)|=(4381183743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_box_8 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-8064689/39062500 : ℝ)*x 0 + (5183809277/10000000000 : ℝ)*x 1 + (2700072429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8064689/39062500 : ℝ)^4391 ≤ (12777540505651/100000000000000 : ℝ)^3367 := by
    have hnat : (8064689 : ℕ)^4391*100000000000000^3367 ≤ 12777540505651^3367*39062500^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8064689 39062500 12777540505651 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183809277/10000000000 : ℝ)^4391 ≤ (42448827930637/100000000000000 : ℝ)^3367 := by
    have hnat : (5183809277 : ℕ)^4391*100000000000000^3367 ≤ 42448827930637^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183809277 10000000000 42448827930637 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700072429/5000000000 : ℝ)^4391 ≤ (44773631540389/100000000000000 : ℝ)^3367 := by
    have hnat : (2700072429 : ℕ)^4391*100000000000000^3367 ≤ 44773631540389^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700072429 5000000000 44773631540389 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8064689/39062500 : ℝ), (5183809277/10000000000 : ℝ), (2700072429/5000000000 : ℝ)] ![(12777540505651/100000000000000 : ℝ), (42448827930637/100000000000000 : ℝ), (44773631540389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8064689/39062500 : ℝ)|^4391 ≤ (12777540505651/100000000000000 : ℝ)^3367
        have hw : |(-8064689/39062500 : ℝ)|=(8064689/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183809277/10000000000 : ℝ)|^4391 ≤ (42448827930637/100000000000000 : ℝ)^3367
        have hw : |(5183809277/10000000000 : ℝ)|=(5183809277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700072429/5000000000 : ℝ)|^4391 ≤ (44773631540389/100000000000000 : ℝ)^3367
        have hw : |(2700072429/5000000000 : ℝ)|=(2700072429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_box_9 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319074243/2500000000 : ℝ)*x 0 + (-970356229/5000000000 : ℝ)*x 1 + (5400144653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319074243/2500000000 : ℝ)^4391 ≤ (43439187304827/100000000000000 : ℝ)^3367 := by
    have hnat : (1319074243 : ℕ)^4391*100000000000000^3367 ≤ 43439187304827^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319074243 2500000000 43439187304827 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (970356229/5000000000 : ℝ)^4391 ≤ (11787183351639/100000000000000 : ℝ)^3367 := by
    have hnat : (970356229 : ℕ)^4391*100000000000000^3367 ≤ 11787183351639^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970356229 5000000000 11787183351639 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400144653/10000000000 : ℝ)^4391 ≤ (4477362932377/10000000000000 : ℝ)^3367 := by
    have hnat : (5400144653 : ℕ)^4391*10000000000000^3367 ≤ 4477362932377^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400144653 10000000000 4477362932377 10000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319074243/2500000000 : ℝ), (-970356229/5000000000 : ℝ), (5400144653/10000000000 : ℝ)] ![(43439187304827/100000000000000 : ℝ), (11787183351639/100000000000000 : ℝ), (4477362932377/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319074243/2500000000 : ℝ)|^4391 ≤ (43439187304827/100000000000000 : ℝ)^3367
        have hw : |(1319074243/2500000000 : ℝ)|=(1319074243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-970356229/5000000000 : ℝ)|^4391 ≤ (11787183351639/100000000000000 : ℝ)^3367
        have hw : |(-970356229/5000000000 : ℝ)|=(970356229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400144653/10000000000 : ℝ)|^4391 ≤ (4477362932377/10000000000000 : ℝ)^3367
        have hw : |(5400144653/10000000000 : ℝ)|=(5400144653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_box_10 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319074391/2500000000 : ℝ)*x 0 + (5400144107/10000000000 : ℝ)*x 1 + (-970356201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319074391/2500000000 : ℝ)^4391 ≤ (21719596830491/50000000000000 : ℝ)^3367 := by
    have hnat : (1319074391 : ℕ)^4391*50000000000000^3367 ≤ 21719596830491^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319074391 2500000000 21719596830491 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400144107/10000000000 : ℝ)^4391 ≤ (22386811709997/50000000000000 : ℝ)^3367 := by
    have hnat : (5400144107 : ℕ)^4391*50000000000000^3367 ≤ 22386811709997^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400144107 10000000000 22386811709997 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (970356201/5000000000 : ℝ)^4391 ≤ (5893591454037/50000000000000 : ℝ)^3367 := by
    have hnat : (970356201 : ℕ)^4391*50000000000000^3367 ≤ 5893591454037^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970356201 5000000000 5893591454037 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319074391/2500000000 : ℝ), (5400144107/10000000000 : ℝ), (-970356201/5000000000 : ℝ)] ![(21719596830491/50000000000000 : ℝ), (22386811709997/50000000000000 : ℝ), (5893591454037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319074391/2500000000 : ℝ)|^4391 ≤ (21719596830491/50000000000000 : ℝ)^3367
        have hw : |(1319074391/2500000000 : ℝ)|=(1319074391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400144107/10000000000 : ℝ)|^4391 ≤ (22386811709997/50000000000000 : ℝ)^3367
        have hw : |(5400144107/10000000000 : ℝ)|=(5400144107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-970356201/5000000000 : ℝ)|^4391 ≤ (5893591454037/50000000000000 : ℝ)^3367
        have hw : |(-970356201/5000000000 : ℝ)|=(970356201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_box_11 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (896773839/2000000000 : ℝ)*x 0 + (4217295327/10000000000 : ℝ)*x 1 + (4217295487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (896773839/2000000000 : ℝ)^4391 ≤ (35132635708451/100000000000000 : ℝ)^3367 := by
    have hnat : (896773839 : ℕ)^4391*100000000000000^3367 ≤ 35132635708451^3367*2000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896773839 2000000000 35132635708451 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4217295327/10000000000 : ℝ)^4391 ≤ (6486736267793/20000000000000 : ℝ)^3367 := by
    have hnat : (4217295327 : ℕ)^4391*20000000000000^3367 ≤ 6486736267793^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4217295327 10000000000 6486736267793 20000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4217295487/10000000000 : ℝ)^4391 ≤ (32433682943697/100000000000000 : ℝ)^3367 := by
    have hnat : (4217295487 : ℕ)^4391*100000000000000^3367 ≤ 32433682943697^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4217295487 10000000000 32433682943697 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(896773839/2000000000 : ℝ), (4217295327/10000000000 : ℝ), (4217295487/10000000000 : ℝ)] ![(35132635708451/100000000000000 : ℝ), (6486736267793/20000000000000 : ℝ), (32433682943697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(896773839/2000000000 : ℝ)|^4391 ≤ (35132635708451/100000000000000 : ℝ)^3367
        have hw : |(896773839/2000000000 : ℝ)|=(896773839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4217295327/10000000000 : ℝ)|^4391 ≤ (6486736267793/20000000000000 : ℝ)^3367
        have hw : |(4217295327/10000000000 : ℝ)|=(4217295327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4217295487/10000000000 : ℝ)|^4391 ≤ (32433682943697/100000000000000 : ℝ)^3367
        have hw : |(4217295487/10000000000 : ℝ)|=(4217295487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_box_12 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-234671049/1250000000 : ℝ)*x 0 + (1366724647/2500000000 : ℝ)*x 1 + (5255428759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (234671049/1250000000 : ℝ)^4391 ≤ (5643978463763/50000000000000 : ℝ)^3367 := by
    have hnat : (234671049 : ℕ)^4391*50000000000000^3367 ≤ 5643978463763^3367*1250000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234671049 1250000000 5643978463763 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366724647/2500000000 : ℝ)^4391 ≤ (45496777623609/100000000000000 : ℝ)^3367 := by
    have hnat : (1366724647 : ℕ)^4391*100000000000000^3367 ≤ 45496777623609^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366724647 2500000000 45496777623609 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255428759/10000000000 : ℝ)^4391 ≤ (43215265427513/100000000000000 : ℝ)^3367 := by
    have hnat : (5255428759 : ℕ)^4391*100000000000000^3367 ≤ 43215265427513^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255428759 10000000000 43215265427513 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-234671049/1250000000 : ℝ), (1366724647/2500000000 : ℝ), (5255428759/10000000000 : ℝ)] ![(5643978463763/50000000000000 : ℝ), (45496777623609/100000000000000 : ℝ), (43215265427513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-234671049/1250000000 : ℝ)|^4391 ≤ (5643978463763/50000000000000 : ℝ)^3367
        have hw : |(-234671049/1250000000 : ℝ)|=(234671049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366724647/2500000000 : ℝ)|^4391 ≤ (45496777623609/100000000000000 : ℝ)^3367
        have hw : |(1366724647/2500000000 : ℝ)|=(1366724647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255428759/10000000000 : ℝ)|^4391 ≤ (43215265427513/100000000000000 : ℝ)^3367
        have hw : |(5255428759/10000000000 : ℝ)|=(5255428759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_box_13 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688784961/5000000000 : ℝ)*x 0 + (-249938809/1250000000 : ℝ)*x 1 + (5255429121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688784961/5000000000 : ℝ)^4391 ≤ (69577639253/156250000000 : ℝ)^3367 := by
    have hnat : (2688784961 : ℕ)^4391*156250000000^3367 ≤ 69577639253^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688784961 5000000000 69577639253 156250000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (249938809/1250000000 : ℝ)^4391 ≤ (12255041555969/100000000000000 : ℝ)^3367 := by
    have hnat : (249938809 : ℕ)^4391*100000000000000^3367 ≤ 12255041555969^3367*1250000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249938809 1250000000 12255041555969 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255429121/10000000000 : ℝ)^4391 ≤ (21607634654767/50000000000000 : ℝ)^3367 := by
    have hnat : (5255429121 : ℕ)^4391*50000000000000^3367 ≤ 21607634654767^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255429121 10000000000 21607634654767 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688784961/5000000000 : ℝ), (-249938809/1250000000 : ℝ), (5255429121/10000000000 : ℝ)] ![(69577639253/156250000000 : ℝ), (12255041555969/100000000000000 : ℝ), (21607634654767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688784961/5000000000 : ℝ)|^4391 ≤ (69577639253/156250000000 : ℝ)^3367
        have hw : |(2688784961/5000000000 : ℝ)|=(2688784961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-249938809/1250000000 : ℝ)|^4391 ≤ (12255041555969/100000000000000 : ℝ)^3367
        have hw : |(-249938809/1250000000 : ℝ)|=(249938809/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255429121/10000000000 : ℝ)|^4391 ≤ (21607634654767/50000000000000 : ℝ)^3367
        have hw : |(5255429121/10000000000 : ℝ)|=(5255429121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_box_14 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (336098101/625000000 : ℝ)*x 0 + (5255429817/10000000000 : ℝ)*x 1 + (-1999509951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336098101/625000000 : ℝ)^4391 ≤ (44529685817423/100000000000000 : ℝ)^3367 := by
    have hnat : (336098101 : ℕ)^4391*100000000000000^3367 ≤ 44529685817423^3367*625000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336098101 625000000 44529685817423 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255429817/10000000000 : ℝ)^4391 ≤ (4321527677331/10000000000000 : ℝ)^3367 := by
    have hnat : (5255429817 : ℕ)^4391*10000000000000^3367 ≤ 4321527677331^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255429817 10000000000 4321527677331 10000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1999509951/10000000000 : ℝ)^4391 ≤ (12255037391601/100000000000000 : ℝ)^3367 := by
    have hnat : (1999509951 : ℕ)^4391*100000000000000^3367 ≤ 12255037391601^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999509951 10000000000 12255037391601 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336098101/625000000 : ℝ), (5255429817/10000000000 : ℝ), (-1999509951/10000000000 : ℝ)] ![(44529685817423/100000000000000 : ℝ), (4321527677331/10000000000000 : ℝ), (12255037391601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336098101/625000000 : ℝ)|^4391 ≤ (44529685817423/100000000000000 : ℝ)^3367
        have hw : |(336098101/625000000 : ℝ)|=(336098101/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255429817/10000000000 : ℝ)|^4391 ≤ (4321527677331/10000000000000 : ℝ)^3367
        have hw : |(5255429817/10000000000 : ℝ)|=(5255429817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1999509951/10000000000 : ℝ)|^4391 ≤ (12255037391601/100000000000000 : ℝ)^3367
        have hw : |(-1999509951/10000000000 : ℝ)|=(1999509951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_box_15 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4128806761/10000000000 : ℝ)*x 0 + (4394822443/10000000000 : ℝ)*x 1 + (2197410917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4128806761/10000000000 : ℝ)^4391 ≤ (3943628026041/12500000000000 : ℝ)^3367 := by
    have hnat : (4128806761 : ℕ)^4391*12500000000000^3367 ≤ 3943628026041^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128806761 10000000000 3943628026041 12500000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4394822443/10000000000 : ℝ)^4391 ≤ (34225490979081/100000000000000 : ℝ)^3367 := by
    have hnat : (4394822443 : ℕ)^4391*100000000000000^3367 ≤ 34225490979081^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4394822443 10000000000 34225490979081 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2197410917/5000000000 : ℝ)^4391 ≤ (4278185599249/12500000000000 : ℝ)^3367 := by
    have hnat : (2197410917 : ℕ)^4391*12500000000000^3367 ≤ 4278185599249^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197410917 5000000000 4278185599249 12500000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4128806761/10000000000 : ℝ), (4394822443/10000000000 : ℝ), (2197410917/5000000000 : ℝ)] ![(3943628026041/12500000000000 : ℝ), (34225490979081/100000000000000 : ℝ), (4278185599249/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4128806761/10000000000 : ℝ)|^4391 ≤ (3943628026041/12500000000000 : ℝ)^3367
        have hw : |(4128806761/10000000000 : ℝ)|=(4128806761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4394822443/10000000000 : ℝ)|^4391 ≤ (34225490979081/100000000000000 : ℝ)^3367
        have hw : |(4394822443/10000000000 : ℝ)|=(4394822443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2197410917/5000000000 : ℝ)|^4391 ≤ (4278185599249/12500000000000 : ℝ)^3367
        have hw : |(2197410917/5000000000 : ℝ)|=(2197410917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1431_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15824599/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62901/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59117/100000 : ℝ) ∧ (4023/5000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (21173/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7379/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2269/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7379/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2269/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7379/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2269/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7379/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2269/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7379/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2269/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7379/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2269/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2269/20000 : ℝ) ^ (2195/512 : ℝ) ≤ (8868364027814577/100000000000000000000 : ℝ) := by
    have hpowers : (2269/20000 : ℝ)^2195 ≤ (8868364027814577/100000000000000000000 : ℝ)^512 := by
      have hnat : (2269 : ℕ)^2195*100000000000000000000^512 ≤ 8868364027814577^512*20000^2195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2269 20000 8868364027814577 100000000000000000000 2195 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2269/20000 : ℝ)) (X := (8868364027814577/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7379/50000 : ℝ) ^ (2195/512 : ℝ) ≤ (3423261246700901/12500000000000000000 : ℝ) := by
    have hpowers : (7379/50000 : ℝ)^2195 ≤ (3423261246700901/12500000000000000000 : ℝ)^512 := by
      have hnat : (7379 : ℕ)^2195*12500000000000000000^512 ≤ 3423261246700901^512*50000^2195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7379 50000 3423261246700901 12500000000000000000 2195 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7379/50000 : ℝ)) (X := (3423261246700901/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008868364027814577/50000000000000000000 : ℝ) ≤ (5000206847091789/5000000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (50008868364027814577/50000000000000000000 : ℝ)^512 ≤ (5000206847091789/5000000000000000 : ℝ)^2195 := by
      have hnat : (50008868364027814577 : ℕ)^512*5000000000000000^2195 ≤ 5000206847091789^2195*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008868364027814577 50000000000000000000 5000206847091789 5000000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000206847091789/5000000000000000 : ℝ)) (X := (50008868364027814577/50000000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007250890800284357/20000000000000000000 : ℝ) ≤ (10000845544466673/10000000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (20007250890800284357/20000000000000000000 : ℝ)^512 ≤ (10000845544466673/10000000000000000 : ℝ)^2195 := by
      have hnat : (20007250890800284357 : ℕ)^512*10000000000000000^2195 ≤ 10000845544466673^2195*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007250890800284357 20000000000000000000 10000845544466673 10000000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000845544466673/10000000000000000 : ℝ)) (X := (20007250890800284357/20000000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253423261246700901/6250000000000000000 : ℝ) ≤ (1250159674343721/1250000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (6253423261246700901/6250000000000000000 : ℝ)^512 ≤ (1250159674343721/1250000000000000 : ℝ)^2195 := by
      have hnat : (6253423261246700901 : ℕ)^512*1250000000000000^2195 ≤ 1250159674343721^2195*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253423261246700901 6250000000000000000 1250159674343721 1250000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250159674343721/1250000000000000 : ℝ)) (X := (6253423261246700901/6250000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8868364027814577/100000000000000000000 : ℝ) ≤ ((8530403313831281541/8532500000000000000 : ℝ)+2*(86370056619/68260000000000 : ℝ)*(2269/20000 : ℝ))^(2195/512 : ℝ) := by
    rw [show (8530403313831281541/8532500000000000000 : ℝ)+2*(86370056619/68260000000000 : ℝ)*(2269/20000 : ℝ)=(5000206847091789/5000000000000000 : ℝ) by norm_num, show 1+2*(8868364027814577/100000000000000000000 : ℝ)=(50008868364027814577/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3423261246700901/12500000000000000000 : ℝ)+(8868364027814577/100000000000000000000 : ℝ) ≤ ((8530403313831281541/8532500000000000000 : ℝ)+(86370056619/68260000000000 : ℝ)*((7379/50000 : ℝ)+(2269/20000 : ℝ)))^(2195/512 : ℝ) := by
    rw [show (8530403313831281541/8532500000000000000 : ℝ)+(86370056619/68260000000000 : ℝ)*((7379/50000 : ℝ)+(2269/20000 : ℝ))=(10000845544466673/10000000000000000 : ℝ) by norm_num, show 1+(3423261246700901/12500000000000000000 : ℝ)+(8868364027814577/100000000000000000000 : ℝ)=(20007250890800284357/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3423261246700901/12500000000000000000 : ℝ) ≤ ((8530403313831281541/8532500000000000000 : ℝ)+2*(86370056619/68260000000000 : ℝ)*(7379/50000 : ℝ))^(2195/512 : ℝ) := by
    rw [show (8530403313831281541/8532500000000000000 : ℝ)+2*(86370056619/68260000000000 : ℝ)*(7379/50000 : ℝ)=(1250159674343721/1250000000000000 : ℝ) by norm_num, show 1+2*(3423261246700901/12500000000000000000 : ℝ)=(6253423261246700901/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8530403313831281541/8532500000000000000 : ℝ)*(X 1 0+X 2 0)+(86370056619/68260000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (2269/20000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (8530403313831281541/8532500000000000000 : ℝ)) (alpha := (86370056619/68260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8530403313831281541/8532500000000000000 : ℝ)*(X 0 1+X 2 1)+(86370056619/68260000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (2269/20000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (8530403313831281541/8532500000000000000 : ℝ)) (alpha := (86370056619/68260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8530403313831281541/8532500000000000000 : ℝ)*(X 0 2+X 1 2)+(86370056619/68260000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (2269/20000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (8530403313831281541/8532500000000000000 : ℝ)) (alpha := (86370056619/68260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1808991993/10000000000 : ℝ)*X 0 0+(2693085857/5000000000 : ℝ)*X 0 1+(1077234353/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5286079197/10000000000 : ℝ)*X 1 0+(-1946513217/10000000000 : ℝ)*X 1 1+(1346542937/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5286079171/10000000000 : ℝ)*X 2 0+(168317867/312500000 : ℝ)*X 2 1+(-973256629/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4450133067/10000000000 : ℝ)*X 0 0+(846890109/2000000000 : ℝ)*X 0 1+(1058612641/2500000000 : ℝ)*X 0 2+(4450133067/10000000000 : ℝ)*X 1 0+(846890109/2000000000 : ℝ)*X 1 1+(1058612641/2500000000 : ℝ)*X 1 2+(4450133067/10000000000 : ℝ)*X 2 0+(846890109/2000000000 : ℝ)*X 2 1+(1058612641/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-533189997/2500000000 : ℝ)*X 0 0+(164579871/312500000 : ℝ)*X 0 1+(5266556097/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5369785879/10000000000 : ℝ)*X 1 0+(-124693181/625000000 : ℝ)*X 1 1+(210662219/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1342446301/2500000000 : ℝ)*X 2 0+(5266556717/10000000000 : ℝ)*X 2 1+(-1995090139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2078282801/5000000000 : ℝ)*X 0 0+(4381183159/10000000000 : ℝ)*X 0 1+(4381183743/10000000000 : ℝ)*X 0 2+(2078282801/5000000000 : ℝ)*X 1 0+(4381183159/10000000000 : ℝ)*X 1 1+(4381183743/10000000000 : ℝ)*X 1 2+(2078282801/5000000000 : ℝ)*X 2 0+(4381183159/10000000000 : ℝ)*X 2 1+(4381183743/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-8064689/39062500 : ℝ)*X 0 0+(5183809277/10000000000 : ℝ)*X 0 1+(2700072429/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1319074243/2500000000 : ℝ)*X 1 0+(-970356229/5000000000 : ℝ)*X 1 1+(5400144653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1319074391/2500000000 : ℝ)*X 2 0+(5400144107/10000000000 : ℝ)*X 2 1+(-970356201/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((896773839/2000000000 : ℝ)*X 0 0+(4217295327/10000000000 : ℝ)*X 0 1+(4217295487/10000000000 : ℝ)*X 0 2+(896773839/2000000000 : ℝ)*X 1 0+(4217295327/10000000000 : ℝ)*X 1 1+(4217295487/10000000000 : ℝ)*X 1 2+(896773839/2000000000 : ℝ)*X 2 0+(4217295327/10000000000 : ℝ)*X 2 1+(4217295487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-234671049/1250000000 : ℝ)*X 0 0+(1366724647/2500000000 : ℝ)*X 0 1+(5255428759/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2688784961/5000000000 : ℝ)*X 1 0+(-249938809/1250000000 : ℝ)*X 1 1+(5255429121/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((336098101/625000000 : ℝ)*X 2 0+(5255429817/10000000000 : ℝ)*X 2 1+(-1999509951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4128806761/10000000000 : ℝ)*X 0 0+(4394822443/10000000000 : ℝ)*X 0 1+(2197410917/5000000000 : ℝ)*X 0 2+(4128806761/10000000000 : ℝ)*X 1 0+(4394822443/10000000000 : ℝ)*X 1 1+(2197410917/5000000000 : ℝ)*X 1 2+(4128806761/10000000000 : ℝ)*X 2 0+(4394822443/10000000000 : ℝ)*X 2 1+(2197410917/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62901/100000 : ℝ) ≤ (-134169649856587574950229944850379/213312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (539037/1000000000000 : ℝ)*(lower1) + (130018449/100000000000000 : ℝ)*(lower2) + (177920079/100000000000000 : ℝ)*(lower3) + (70919241/100000000000000 : ℝ)*(lower4) + (3018953369409873/100000000000000 : ℝ)*(major0) + (3018953369409873/100000000000000 : ℝ)*(major1) + (3018953369409873/100000000000000 : ℝ)*(major2) + (2804443863/25000000000000 : ℝ)*(sp1) + (2075556501121011/50000000000000 : ℝ)*(sp4) + (4151101784466571/100000000000000 : ℝ)*(sp5) + (25942485987877/625000000000 : ℝ)*(sp6) + (476933038847727/25000000000000 : ℝ)*(sp7) + (157622090851/50000000000000 : ℝ)*(sp14) + (27636443231/100000000000000 : ℝ)*(sp15) + (1907759791834139/100000000000000 : ℝ)*(f.failure) + (2075556501121011/50000000000000 : ℝ)*(f.sum) + (2305083735717/426625000000000000000000000 : ℝ)*base66 + (8374458608872179293/853250000000000000000000000000000 : ℝ)*base67 + (6192427415307429293/853250000000000000000000000000000 : ℝ)*base69 + (1146829702258570707/853250000000000000000000000000000 : ℝ)*base72 + (7122902018661/1706500000000000000000000000 : ℝ)*base73 + (7223880224749679293/853250000000000000000000000000000 : ℝ)*base75 + (6023841694124679293/853250000000000000000000000000000 : ℝ)*base77 + (7082190331804679293/853250000000000000000000000000000 : ℝ)*base79 + (46230227693179/3413000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (5814739/1000000000000000000000 : ℝ)*base90 + (5814739/1000000000000000000000 : ℝ)*base92 + (5814739/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59117/100000 : ℝ) ≤ (504438462856145198986086309/853250000000000000000000000 : ℝ) := by norm_num
    linear_combination (4276449/100000000000000 : ℝ)*(lower0) + (4019841/20000000000000 : ℝ)*(upper2) + (3952353/100000000000000 : ℝ)*(lower5) + (3090637894841687/100000000000000 : ℝ)*(major0) + (3090637894841687/100000000000000 : ℝ)*(major1) + (3090637894841687/100000000000000 : ℝ)*(major2) + (263031780057971/6250000000000 : ℝ)*(sp0) + (420850893590499/10000000000000 : ℝ)*(sp1) + (1052127483299303/25000000000000 : ℝ)*(sp2) + (97652913478717/5000000000000 : ℝ)*(sp3) + (541917651/50000000000000 : ℝ)*(sp5) + (474222729/50000000000000 : ℝ)*(sp7) + (2163577/2500000000000 : ℝ)*(sp10) + (307762551/20000000000000 : ℝ)*(sp12) + (976529609009899/50000000000000 : ℝ)*(f.failure) + (1052127504935073/25000000000000 : ℝ)*(f.sum) + (515723007691/3413000000000000000000000000 : ℝ)*base66 + (6362376250712524667/853250000000000000000000000000000 : ℝ)*base67 + (2440843198700274667/853250000000000000000000000000000 : ℝ)*base69 + (1640653299795975333/853250000000000000000000000000000 : ℝ)*base72 + (10112452421847/3413000000000000000000000000 : ℝ)*base74 + (1639335230074024667/853250000000000000000000000000000 : ℝ)*base75 + (3453583339568975333/853250000000000000000000000000000 : ℝ)*base78 + (5518959898780475333/853250000000000000000000000000000 : ℝ)*base80 + (1713088425521/3413000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (3705501/500000000000000000000 : ℝ)*base89 + (3705501/500000000000000000000 : ℝ)*base91 + (3705501/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (4023/5000 : ℝ) ≤ (171635513542824520304613337390269/213312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51255747/25000000000000 : ℝ)*(lower3) + (4798631/5000000000000 : ℝ)*(upper4) + (19708117/50000000000000 : ℝ)*(lower5) + (1699216454671803/50000000000000 : ℝ)*(major0) + (1699216454671803/50000000000000 : ℝ)*(major1) + (1699216454671803/50000000000000 : ℝ)*(major2) + (7984087883/100000000000000 : ℝ)*(sp0) + (90816916159/50000000000000 : ℝ)*(sp1) + (27762807833/25000000000000 : ℝ)*(sp3) + (2311232326545449/50000000000000 : ℝ)*(sp8) + (4622300150696123/100000000000000 : ℝ)*(sp9) + (4622481784528441/100000000000000 : ℝ)*(sp10) + (2147452314730489/100000000000000 : ℝ)*(sp11) + (9147349659/100000000000000 : ℝ)*(sp12) + (2147563365961821/100000000000000 : ℝ)*(f.failure) + (4622481784528441/100000000000000 : ℝ)*(f.sum) + (194314464473/1706500000000000000000000000 : ℝ)*base66 + (2993013393146838423/426625000000000000000000000000000 : ℝ)*base67 + (71203181141161577/426625000000000000000000000000000 : ℝ)*base70 + (2923330492547411577/426625000000000000000000000000000 : ℝ)*base72 + (162159462579/27304000000000000000000000 : ℝ)*base73 + (1142432731671463423/426625000000000000000000000000000 : ℝ)*base75 + (3390011109870661577/426625000000000000000000000000000 : ℝ)*base78 + (603121141994536577/426625000000000000000000000000000 : ℝ)*base80 + (6307083180903/3413000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (6634779/1000000000000000000000 : ℝ)*base89 + (6634779/1000000000000000000000 : ℝ)*base91 + (6634779/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-21173/25000 : ℝ) ≤ (-1806539483931658284209756378559/2133125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (304104323/100000000000000 : ℝ)*(lower0) + (25296869/12500000000000 : ℝ)*(upper3) + (269241397/50000000000000 : ℝ)*(upper5) + (34359166466717/1000000000000 : ℝ)*(major0) + (34359166466717/1000000000000 : ℝ)*(major1) + (34359166466717/1000000000000 : ℝ)*(major2) + (1381253221/20000000000000 : ℝ)*(sp4) + (185895264631/100000000000000 : ℝ)*(sp5) + (10133125863/6250000000000 : ℝ)*(sp7) + (2901489367/25000000000000 : ℝ)*(sp8) + (472879434530911/10000000000000 : ℝ)*(sp12) + (4728626962268053/100000000000000 : ℝ)*(sp13) + (1182203214383171/25000000000000 : ℝ)*(sp14) + (1085544121031523/50000000000000 : ℝ)*(sp15) + (1085625186038427/50000000000000 : ℝ)*(f.failure) + (1182203214383171/25000000000000 : ℝ)*(f.sum) + (9607441087/2730400000000000000000000 : ℝ)*base66 + (6201888228749103/8532500000000000000000000000000 : ℝ)*base68 + (56467880563718397/8532500000000000000000000000000 : ℝ)*base69 + (89673178806606603/8532500000000000000000000000000 : ℝ)*base72 + (5660181934573/1706500000000000000000000000 : ℝ)*base73 + (60370115670149103/8532500000000000000000000000000 : ℝ)*base76 + (80962194512549103/8532500000000000000000000000000 : ℝ)*base78 + (114521574291689103/8532500000000000000000000000000 : ℝ)*base80 + (91686828697/853250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (5865773/500000000000000000000 : ℝ)*base89 + (5865773/500000000000000000000 : ℝ)*base91 + (5865773/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1431_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15824599/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62901/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59117/100000 : ℝ) else (4023/5000 : ℝ) ≤ X j i ∧ X j i ≤ (21173/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1431_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1431_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15824599/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62901/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59117/100000 : ℝ) else (4023/5000 : ℝ) ≤ X j i ∧ X j i ≤ (21173/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1431_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1431_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1431_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15824599/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62901/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59117/100000 : ℝ) else (4023/5000 : ℝ) ≤ X j i ∧ X j i ≤ (21173/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1431_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
