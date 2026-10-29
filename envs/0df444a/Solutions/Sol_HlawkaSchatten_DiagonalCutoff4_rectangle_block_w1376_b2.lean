-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1376_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:22:06.832818+00:00
-- url     : https://prove2.me/submissions/049ca4c0-9d49-479d-8e4d-971dcad6dcf3

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
theorem support_rectangle_w1376_s6_0 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2014955897/10000000000 : ℝ)*x 0 + (541096163/1000000000 : ℝ)*x 1 + (2622793319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2014955897/10000000000 : ℝ)^271 ≤ (6139446852829/50000000000000 : ℝ)^207 := by
    have hnat : (2014955897 : ℕ)^271*50000000000000^207 ≤ 6139446852829^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014955897 10000000000 6139446852829 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541096163/1000000000 : ℝ)^271 ≤ (44751601840897/100000000000000 : ℝ)^207 := by
    have hnat : (541096163 : ℕ)^271*100000000000000^207 ≤ 44751601840897^207*1000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541096163 1000000000 44751601840897 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622793319/5000000000 : ℝ)^271 ≤ (2148475222481/5000000000000 : ℝ)^207 := by
    have hnat : (2622793319 : ℕ)^271*5000000000000^207 ≤ 2148475222481^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622793319 5000000000 2148475222481 5000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2014955897/10000000000 : ℝ), (541096163/1000000000 : ℝ), (2622793319/5000000000 : ℝ)] ![(6139446852829/50000000000000 : ℝ), (44751601840897/100000000000000 : ℝ), (2148475222481/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2014955897/10000000000 : ℝ)|^271 ≤ (6139446852829/50000000000000 : ℝ)^207
        have hw : |(-2014955897/10000000000 : ℝ)|=(2014955897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541096163/1000000000 : ℝ)|^271 ≤ (44751601840897/100000000000000 : ℝ)^207
        have hw : |(541096163/1000000000 : ℝ)|=(541096163/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622793319/5000000000 : ℝ)|^271 ≤ (2148475222481/5000000000000 : ℝ)^207
        have hw : |(2622793319/5000000000 : ℝ)|=(2622793319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s6_1 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1069677467/2000000000 : ℝ)*x 0 + (-1049594811/5000000000 : ℝ)*x 1 + (2622793319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069677467/2000000000 : ℝ)^271 ≤ (8815057104807/20000000000000 : ℝ)^207 := by
    have hnat : (1069677467 : ℕ)^271*20000000000000^207 ≤ 8815057104807^207*2000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069677467 2000000000 8815057104807 20000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049594811/5000000000 : ℝ)^271 ≤ (12955210015669/100000000000000 : ℝ)^207 := by
    have hnat : (1049594811 : ℕ)^271*100000000000000^207 ≤ 12955210015669^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049594811 5000000000 12955210015669 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622793319/5000000000 : ℝ)^271 ≤ (2148475222481/5000000000000 : ℝ)^207 := by
    have hnat : (2622793319 : ℕ)^271*5000000000000^207 ≤ 2148475222481^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622793319 5000000000 2148475222481 5000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069677467/2000000000 : ℝ), (-1049594811/5000000000 : ℝ), (2622793319/5000000000 : ℝ)] ![(8815057104807/20000000000000 : ℝ), (12955210015669/100000000000000 : ℝ), (2148475222481/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069677467/2000000000 : ℝ)|^271 ≤ (8815057104807/20000000000000 : ℝ)^207
        have hw : |(1069677467/2000000000 : ℝ)|=(1069677467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1049594811/5000000000 : ℝ)|^271 ≤ (12955210015669/100000000000000 : ℝ)^207
        have hw : |(-1049594811/5000000000 : ℝ)|=(1049594811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622793319/5000000000 : ℝ)|^271 ≤ (2148475222481/5000000000000 : ℝ)^207
        have hw : |(2622793319/5000000000 : ℝ)|=(2622793319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s6_2 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1069677467/2000000000 : ℝ)*x 0 + (2622793319/5000000000 : ℝ)*x 1 + (-1049594811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069677467/2000000000 : ℝ)^271 ≤ (8815057104807/20000000000000 : ℝ)^207 := by
    have hnat : (1069677467 : ℕ)^271*20000000000000^207 ≤ 8815057104807^207*2000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069677467 2000000000 8815057104807 20000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622793319/5000000000 : ℝ)^271 ≤ (2148475222481/5000000000000 : ℝ)^207 := by
    have hnat : (2622793319 : ℕ)^271*5000000000000^207 ≤ 2148475222481^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622793319 5000000000 2148475222481 5000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049594811/5000000000 : ℝ)^271 ≤ (12955210015669/100000000000000 : ℝ)^207 := by
    have hnat : (1049594811 : ℕ)^271*100000000000000^207 ≤ 12955210015669^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049594811 5000000000 12955210015669 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069677467/2000000000 : ℝ), (2622793319/5000000000 : ℝ), (-1049594811/5000000000 : ℝ)] ![(8815057104807/20000000000000 : ℝ), (2148475222481/5000000000000 : ℝ), (12955210015669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069677467/2000000000 : ℝ)|^271 ≤ (8815057104807/20000000000000 : ℝ)^207
        have hw : |(1069677467/2000000000 : ℝ)|=(1069677467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622793319/5000000000 : ℝ)|^271 ≤ (2148475222481/5000000000000 : ℝ)^207
        have hw : |(2622793319/5000000000 : ℝ)|=(2622793319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1049594811/5000000000 : ℝ)|^271 ≤ (12955210015669/100000000000000 : ℝ)^207
        have hw : |(-1049594811/5000000000 : ℝ)|=(1049594811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s6_3 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4317806117/10000000000 : ℝ)*x 0 + (4048509/9765625 : ℝ)*x 1 + (2248249677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317806117/10000000000 : ℝ)^271 ≤ (6660767091/20000000000 : ℝ)^207 := by
    have hnat : (4317806117 : ℕ)^271*20000000000^207 ≤ 6660767091^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317806117 10000000000 6660767091 20000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4048509/9765625 : ℝ)^271 ≤ (31576470781309/100000000000000 : ℝ)^207 := by
    have hnat : (4048509 : ℕ)^271*100000000000000^207 ≤ 31576470781309^207*9765625^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4048509 9765625 31576470781309 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248249677/5000000000 : ℝ)^271 ≤ (8779923439009/25000000000000 : ℝ)^207 := by
    have hnat : (2248249677 : ℕ)^271*25000000000000^207 ≤ 8779923439009^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248249677 5000000000 8779923439009 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317806117/10000000000 : ℝ), (4048509/9765625 : ℝ), (2248249677/5000000000 : ℝ)] ![(6660767091/20000000000 : ℝ), (31576470781309/100000000000000 : ℝ), (8779923439009/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317806117/10000000000 : ℝ)|^271 ≤ (6660767091/20000000000 : ℝ)^207
        have hw : |(4317806117/10000000000 : ℝ)|=(4317806117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4048509/9765625 : ℝ)|^271 ≤ (31576470781309/100000000000000 : ℝ)^207
        have hw : |(4048509/9765625 : ℝ)|=(4048509/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2248249677/5000000000 : ℝ)|^271 ≤ (8779923439009/25000000000000 : ℝ)^207
        have hw : |(2248249677/5000000000 : ℝ)|=(2248249677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s6_4 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-503741933/2500000000 : ℝ)*x 0 + (2623090203/5000000000 : ℝ)*x 1 + (5410364791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (503741933/2500000000 : ℝ)^271 ≤ (12278988125071/100000000000000 : ℝ)^207 := by
    have hnat : (503741933 : ℕ)^271*100000000000000^207 ≤ 12278988125071^207*2500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503741933 2500000000 12278988125071 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623090203/5000000000 : ℝ)^271 ≤ (21487936126271/50000000000000 : ℝ)^207 := by
    have hnat : (2623090203 : ℕ)^271*50000000000000^207 ≤ 21487936126271^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623090203 5000000000 21487936126271 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410364791/10000000000 : ℝ)^271 ≤ (44745139604149/100000000000000 : ℝ)^207 := by
    have hnat : (5410364791 : ℕ)^271*100000000000000^207 ≤ 44745139604149^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410364791 10000000000 44745139604149 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-503741933/2500000000 : ℝ), (2623090203/5000000000 : ℝ), (5410364791/10000000000 : ℝ)] ![(12278988125071/100000000000000 : ℝ), (21487936126271/50000000000000 : ℝ), (44745139604149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-503741933/2500000000 : ℝ)|^271 ≤ (12278988125071/100000000000000 : ℝ)^207
        have hw : |(-503741933/2500000000 : ℝ)|=(503741933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623090203/5000000000 : ℝ)|^271 ≤ (21487936126271/50000000000000 : ℝ)^207
        have hw : |(2623090203/5000000000 : ℝ)|=(2623090203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410364791/10000000000 : ℝ)|^271 ≤ (44745139604149/100000000000000 : ℝ)^207
        have hw : |(5410364791/10000000000 : ℝ)|=(5410364791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s6_5 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5305628293/10000000000 : ℝ)*x 0 + (-77376459/400000000 : ℝ)*x 1 + (2705182397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305628293/10000000000 : ℝ)^271 ≤ (872290800029/2000000000000 : ℝ)^207 := by
    have hnat : (5305628293 : ℕ)^271*2000000000000^207 ≤ 872290800029^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305628293 10000000000 872290800029 2000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (77376459/400000000 : ℝ)^271 ≤ (5820160172151/50000000000000 : ℝ)^207 := by
    have hnat : (77376459 : ℕ)^271*50000000000000^207 ≤ 5820160172151^207*400000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77376459 400000000 5820160172151 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705182397/5000000000 : ℝ)^271 ≤ (44745139636631/100000000000000 : ℝ)^207 := by
    have hnat : (2705182397 : ℕ)^271*100000000000000^207 ≤ 44745139636631^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705182397 5000000000 44745139636631 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305628293/10000000000 : ℝ), (-77376459/400000000 : ℝ), (2705182397/5000000000 : ℝ)] ![(872290800029/2000000000000 : ℝ), (5820160172151/50000000000000 : ℝ), (44745139636631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305628293/10000000000 : ℝ)|^271 ≤ (872290800029/2000000000000 : ℝ)^207
        have hw : |(5305628293/10000000000 : ℝ)|=(5305628293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-77376459/400000000 : ℝ)|^271 ≤ (5820160172151/50000000000000 : ℝ)^207
        have hw : |(-77376459/400000000 : ℝ)|=(77376459/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705182397/5000000000 : ℝ)|^271 ≤ (44745139636631/100000000000000 : ℝ)^207
        have hw : |(2705182397/5000000000 : ℝ)|=(2705182397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s6_6 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2652814151/5000000000 : ℝ)*x 0 + (1352591197/2500000000 : ℝ)*x 1 + (-193441147/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652814151/5000000000 : ℝ)^271 ≤ (10903635024577/25000000000000 : ℝ)^207 := by
    have hnat : (2652814151 : ℕ)^271*25000000000000^207 ≤ 10903635024577^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652814151 5000000000 10903635024577 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352591197/2500000000 : ℝ)^271 ≤ (44745139571667/100000000000000 : ℝ)^207 := by
    have hnat : (1352591197 : ℕ)^271*100000000000000^207 ≤ 44745139571667^207*2500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352591197 2500000000 44745139571667 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (193441147/1000000000 : ℝ)^271 ≤ (727520019057/6250000000000 : ℝ)^207 := by
    have hnat : (193441147 : ℕ)^271*6250000000000^207 ≤ 727520019057^207*1000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193441147 1000000000 727520019057 6250000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652814151/5000000000 : ℝ), (1352591197/2500000000 : ℝ), (-193441147/1000000000 : ℝ)] ![(10903635024577/25000000000000 : ℝ), (44745139571667/100000000000000 : ℝ), (727520019057/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652814151/5000000000 : ℝ)|^271 ≤ (10903635024577/25000000000000 : ℝ)^207
        have hw : |(2652814151/5000000000 : ℝ)|=(2652814151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352591197/2500000000 : ℝ)|^271 ≤ (44745139571667/100000000000000 : ℝ)^207
        have hw : |(1352591197/2500000000 : ℝ)|=(1352591197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-193441147/1000000000 : ℝ)|^271 ≤ (727520019057/6250000000000 : ℝ)^207
        have hw : |(-193441147/1000000000 : ℝ)|=(193441147/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s6_7 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (172713249/400000000 : ℝ)*x 0 + (112380993/250000000 : ℝ)*x 1 + (829387869/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172713249/400000000 : ℝ)^271 ≤ (16652044496357/50000000000000 : ℝ)^207 := by
    have hnat : (172713249 : ℕ)^271*50000000000000^207 ≤ 16652044496357^207*400000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172713249 400000000 16652044496357 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112380993/250000000 : ℝ)^271 ≤ (35106814205853/100000000000000 : ℝ)^207 := by
    have hnat : (112380993 : ℕ)^271*100000000000000^207 ≤ 35106814205853^207*250000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112380993 250000000 35106814205853 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (829387869/2000000000 : ℝ)^271 ≤ (3948637098179/12500000000000 : ℝ)^207 := by
    have hnat : (829387869 : ℕ)^271*12500000000000^207 ≤ 3948637098179^207*2000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829387869 2000000000 3948637098179 12500000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172713249/400000000 : ℝ), (112380993/250000000 : ℝ), (829387869/2000000000 : ℝ)] ![(16652044496357/50000000000000 : ℝ), (35106814205853/100000000000000 : ℝ), (3948637098179/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172713249/400000000 : ℝ)|^271 ≤ (16652044496357/50000000000000 : ℝ)^207
        have hw : |(172713249/400000000 : ℝ)|=(172713249/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(112380993/250000000 : ℝ)|^271 ≤ (35106814205853/100000000000000 : ℝ)^207
        have hw : |(112380993/250000000 : ℝ)|=(112380993/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(829387869/2000000000 : ℝ)|^271 ≤ (3948637098179/12500000000000 : ℝ)^207
        have hw : |(829387869/2000000000 : ℝ)|=(829387869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1376_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (609648/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7367/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5613/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1841/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7367/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11221/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7367/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11221/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7367/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11221/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7367/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11221/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7367/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11221/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7367/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11221/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11221/100000 : ℝ) ^ (4335/1024 : ℝ) ≤ (951491910829911/10000000000000000000 : ℝ) := by
    have hpowers : (11221/100000 : ℝ)^4335 ≤ (951491910829911/10000000000000000000 : ℝ)^1024 := by
      have hnat : (11221 : ℕ)^4335*10000000000000000000^1024 ≤ 951491910829911^1024*100000^4335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11221 100000 951491910829911 10000000000000000000 4335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11221/100000 : ℝ)) (X := (951491910829911/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7367/50000 : ℝ) ^ (4335/1024 : ℝ) ≤ (30141856985718727/100000000000000000000 : ℝ) := by
    have hpowers : (7367/50000 : ℝ)^4335 ≤ (30141856985718727/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7367 : ℕ)^4335*100000000000000000000^1024 ≤ 30141856985718727^1024*50000^4335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7367 50000 30141856985718727 100000000000000000000 4335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7367/50000 : ℝ)) (X := (30141856985718727/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000951491910829911/5000000000000000000 : ℝ) ≤ (10000449484160071/10000000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (5000951491910829911/5000000000000000000 : ℝ)^1024 ≤ (10000449484160071/10000000000000000 : ℝ)^4335 := by
      have hnat : (5000951491910829911 : ℕ)^1024*10000000000000000^4335 ≤ 10000449484160071^4335*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000951491910829911 5000000000000000000 10000449484160071 10000000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000449484160071/10000000000000000 : ℝ)) (X := (5000951491910829911/5000000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039656776094017837/100000000000000000000 : ℝ) ≤ (5000468308998357/5000000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (100039656776094017837/100000000000000000000 : ℝ)^1024 ≤ (5000468308998357/5000000000000000 : ℝ)^4335 := by
      have hnat : (100039656776094017837 : ℕ)^1024*5000000000000000^4335 ≤ 5000468308998357^4335*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039656776094017837 100000000000000000000 5000468308998357 5000000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000468308998357/5000000000000000 : ℝ)) (X := (100039656776094017837/100000000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030141856985718727/50000000000000000000 : ℝ) ≤ (10001423751833357/10000000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (50030141856985718727/50000000000000000000 : ℝ)^1024 ≤ (10001423751833357/10000000000000000 : ℝ)^4335 := by
      have hnat : (50030141856985718727 : ℕ)^1024*10000000000000000^4335 ≤ 10001423751833357^4335*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030141856985718727 50000000000000000000 10001423751833357 10000000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001423751833357/10000000000000000 : ℝ)) (X := (50030141856985718727/50000000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(951491910829911/10000000000000000000 : ℝ) ≤ ((35120646780292387217/35130000000000000000 : ℝ)+2*(487133836643/351300000000000 : ℝ)*(11221/100000 : ℝ))^(4335/1024 : ℝ) := by
    rw [show (35120646780292387217/35130000000000000000 : ℝ)+2*(487133836643/351300000000000 : ℝ)*(11221/100000 : ℝ)=(10000449484160071/10000000000000000 : ℝ) by norm_num, show 1+2*(951491910829911/10000000000000000000 : ℝ)=(5000951491910829911/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30141856985718727/100000000000000000000 : ℝ)+(951491910829911/10000000000000000000 : ℝ) ≤ ((35120646780292387217/35130000000000000000 : ℝ)+(487133836643/351300000000000 : ℝ)*((7367/50000 : ℝ)+(11221/100000 : ℝ)))^(4335/1024 : ℝ) := by
    rw [show (35120646780292387217/35130000000000000000 : ℝ)+(487133836643/351300000000000 : ℝ)*((7367/50000 : ℝ)+(11221/100000 : ℝ))=(5000468308998357/5000000000000000 : ℝ) by norm_num, show 1+(30141856985718727/100000000000000000000 : ℝ)+(951491910829911/10000000000000000000 : ℝ)=(100039656776094017837/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30141856985718727/100000000000000000000 : ℝ) ≤ ((35120646780292387217/35130000000000000000 : ℝ)+2*(487133836643/351300000000000 : ℝ)*(7367/50000 : ℝ))^(4335/1024 : ℝ) := by
    rw [show (35120646780292387217/35130000000000000000 : ℝ)+2*(487133836643/351300000000000 : ℝ)*(7367/50000 : ℝ)=(10001423751833357/10000000000000000 : ℝ) by norm_num, show 1+2*(30141856985718727/100000000000000000000 : ℝ)=(50030141856985718727/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35120646780292387217/35130000000000000000 : ℝ)*(X 1 0+X 2 0)+(487133836643/351300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (11221/100000 : ℝ)) (hi := (7367/50000 : ℝ)) (c := (35120646780292387217/35130000000000000000 : ℝ)) (alpha := (487133836643/351300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35120646780292387217/35130000000000000000 : ℝ)*(X 0 1+X 2 1)+(487133836643/351300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (11221/100000 : ℝ)) (hi := (7367/50000 : ℝ)) (c := (35120646780292387217/35130000000000000000 : ℝ)) (alpha := (487133836643/351300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35120646780292387217/35130000000000000000 : ℝ)*(X 0 2+X 1 2)+(487133836643/351300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (11221/100000 : ℝ)) (hi := (7367/50000 : ℝ)) (c := (35120646780292387217/35130000000000000000 : ℝ)) (alpha := (487133836643/351300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2014955897/10000000000 : ℝ)*X 0 0+(541096163/1000000000 : ℝ)*X 0 1+(2622793319/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069677467/2000000000 : ℝ)*X 1 0+(-1049594811/5000000000 : ℝ)*X 1 1+(2622793319/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069677467/2000000000 : ℝ)*X 2 0+(2622793319/5000000000 : ℝ)*X 2 1+(-1049594811/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4317806117/10000000000 : ℝ)*X 0 0+(4048509/9765625 : ℝ)*X 0 1+(2248249677/5000000000 : ℝ)*X 0 2+(4317806117/10000000000 : ℝ)*X 1 0+(4048509/9765625 : ℝ)*X 1 1+(2248249677/5000000000 : ℝ)*X 1 2+(4317806117/10000000000 : ℝ)*X 2 0+(4048509/9765625 : ℝ)*X 2 1+(2248249677/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-503741933/2500000000 : ℝ)*X 0 0+(2623090203/5000000000 : ℝ)*X 0 1+(5410364791/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305628293/10000000000 : ℝ)*X 1 0+(-77376459/400000000 : ℝ)*X 1 1+(2705182397/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652814151/5000000000 : ℝ)*X 2 0+(1352591197/2500000000 : ℝ)*X 2 1+(-193441147/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((172713249/400000000 : ℝ)*X 0 0+(112380993/250000000 : ℝ)*X 0 1+(829387869/2000000000 : ℝ)*X 0 2+(172713249/400000000 : ℝ)*X 1 0+(112380993/250000000 : ℝ)*X 1 1+(829387869/2000000000 : ℝ)*X 1 2+(172713249/400000000 : ℝ)*X 2 0+(112380993/250000000 : ℝ)*X 2 1+(829387869/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3414915948883506150504214573/292750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2162348627/100000000000000 : ℝ)*(base19) + (2015556549/100000000000000 : ℝ)*(base23) + (9813761/12500000000000 : ℝ)*(lower2) + (72924433/25000000000000 : ℝ)*(upper3) + (46009881/25000000000000 : ℝ)*(upper5) + (2224353304169869/50000000000000 : ℝ)*(major0) + (2224353304169869/50000000000000 : ℝ)*(major1) + (2224353304169869/50000000000000 : ℝ)*(major2) + (1511727534745731/25000000000000 : ℝ)*(sp0) + (6046952665337051/100000000000000 : ℝ)*(sp1) + (755869101516141/12500000000000 : ℝ)*(sp2) + (1425217600022897/50000000000000 : ℝ)*(sp3) + (22344351377/50000000000000 : ℝ)*(sp4) + (570002903/2500000000000 : ℝ)*(sp7) + (2850458000161913/100000000000000 : ℝ)*(f.failure) + (3023477413842839/50000000000000 : ℝ)*(f.sum) + (8709549331837/2195625000000000000000000000 : ℝ)*base66 + (8257462182493135427/1756500000000000000000000000000000 : ℝ)*base68 + (9633993035644135427/1756500000000000000000000000000000 : ℝ)*base70 + (8857814386329364573/1756500000000000000000000000000000 : ℝ)*base71 + (6019300606537/2195625000000000000000000000 : ℝ)*base74 + (15411904259377864573/1756500000000000000000000000000000 : ℝ)*base75 + (811972446088135427/1756500000000000000000000000000000 : ℝ)*base78 + (11041773625723135427/1756500000000000000000000000000000 : ℝ)*base80 + (59755174903183/8782500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (109813/19531250000000000000 : ℝ)*base90 + (109813/19531250000000000000 : ℝ)*base92 + (109813/19531250000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1494403642240248627761863629/292750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (877616281/100000000000000 : ℝ)*(base19) + (965692561/100000000000000 : ℝ)*(base23) + (1648427/1562500000000 : ℝ)*(upper3) + (4350761/12500000000000 : ℝ)*(lower4) + (6835167/6250000000000 : ℝ)*(upper5) + (2240449419089837/50000000000000 : ℝ)*(major0) + (2240449419089837/50000000000000 : ℝ)*(major1) + (2240449419089837/50000000000000 : ℝ)*(major2) + (3630599507/20000000000000 : ℝ)*(sp1) + (19659647347/100000000000000 : ℝ)*(sp2) + (6090712702079437/100000000000000 : ℝ)*(sp4) + (6090693671465621/100000000000000 : ℝ)*(sp5) + (6090692076739529/100000000000000 : ℝ)*(sp6) + (2871084804122929/100000000000000 : ℝ)*(sp7) + (2871084804122929/100000000000000 : ℝ)*(f.failure) + (6090712702079437/100000000000000 : ℝ)*(f.sum) + (34637773502717/17565000000000000000000000000 : ℝ)*base65 + (9185774158130486371/1756500000000000000000000000000000 : ℝ)*base68 + (14742273734285486371/1756500000000000000000000000000000 : ℝ)*base70 + (12882819999263013629/1756500000000000000000000000000000 : ℝ)*base71 + (9110072081893/17565000000000000000000000000 : ℝ)*base74 + (22051515144674013629/1756500000000000000000000000000000 : ℝ)*base75 + (1469657122349486371/1756500000000000000000000000000000 : ℝ)*base78 + (17827302414434486371/1756500000000000000000000000000000 : ℝ)*base80 + (100008137440783/17565000000000000000000000000 : ℝ)*base82 + (131371/19531250000000000000 : ℝ)*base89 + (131371/19531250000000000000 : ℝ)*base91 + (131371/19531250000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1376_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (609648/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7367/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1376_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1376_s7_0 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2014962659/10000000000 : ℝ)*x 0 + (5410917371/10000000000 : ℝ)*x 1 + (5245626293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2014962659/10000000000 : ℝ)^271 ≤ (12278947652749/100000000000000 : ℝ)^207 := by
    have hnat : (2014962659 : ℕ)^271*100000000000000^207 ≤ 12278947652749^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014962659 10000000000 12278947652749 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410917371/10000000000 : ℝ)^271 ≤ (44751122621791/100000000000000 : ℝ)^207 := by
    have hnat : (5410917371 : ℕ)^271*100000000000000^207 ≤ 44751122621791^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410917371 10000000000 44751122621791 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245626293/10000000000 : ℝ)^271 ≤ (42969929718583/100000000000000 : ℝ)^207 := by
    have hnat : (5245626293 : ℕ)^271*100000000000000^207 ≤ 42969929718583^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245626293 10000000000 42969929718583 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2014962659/10000000000 : ℝ), (5410917371/10000000000 : ℝ), (5245626293/10000000000 : ℝ)] ![(12278947652749/100000000000000 : ℝ), (44751122621791/100000000000000 : ℝ), (42969929718583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2014962659/10000000000 : ℝ)|^271 ≤ (12278947652749/100000000000000 : ℝ)^207
        have hw : |(-2014962659/10000000000 : ℝ)|=(2014962659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410917371/10000000000 : ℝ)|^271 ≤ (44751122621791/100000000000000 : ℝ)^207
        have hw : |(5410917371/10000000000 : ℝ)|=(5410917371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245626293/10000000000 : ℝ)|^271 ≤ (42969929718583/100000000000000 : ℝ)^207
        have hw : |(5245626293/10000000000 : ℝ)|=(5245626293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s7_1 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5348375777/10000000000 : ℝ)*x 0 + (-83966083/400000000 : ℝ)*x 1 + (5245626553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348375777/10000000000 : ℝ)^271 ≤ (11018790206919/25000000000000 : ℝ)^207 := by
    have hnat : (5348375777 : ℕ)^271*25000000000000^207 ≤ 11018790206919^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348375777 10000000000 11018790206919 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (83966083/400000000 : ℝ)^271 ≤ (12954906650459/100000000000000 : ℝ)^207 := by
    have hnat : (83966083 : ℕ)^271*100000000000000^207 ≤ 12954906650459^207*400000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83966083 400000000 12954906650459 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245626553/10000000000 : ℝ)^271 ≤ (10742483126721/25000000000000 : ℝ)^207 := by
    have hnat : (5245626553 : ℕ)^271*25000000000000^207 ≤ 10742483126721^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245626553 10000000000 10742483126721 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348375777/10000000000 : ℝ), (-83966083/400000000 : ℝ), (5245626553/10000000000 : ℝ)] ![(11018790206919/25000000000000 : ℝ), (12954906650459/100000000000000 : ℝ), (10742483126721/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348375777/10000000000 : ℝ)|^271 ≤ (11018790206919/25000000000000 : ℝ)^207
        have hw : |(5348375777/10000000000 : ℝ)|=(5348375777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-83966083/400000000 : ℝ)|^271 ≤ (12954906650459/100000000000000 : ℝ)^207
        have hw : |(-83966083/400000000 : ℝ)|=(83966083/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245626553/10000000000 : ℝ)|^271 ≤ (10742483126721/25000000000000 : ℝ)^207
        have hw : |(5245626553/10000000000 : ℝ)|=(5245626553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s7_2 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2674187607/5000000000 : ℝ)*x 0 + (2622813369/5000000000 : ℝ)*x 1 + (-2099152581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674187607/5000000000 : ℝ)^271 ≤ (11018788688403/25000000000000 : ℝ)^207 := by
    have hnat : (2674187607 : ℕ)^271*25000000000000^207 ≤ 11018788688403^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674187607 5000000000 11018788688403 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622813369/5000000000 : ℝ)^271 ≤ (42969934490867/100000000000000 : ℝ)^207 := by
    have hnat : (2622813369 : ℕ)^271*100000000000000^207 ≤ 42969934490867^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622813369 5000000000 42969934490867 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2099152581/10000000000 : ℝ)^271 ≤ (3238727684683/25000000000000 : ℝ)^207 := by
    have hnat : (2099152581 : ℕ)^271*25000000000000^207 ≤ 3238727684683^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099152581 10000000000 3238727684683 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674187607/5000000000 : ℝ), (2622813369/5000000000 : ℝ), (-2099152581/10000000000 : ℝ)] ![(11018788688403/25000000000000 : ℝ), (42969934490867/100000000000000 : ℝ), (3238727684683/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674187607/5000000000 : ℝ)|^271 ≤ (11018788688403/25000000000000 : ℝ)^207
        have hw : |(2674187607/5000000000 : ℝ)|=(2674187607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622813369/5000000000 : ℝ)|^271 ≤ (42969934490867/100000000000000 : ℝ)^207
        have hw : |(2622813369/5000000000 : ℝ)|=(2622813369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2099152581/10000000000 : ℝ)|^271 ≤ (3238727684683/25000000000000 : ℝ)^207
        have hw : |(-2099152581/10000000000 : ℝ)|=(2099152581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s7_3 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1079452303/2500000000 : ℝ)*x 0 + (4145761651/10000000000 : ℝ)*x 1 + (2248205027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079452303/2500000000 : ℝ)^271 ≤ (8325966676983/25000000000000 : ℝ)^207 := by
    have hnat : (1079452303 : ℕ)^271*25000000000000^207 ≤ 8325966676983^207*2500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079452303 2500000000 8325966676983 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4145761651/10000000000 : ℝ)^271 ≤ (31577352627981/100000000000000 : ℝ)^207 := by
    have hnat : (4145761651 : ℕ)^271*100000000000000^207 ≤ 31577352627981^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145761651 10000000000 31577352627981 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248205027/5000000000 : ℝ)^271 ≤ (35118780641501/100000000000000 : ℝ)^207 := by
    have hnat : (2248205027 : ℕ)^271*100000000000000^207 ≤ 35118780641501^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248205027 5000000000 35118780641501 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079452303/2500000000 : ℝ), (4145761651/10000000000 : ℝ), (2248205027/5000000000 : ℝ)] ![(8325966676983/25000000000000 : ℝ), (31577352627981/100000000000000 : ℝ), (35118780641501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079452303/2500000000 : ℝ)|^271 ≤ (8325966676983/25000000000000 : ℝ)^207
        have hw : |(1079452303/2500000000 : ℝ)|=(1079452303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4145761651/10000000000 : ℝ)|^271 ≤ (31577352627981/100000000000000 : ℝ)^207
        have hw : |(4145761651/10000000000 : ℝ)|=(4145761651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2248205027/5000000000 : ℝ)|^271 ≤ (35118780641501/100000000000000 : ℝ)^207
        have hw : |(2248205027/5000000000 : ℝ)|=(2248205027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s7_4 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2014974333/10000000000 : ℝ)*x 0 + (524621963/1000000000 : ℝ)*x 1 + (216412843/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2014974333/10000000000 : ℝ)^271 ≤ (12279040787803/100000000000000 : ℝ)^207 := by
    have hnat : (2014974333 : ℕ)^271*100000000000000^207 ≤ 12279040787803^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014974333 10000000000 12279040787803 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524621963/1000000000 : ℝ)^271 ≤ (42976292914081/100000000000000 : ℝ)^207 := by
    have hnat : (524621963 : ℕ)^271*100000000000000^207 ≤ 42976292914081^207*1000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524621963 1000000000 42976292914081 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216412843/400000000 : ℝ)^271 ≤ (4474466628057/10000000000000 : ℝ)^207 := by
    have hnat : (216412843 : ℕ)^271*10000000000000^207 ≤ 4474466628057^207*400000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216412843 400000000 4474466628057 10000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2014974333/10000000000 : ℝ), (524621963/1000000000 : ℝ), (216412843/400000000 : ℝ)] ![(12279040787803/100000000000000 : ℝ), (42976292914081/100000000000000 : ℝ), (4474466628057/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2014974333/10000000000 : ℝ)|^271 ≤ (12279040787803/100000000000000 : ℝ)^207
        have hw : |(-2014974333/10000000000 : ℝ)|=(2014974333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524621963/1000000000 : ℝ)|^271 ≤ (42976292914081/100000000000000 : ℝ)^207
        have hw : |(524621963/1000000000 : ℝ)|=(524621963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216412843/400000000 : ℝ)|^271 ≤ (4474466628057/10000000000000 : ℝ)^207
        have hw : |(216412843/400000000 : ℝ)|=(216412843/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s7_5 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2652819111/5000000000 : ℝ)*x 0 + (-30225907/156250000 : ℝ)*x 1 + (2705160519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652819111/5000000000 : ℝ)^271 ≤ (8722929371497/20000000000000 : ℝ)^207 := by
    have hnat : (2652819111 : ℕ)^271*20000000000000^207 ≤ 8722929371497^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652819111 5000000000 8722929371497 20000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30225907/156250000 : ℝ)^271 ≤ (1455085905869/12500000000000 : ℝ)^207 := by
    have hnat : (30225907 : ℕ)^271*12500000000000^207 ≤ 1455085905869^207*156250000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30225907 156250000 1455085905869 12500000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705160519/5000000000 : ℝ)^271 ≤ (44744665879963/100000000000000 : ℝ)^207 := by
    have hnat : (2705160519 : ℕ)^271*100000000000000^207 ≤ 44744665879963^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705160519 5000000000 44744665879963 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652819111/5000000000 : ℝ), (-30225907/156250000 : ℝ), (2705160519/5000000000 : ℝ)] ![(8722929371497/20000000000000 : ℝ), (1455085905869/12500000000000 : ℝ), (44744665879963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652819111/5000000000 : ℝ)|^271 ≤ (8722929371497/20000000000000 : ℝ)^207
        have hw : |(2652819111/5000000000 : ℝ)|=(2652819111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-30225907/156250000 : ℝ)|^271 ≤ (1455085905869/12500000000000 : ℝ)^207
        have hw : |(-30225907/156250000 : ℝ)|=(30225907/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705160519/5000000000 : ℝ)|^271 ≤ (44744665879963/100000000000000 : ℝ)^207
        have hw : |(2705160519/5000000000 : ℝ)|=(2705160519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s7_6 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5305638219/10000000000 : ℝ)*x 0 + (676290133/1250000000 : ℝ)*x 1 + (-1934458017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305638219/10000000000 : ℝ)^271 ≤ (43614646825199/100000000000000 : ℝ)^207 := by
    have hnat : (5305638219 : ℕ)^271*100000000000000^207 ≤ 43614646825199^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305638219 10000000000 43614646825199 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676290133/1250000000 : ℝ)^271 ≤ (44744666161471/100000000000000 : ℝ)^207 := by
    have hnat : (676290133 : ℕ)^271*100000000000000^207 ≤ 44744666161471^207*1250000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676290133 1250000000 44744666161471 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1934458017/10000000000 : ℝ)^271 ≤ (2910171750683/25000000000000 : ℝ)^207 := by
    have hnat : (1934458017 : ℕ)^271*25000000000000^207 ≤ 2910171750683^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1934458017 10000000000 2910171750683 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305638219/10000000000 : ℝ), (676290133/1250000000 : ℝ), (-1934458017/10000000000 : ℝ)] ![(43614646825199/100000000000000 : ℝ), (44744666161471/100000000000000 : ℝ), (2910171750683/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305638219/10000000000 : ℝ)|^271 ≤ (43614646825199/100000000000000 : ℝ)^207
        have hw : |(5305638219/10000000000 : ℝ)|=(5305638219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676290133/1250000000 : ℝ)|^271 ≤ (44744666161471/100000000000000 : ℝ)^207
        have hw : |(676290133/1250000000 : ℝ)|=(676290133/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1934458017/10000000000 : ℝ)|^271 ≤ (2910171750683/25000000000000 : ℝ)^207
        have hw : |(-1934458017/10000000000 : ℝ)|=(1934458017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s7_7 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (431783419/1000000000 : ℝ)*x 0 + (4495151333/10000000000 : ℝ)*x 1 + (4147026961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431783419/1000000000 : ℝ)^271 ≤ (1332164757319/4000000000000 : ℝ)^207 := by
    have hnat : (431783419 : ℕ)^271*4000000000000^207 ≤ 1332164757319^207*1000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431783419 1000000000 1332164757319 4000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4495151333/10000000000 : ℝ)^271 ≤ (35105910505227/100000000000000 : ℝ)^207 := by
    have hnat : (4495151333 : ℕ)^271*100000000000000^207 ≤ 35105910505227^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495151333 10000000000 35105910505227 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4147026961/10000000000 : ℝ)^271 ≤ (31589970547749/100000000000000 : ℝ)^207 := by
    have hnat : (4147026961 : ℕ)^271*100000000000000^207 ≤ 31589970547749^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4147026961 10000000000 31589970547749 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431783419/1000000000 : ℝ), (4495151333/10000000000 : ℝ), (4147026961/10000000000 : ℝ)] ![(1332164757319/4000000000000 : ℝ), (35105910505227/100000000000000 : ℝ), (31589970547749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431783419/1000000000 : ℝ)|^271 ≤ (1332164757319/4000000000000 : ℝ)^207
        have hw : |(431783419/1000000000 : ℝ)|=(431783419/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4495151333/10000000000 : ℝ)|^271 ≤ (35105910505227/100000000000000 : ℝ)^207
        have hw : |(4495151333/10000000000 : ℝ)|=(4495151333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4147026961/10000000000 : ℝ)|^271 ≤ (31589970547749/100000000000000 : ℝ)^207
        have hw : |(4147026961/10000000000 : ℝ)|=(4147026961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1376_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (609648/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11227/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14727/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1841/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5613/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1841/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5613/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1841/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5613/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1841/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5613/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1841/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5613/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1841/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5613/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5613/50000 : ℝ) ^ (4335/1024 : ℝ) ≤ (9532880729786413/100000000000000000000 : ℝ) := by
    have hpowers : (5613/50000 : ℝ)^4335 ≤ (9532880729786413/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5613 : ℕ)^4335*100000000000000000000^1024 ≤ 9532880729786413^1024*50000^4335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5613 50000 9532880729786413 100000000000000000000 4335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5613/50000 : ℝ)) (X := (9532880729786413/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1841/12500 : ℝ) ^ (4335/1024 : ℝ) ≤ (15044964360636577/50000000000000000000 : ℝ) := by
    have hpowers : (1841/12500 : ℝ)^4335 ≤ (15044964360636577/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1841 : ℕ)^4335*50000000000000000000^1024 ≤ 15044964360636577^1024*12500^4335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1841 12500 15044964360636577 50000000000000000000 4335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1841/12500 : ℝ)) (X := (15044964360636577/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009532880729786413/50000000000000000000 : ℝ) ≤ (10000450332604131/10000000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (50009532880729786413/50000000000000000000 : ℝ)^1024 ≤ (10000450332604131/10000000000000000 : ℝ)^4335 := by
      have hnat : (50009532880729786413 : ℕ)^1024*10000000000000000^4335 ≤ 10000450332604131^4335*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009532880729786413 50000000000000000000 10000450332604131 10000000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000450332604131/10000000000000000 : ℝ)) (X := (50009532880729786413/50000000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039622809451059567/100000000000000000000 : ℝ) ≤ (2000187163178049/2000000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (100039622809451059567/100000000000000000000 : ℝ)^1024 ≤ (2000187163178049/2000000000000000 : ℝ)^4335 := by
      have hnat : (100039622809451059567 : ℕ)^1024*2000000000000000^4335 ≤ 2000187163178049^4335*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039622809451059567 100000000000000000000 2000187163178049 2000000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000187163178049/2000000000000000 : ℝ)) (X := (100039622809451059567/100000000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015044964360636577/25000000000000000000 : ℝ) ≤ (10001421299176359/10000000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (25015044964360636577/25000000000000000000 : ℝ)^1024 ≤ (10001421299176359/10000000000000000 : ℝ)^4335 := by
      have hnat : (25015044964360636577 : ℕ)^1024*10000000000000000^4335 ≤ 10001421299176359^4335*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015044964360636577 25000000000000000000 10001421299176359 10000000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001421299176359/10000000000000000 : ℝ)) (X := (25015044964360636577/25000000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9532880729786413/100000000000000000000 : ℝ) ≤ ((17505338497019917617/17510000000000000000 : ℝ)+2*(242741643057/175100000000000 : ℝ)*(5613/50000 : ℝ))^(4335/1024 : ℝ) := by
    rw [show (17505338497019917617/17510000000000000000 : ℝ)+2*(242741643057/175100000000000 : ℝ)*(5613/50000 : ℝ)=(10000450332604131/10000000000000000 : ℝ) by norm_num, show 1+2*(9532880729786413/100000000000000000000 : ℝ)=(50009532880729786413/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15044964360636577/50000000000000000000 : ℝ)+(9532880729786413/100000000000000000000 : ℝ) ≤ ((17505338497019917617/17510000000000000000 : ℝ)+(242741643057/175100000000000 : ℝ)*((1841/12500 : ℝ)+(5613/50000 : ℝ)))^(4335/1024 : ℝ) := by
    rw [show (17505338497019917617/17510000000000000000 : ℝ)+(242741643057/175100000000000 : ℝ)*((1841/12500 : ℝ)+(5613/50000 : ℝ))=(2000187163178049/2000000000000000 : ℝ) by norm_num, show 1+(15044964360636577/50000000000000000000 : ℝ)+(9532880729786413/100000000000000000000 : ℝ)=(100039622809451059567/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15044964360636577/50000000000000000000 : ℝ) ≤ ((17505338497019917617/17510000000000000000 : ℝ)+2*(242741643057/175100000000000 : ℝ)*(1841/12500 : ℝ))^(4335/1024 : ℝ) := by
    rw [show (17505338497019917617/17510000000000000000 : ℝ)+2*(242741643057/175100000000000 : ℝ)*(1841/12500 : ℝ)=(10001421299176359/10000000000000000 : ℝ) by norm_num, show 1+2*(15044964360636577/50000000000000000000 : ℝ)=(25015044964360636577/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17505338497019917617/17510000000000000000 : ℝ)*(X 1 0+X 2 0)+(242741643057/175100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (5613/50000 : ℝ)) (hi := (1841/12500 : ℝ)) (c := (17505338497019917617/17510000000000000000 : ℝ)) (alpha := (242741643057/175100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17505338497019917617/17510000000000000000 : ℝ)*(X 0 1+X 2 1)+(242741643057/175100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (5613/50000 : ℝ)) (hi := (1841/12500 : ℝ)) (c := (17505338497019917617/17510000000000000000 : ℝ)) (alpha := (242741643057/175100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17505338497019917617/17510000000000000000 : ℝ)*(X 0 2+X 1 2)+(242741643057/175100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (5613/50000 : ℝ)) (hi := (1841/12500 : ℝ)) (c := (17505338497019917617/17510000000000000000 : ℝ)) (alpha := (242741643057/175100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2014962659/10000000000 : ℝ)*X 0 0+(5410917371/10000000000 : ℝ)*X 0 1+(5245626293/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348375777/10000000000 : ℝ)*X 1 0+(-83966083/400000000 : ℝ)*X 1 1+(5245626553/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674187607/5000000000 : ℝ)*X 2 0+(2622813369/5000000000 : ℝ)*X 2 1+(-2099152581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1079452303/2500000000 : ℝ)*X 0 0+(4145761651/10000000000 : ℝ)*X 0 1+(2248205027/5000000000 : ℝ)*X 0 2+(1079452303/2500000000 : ℝ)*X 1 0+(4145761651/10000000000 : ℝ)*X 1 1+(2248205027/5000000000 : ℝ)*X 1 2+(1079452303/2500000000 : ℝ)*X 2 0+(4145761651/10000000000 : ℝ)*X 2 1+(2248205027/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2014974333/10000000000 : ℝ)*X 0 0+(524621963/1000000000 : ℝ)*X 0 1+(216412843/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652819111/5000000000 : ℝ)*X 1 0+(-30225907/156250000 : ℝ)*X 1 1+(2705160519/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305638219/10000000000 : ℝ)*X 2 0+(676290133/1250000000 : ℝ)*X 2 1+(-1934458017/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((431783419/1000000000 : ℝ)*X 0 0+(4495151333/10000000000 : ℝ)*X 0 1+(4147026961/10000000000 : ℝ)*X 0 2+(431783419/1000000000 : ℝ)*X 1 0+(4495151333/10000000000 : ℝ)*X 1 1+(4147026961/10000000000 : ℝ)*X 1 2+(431783419/1000000000 : ℝ)*X 2 0+(4495151333/10000000000 : ℝ)*X 2 1+(4147026961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1587724844612734459938029187/175100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2417744609/100000000000000 : ℝ)*(base19) + (448448137/25000000000000 : ℝ)*(base23) + (472253983/100000000000000 : ℝ)*(upper3) + (35859251/100000000000000 : ℝ)*(lower4) + (2225494927173421/50000000000000 : ℝ)*(major0) + (2225494927173421/50000000000000 : ℝ)*(major1) + (4450989854346843/100000000000000 : ℝ)*(major2) + (6050007770925881/100000000000000 : ℝ)*(sp0) + (6050056024708563/100000000000000 : ℝ)*(sp1) + (6050049873717551/100000000000000 : ℝ)*(sp2) + (178243003183801/6250000000000 : ℝ)*(sp3) + (50671527291/100000000000000 : ℝ)*(sp4) + (211716971/3125000000000 : ℝ)*(sp6) + (16456524313/50000000000000 : ℝ)*(sp7) + (1425960481994721/50000000000000 : ℝ)*(f.failure) + (1512514610613293/25000000000000 : ℝ)*(f.sum) + (646910016891/3502000000000000000000000000 : ℝ)*base66 + (3240233629492107757/875500000000000000000000000000000 : ℝ)*base67 + (11868568125804566869/1751000000000000000000000000000000 : ℝ)*base70 + (9875221723271892243/875500000000000000000000000000000 : ℝ)*base72 + (3946919032611/3502000000000000000000000000 : ℝ)*base73 + (2932385818935566869/1751000000000000000000000000000000 : ℝ)*base76 + (3166995618165242243/875500000000000000000000000000000 : ℝ)*base78 + (664942082568242243/875500000000000000000000000000000 : ℝ)*base80 + (45271398033269/8755000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (90083/19531250000000000000 : ℝ)*base89 + (90083/19531250000000000000 : ℝ)*base91 + (210459/39062500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (485197927755555425076066057/109437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (697761883/100000000000000 : ℝ)*(base19) + (843710309/100000000000000 : ℝ)*(base23) + (222606281/100000000000000 : ℝ)*(lower1) + (75097037/100000000000000 : ℝ)*(upper3) + (32829571/50000000000000 : ℝ)*(lower4) + (95891639/100000000000000 : ℝ)*(upper5) + (1120788376248607/25000000000000 : ℝ)*(major0) + (1120788376248607/25000000000000 : ℝ)*(major1) + (1120788376248607/25000000000000 : ℝ)*(major2) + (3183180253/100000000000000 : ℝ)*(sp2) + (609377740604439/10000000000000 : ℝ)*(sp4) + (6093776708282507/100000000000000 : ℝ)*(sp5) + (1523443344788457/25000000000000 : ℝ)*(sp6) + (718132364039761/25000000000000 : ℝ)*(sp7) + (718132364039761/25000000000000 : ℝ)*(f.failure) + (609377740604439/10000000000000 : ℝ)*(f.sum) + (6565397881777/4377500000000000000000000000 : ℝ)*base66 + (3109386339027090481/437750000000000000000000000000000 : ℝ)*base68 + (7658538261947590481/437750000000000000000000000000000 : ℝ)*base70 + (38322637523707409519/437750000000000000000000000000000 : ℝ)*base71 + (284486588669/136796875000000000000000000 : ℝ)*base73 + (47435551322201590481/437750000000000000000000000000000 : ℝ)*base76 + (6084131558522590481/437750000000000000000000000000000 : ℝ)*base78 + (3838529882153590481/437750000000000000000000000000000 : ℝ)*base80 + (35059431939071/8755000000000000000000000000 : ℝ)*base81 + (104753/9765625000000000000 : ℝ)*base89 + (104753/9765625000000000000 : ℝ)*base91 + (104753/9765625000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1376_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (609648/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5613/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11227/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14727/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1376_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1376_s8_0 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1007481609/5000000000 : ℝ)*x 0 + (5410909451/10000000000 : ℝ)*x 1 + (5245633873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1007481609/5000000000 : ℝ)^271 ≤ (6139476056221/50000000000000 : ℝ)^207 := by
    have hnat : (1007481609 : ℕ)^271*50000000000000^207 ≤ 6139476056221^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007481609 5000000000 6139476056221 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410909451/10000000000 : ℝ)^271 ≤ (44751036867263/100000000000000 : ℝ)^207 := by
    have hnat : (5410909451 : ℕ)^271*100000000000000^207 ≤ 44751036867263^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410909451 10000000000 44751036867263 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245633873/10000000000 : ℝ)^271 ≤ (42970011008287/100000000000000 : ℝ)^207 := by
    have hnat : (5245633873 : ℕ)^271*100000000000000^207 ≤ 42970011008287^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245633873 10000000000 42970011008287 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1007481609/5000000000 : ℝ), (5410909451/10000000000 : ℝ), (5245633873/10000000000 : ℝ)] ![(6139476056221/50000000000000 : ℝ), (44751036867263/100000000000000 : ℝ), (42970011008287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1007481609/5000000000 : ℝ)|^271 ≤ (6139476056221/50000000000000 : ℝ)^207
        have hw : |(-1007481609/5000000000 : ℝ)|=(1007481609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410909451/10000000000 : ℝ)|^271 ≤ (44751036867263/100000000000000 : ℝ)^207
        have hw : |(5410909451/10000000000 : ℝ)|=(5410909451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245633873/10000000000 : ℝ)|^271 ≤ (42970011008287/100000000000000 : ℝ)^207
        have hw : |(5245633873/10000000000 : ℝ)|=(5245633873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s8_1 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (66854669/125000000 : ℝ)*x 0 + (-2099145451/10000000000 : ℝ)*x 1 + (2622816907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66854669/125000000 : ℝ)^271 ≤ (44075136477479/100000000000000 : ℝ)^207 := by
    have hnat : (66854669 : ℕ)^271*100000000000000^207 ≤ 44075136477479^207*125000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66854669 125000000 44075136477479 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2099145451/10000000000 : ℝ)^271 ≤ (161935664141/1250000000000 : ℝ)^207 := by
    have hnat : (2099145451 : ℕ)^271*1250000000000^207 ≤ 161935664141^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099145451 10000000000 161935664141 1250000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622816907/5000000000 : ℝ)^271 ≤ (42970010375557/100000000000000 : ℝ)^207 := by
    have hnat : (2622816907 : ℕ)^271*100000000000000^207 ≤ 42970010375557^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622816907 5000000000 42970010375557 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66854669/125000000 : ℝ), (-2099145451/10000000000 : ℝ), (2622816907/5000000000 : ℝ)] ![(44075136477479/100000000000000 : ℝ), (161935664141/1250000000000 : ℝ), (42970010375557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66854669/125000000 : ℝ)|^271 ≤ (44075136477479/100000000000000 : ℝ)^207
        have hw : |(66854669/125000000 : ℝ)|=(66854669/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2099145451/10000000000 : ℝ)|^271 ≤ (161935664141/1250000000000 : ℝ)^207
        have hw : |(-2099145451/10000000000 : ℝ)|=(2099145451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622816907/5000000000 : ℝ)|^271 ≤ (42970010375557/100000000000000 : ℝ)^207
        have hw : |(2622816907/5000000000 : ℝ)|=(2622816907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s8_2 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5348373637/10000000000 : ℝ)*x 0 + (5245633681/10000000000 : ℝ)*x 1 + (-8199787/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348373637/10000000000 : ℝ)^271 ≤ (22037568869881/50000000000000 : ℝ)^207 := by
    have hnat : (5348373637 : ℕ)^271*50000000000000^207 ≤ 22037568869881^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348373637 10000000000 22037568869881 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245633681/10000000000 : ℝ)^271 ≤ (21485004474617/50000000000000 : ℝ)^207 := by
    have hnat : (5245633681 : ℕ)^271*50000000000000^207 ≤ 21485004474617^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245633681 10000000000 21485004474617 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8199787/39062500 : ℝ)^271 ≤ (1619356662619/12500000000000 : ℝ)^207 := by
    have hnat : (8199787 : ℕ)^271*12500000000000^207 ≤ 1619356662619^207*39062500^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8199787 39062500 1619356662619 12500000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348373637/10000000000 : ℝ), (5245633681/10000000000 : ℝ), (-8199787/39062500 : ℝ)] ![(22037568869881/50000000000000 : ℝ), (21485004474617/50000000000000 : ℝ), (1619356662619/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348373637/10000000000 : ℝ)|^271 ≤ (22037568869881/50000000000000 : ℝ)^207
        have hw : |(5348373637/10000000000 : ℝ)|=(5348373637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245633681/10000000000 : ℝ)|^271 ≤ (21485004474617/50000000000000 : ℝ)^207
        have hw : |(5245633681/10000000000 : ℝ)|=(5245633681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8199787/39062500 : ℝ)|^271 ≤ (1619356662619/12500000000000 : ℝ)^207
        have hw : |(-8199787/39062500 : ℝ)|=(8199787/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s8_3 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2158904723/5000000000 : ℝ)*x 0 + (1036444541/2500000000 : ℝ)*x 1 + (112409843/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158904723/5000000000 : ℝ)^271 ≤ (6660773814167/20000000000000 : ℝ)^207 := by
    have hnat : (2158904723 : ℕ)^271*20000000000000^207 ≤ 6660773814167^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158904723 5000000000 6660773814167 20000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036444541/2500000000 : ℝ)^271 ≤ (31577517291193/100000000000000 : ℝ)^207 := by
    have hnat : (1036444541 : ℕ)^271*100000000000000^207 ≤ 31577517291193^207*2500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036444541 2500000000 31577517291193 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112409843/250000000 : ℝ)^271 ≤ (2194913351433/6250000000000 : ℝ)^207 := by
    have hnat : (112409843 : ℕ)^271*6250000000000^207 ≤ 2194913351433^207*250000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112409843 250000000 2194913351433 6250000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158904723/5000000000 : ℝ), (1036444541/2500000000 : ℝ), (112409843/250000000 : ℝ)] ![(6660773814167/20000000000000 : ℝ), (31577517291193/100000000000000 : ℝ), (2194913351433/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158904723/5000000000 : ℝ)|^271 ≤ (6660773814167/20000000000000 : ℝ)^207
        have hw : |(2158904723/5000000000 : ℝ)|=(2158904723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036444541/2500000000 : ℝ)|^271 ≤ (31577517291193/100000000000000 : ℝ)^207
        have hw : |(1036444541/2500000000 : ℝ)|=(1036444541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(112409843/250000000 : ℝ)|^271 ≤ (2194913351433/6250000000000 : ℝ)^207
        have hw : |(112409843/250000000 : ℝ)|=(112409843/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s8_4 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2014974879/10000000000 : ℝ)*x 0 + (5246227317/10000000000 : ℝ)*x 1 + (5410313059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2014974879/10000000000 : ℝ)^271 ≤ (1227904514379/10000000000000 : ℝ)^207 := by
    have hnat : (2014974879 : ℕ)^271*10000000000000^207 ≤ 1227904514379^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014974879 10000000000 1227904514379 10000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246227317/10000000000 : ℝ)^271 ≤ (21488187677081/50000000000000 : ℝ)^207 := by
    have hnat : (5246227317 : ℕ)^271*50000000000000^207 ≤ 21488187677081^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246227317 10000000000 21488187677081 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410313059/10000000000 : ℝ)^271 ≤ (44744579489551/100000000000000 : ℝ)^207 := by
    have hnat : (5410313059 : ℕ)^271*100000000000000^207 ≤ 44744579489551^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410313059 10000000000 44744579489551 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2014974879/10000000000 : ℝ), (5246227317/10000000000 : ℝ), (5410313059/10000000000 : ℝ)] ![(1227904514379/10000000000000 : ℝ), (21488187677081/50000000000000 : ℝ), (44744579489551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2014974879/10000000000 : ℝ)|^271 ≤ (1227904514379/10000000000000 : ℝ)^207
        have hw : |(-2014974879/10000000000 : ℝ)|=(2014974879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246227317/10000000000 : ℝ)|^271 ≤ (21488187677081/50000000000000 : ℝ)^207
        have hw : |(5246227317/10000000000 : ℝ)|=(5246227317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410313059/10000000000 : ℝ)|^271 ≤ (44744579489551/100000000000000 : ℝ)^207
        have hw : |(5410313059/10000000000 : ℝ)|=(5410313059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s8_5 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4317834843/10000000000 : ℝ)*x 0 + (2247567541/5000000000 : ℝ)*x 1 + (51838037/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317834843/10000000000 : ℝ)^271 ≤ (16652062763451/50000000000000 : ℝ)^207 := by
    have hnat : (4317834843 : ℕ)^271*50000000000000^207 ≤ 16652062763451^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317834843 10000000000 16652062763451 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247567541/5000000000 : ℝ)^271 ≤ (1097054510929/3125000000000 : ℝ)^207 := by
    have hnat : (2247567541 : ℕ)^271*3125000000000^207 ≤ 1097054510929^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247567541 5000000000 1097054510929 3125000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51838037/125000000 : ℝ)^271 ≤ (1579506505027/5000000000000 : ℝ)^207 := by
    have hnat : (51838037 : ℕ)^271*5000000000000^207 ≤ 1579506505027^207*125000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51838037 125000000 1579506505027 5000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317834843/10000000000 : ℝ), (2247567541/5000000000 : ℝ), (51838037/125000000 : ℝ)] ![(16652062763451/50000000000000 : ℝ), (1097054510929/3125000000000 : ℝ), (1579506505027/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317834843/10000000000 : ℝ)|^271 ≤ (16652062763451/50000000000000 : ℝ)^207
        have hw : |(4317834843/10000000000 : ℝ)|=(4317834843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2247567541/5000000000 : ℝ)|^271 ≤ (1097054510929/3125000000000 : ℝ)^207
        have hw : |(2247567541/5000000000 : ℝ)|=(2247567541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(51838037/125000000 : ℝ)|^271 ≤ (1579506505027/5000000000000 : ℝ)^207
        have hw : |(51838037/125000000 : ℝ)|=(51838037/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1376_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (609648/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14727/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11227/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2807/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14727/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14727/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11227/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14727/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11227/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14727/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11227/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14727/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11227/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14727/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11227/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14727/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11227/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11227/100000 : ℝ) ^ (4335/1024 : ℝ) ≤ (9536476159562223/100000000000000000000 : ℝ) := by
    have hpowers : (11227/100000 : ℝ)^4335 ≤ (9536476159562223/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11227 : ℕ)^4335*100000000000000000000^1024 ≤ 9536476159562223^1024*100000^4335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11227 100000 9536476159562223 100000000000000000000 4335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11227/100000 : ℝ)) (X := (9536476159562223/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14727/100000 : ℝ) ^ (4335/1024 : ℝ) ≤ (30081280658054249/100000000000000000000 : ℝ) := by
    have hpowers : (14727/100000 : ℝ)^4335 ≤ (30081280658054249/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14727 : ℕ)^4335*100000000000000000000^1024 ≤ 30081280658054249^1024*100000^4335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14727 100000 30081280658054249 100000000000000000000 4335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14727/100000 : ℝ)) (X := (30081280658054249/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009536476159562223/50000000000000000000 : ℝ) ≤ (10000450502439607/10000000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (50009536476159562223/50000000000000000000 : ℝ)^1024 ≤ (10000450502439607/10000000000000000 : ℝ)^4335 := by
      have hnat : (50009536476159562223 : ℕ)^1024*10000000000000000^4335 ≤ 10000450502439607^4335*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009536476159562223 50000000000000000000 10000450502439607 10000000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000450502439607/10000000000000000 : ℝ)) (X := (50009536476159562223/50000000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12504952219602202059/12500000000000000000 : ℝ) ≤ (10000935696574639/10000000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (12504952219602202059/12500000000000000000 : ℝ)^1024 ≤ (10000935696574639/10000000000000000 : ℝ)^4335 := by
      have hnat : (12504952219602202059 : ℕ)^1024*10000000000000000^4335 ≤ 10000935696574639^4335*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504952219602202059 12500000000000000000 10000935696574639 10000000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000935696574639/10000000000000000 : ℝ)) (X := (12504952219602202059/12500000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030081280658054249/50000000000000000000 : ℝ) ≤ (10001420890709671/10000000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (50030081280658054249/50000000000000000000 : ℝ)^1024 ≤ (10001420890709671/10000000000000000 : ℝ)^4335 := by
      have hnat : (50030081280658054249 : ℕ)^1024*10000000000000000^4335 ≤ 10001420890709671^4335*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030081280658054249 50000000000000000000 10001420890709671 10000000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001420890709671/10000000000000000 : ℝ)) (X := (50030081280658054249/50000000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9536476159562223/100000000000000000000 : ℝ) ≤ ((8747670552357653993/8750000000000000000 : ℝ)+2*(60649266879/43750000000000 : ℝ)*(11227/100000 : ℝ))^(4335/1024 : ℝ) := by
    rw [show (8747670552357653993/8750000000000000000 : ℝ)+2*(60649266879/43750000000000 : ℝ)*(11227/100000 : ℝ)=(10000450502439607/10000000000000000 : ℝ) by norm_num, show 1+2*(9536476159562223/100000000000000000000 : ℝ)=(50009536476159562223/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30081280658054249/100000000000000000000 : ℝ)+(9536476159562223/100000000000000000000 : ℝ) ≤ ((8747670552357653993/8750000000000000000 : ℝ)+(60649266879/43750000000000 : ℝ)*((14727/100000 : ℝ)+(11227/100000 : ℝ)))^(4335/1024 : ℝ) := by
    rw [show (8747670552357653993/8750000000000000000 : ℝ)+(60649266879/43750000000000 : ℝ)*((14727/100000 : ℝ)+(11227/100000 : ℝ))=(10000935696574639/10000000000000000 : ℝ) by norm_num, show 1+(30081280658054249/100000000000000000000 : ℝ)+(9536476159562223/100000000000000000000 : ℝ)=(12504952219602202059/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30081280658054249/100000000000000000000 : ℝ) ≤ ((8747670552357653993/8750000000000000000 : ℝ)+2*(60649266879/43750000000000 : ℝ)*(14727/100000 : ℝ))^(4335/1024 : ℝ) := by
    rw [show (8747670552357653993/8750000000000000000 : ℝ)+2*(60649266879/43750000000000 : ℝ)*(14727/100000 : ℝ)=(10001420890709671/10000000000000000 : ℝ) by norm_num, show 1+2*(30081280658054249/100000000000000000000 : ℝ)=(50030081280658054249/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8747670552357653993/8750000000000000000 : ℝ)*(X 1 0+X 2 0)+(60649266879/43750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (11227/100000 : ℝ)) (hi := (14727/100000 : ℝ)) (c := (8747670552357653993/8750000000000000000 : ℝ)) (alpha := (60649266879/43750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8747670552357653993/8750000000000000000 : ℝ)*(X 0 1+X 2 1)+(60649266879/43750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (11227/100000 : ℝ)) (hi := (14727/100000 : ℝ)) (c := (8747670552357653993/8750000000000000000 : ℝ)) (alpha := (60649266879/43750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8747670552357653993/8750000000000000000 : ℝ)*(X 0 2+X 1 2)+(60649266879/43750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (11227/100000 : ℝ)) (hi := (14727/100000 : ℝ)) (c := (8747670552357653993/8750000000000000000 : ℝ)) (alpha := (60649266879/43750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1007481609/5000000000 : ℝ)*X 0 0+(5410909451/10000000000 : ℝ)*X 0 1+(5245633873/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((66854669/125000000 : ℝ)*X 1 0+(-2099145451/10000000000 : ℝ)*X 1 1+(2622816907/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348373637/10000000000 : ℝ)*X 2 0+(5245633681/10000000000 : ℝ)*X 2 1+(-8199787/39062500 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2158904723/5000000000 : ℝ)*X 0 0+(1036444541/2500000000 : ℝ)*X 0 1+(112409843/250000000 : ℝ)*X 0 2+(2158904723/5000000000 : ℝ)*X 1 0+(1036444541/2500000000 : ℝ)*X 1 1+(112409843/250000000 : ℝ)*X 1 2+(2158904723/5000000000 : ℝ)*X 2 0+(1036444541/2500000000 : ℝ)*X 2 1+(112409843/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2014974879/10000000000 : ℝ)*X 0 0+(5246227317/10000000000 : ℝ)*X 0 1+(5410313059/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4317834843/10000000000 : ℝ)*X 0 0+(2247567541/5000000000 : ℝ)*X 0 1+(51838037/125000000 : ℝ)*X 0 2+(4317834843/10000000000 : ℝ)*X 1 0+(2247567541/5000000000 : ℝ)*X 1 1+(51838037/125000000 : ℝ)*X 1 2+(4317834843/10000000000 : ℝ)*X 2 0+(2247567541/5000000000 : ℝ)*X 2 1+(51838037/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2145709874444755855474479/1093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31003811/10000000000000 : ℝ)*(base19) + (409043381/100000000000000 : ℝ)*(base23) + (9229171/50000000000000 : ℝ)*(lower2) + (154763/25000000000000 : ℝ)*(lower4) + (1050847/4000000000000 : ℝ)*(lower5) + (4451324671900401/100000000000000 : ℝ)*(major0) + (4451324671900401/100000000000000 : ℝ)*(major1) + (2225662335950201/50000000000000 : ℝ)*(major2) + (1512626750168923/25000000000000 : ℝ)*(sp0) + (6050513473852963/100000000000000 : ℝ)*(sp1) + (6050513374847693/100000000000000 : ℝ)*(sp2) + (1426065302978101/50000000000000 : ℝ)*(sp3) + (6783215381/100000000000000 : ℝ)*(sp4) + (4888560461/100000000000000 : ℝ)*(sp5) + (2852135494516663/100000000000000 : ℝ)*(f.failure) + (6050513783891073/100000000000000 : ℝ)*(f.sum) + (4304104178837/4375000000000000000000000000 : ℝ)*base65 + (1833745051737448807/875000000000000000000000000000000 : ℝ)*base68 + (2960050037872202593/437500000000000000000000000000000 : ℝ)*base69 + (1097408643237448807/875000000000000000000000000000000 : ℝ)*base72 + (4846041847769/2187500000000000000000000000 : ℝ)*base74 + (378793349809702593/437500000000000000000000000000000 : ℝ)*base75 + (214596709641178401/125000000000000000000000000000000 : ℝ)*base78 + (578748923016178401/125000000000000000000000000000000 : ℝ)*base80 + (472475078479/2187500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (423999/39062500000000000000 : ℝ)*base89 + (423999/39062500000000000000 : ℝ)*base91 + (16687/19531250000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1376_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (609648/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14727/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11227/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2807/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14727/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1376_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1376_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (609648/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7367/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2807/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14727/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1376_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1376_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1376_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (609648/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7367/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2807/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14727/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1376_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
