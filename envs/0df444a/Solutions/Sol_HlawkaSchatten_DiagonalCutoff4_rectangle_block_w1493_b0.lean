-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1493_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:49:45.28999+00:00
-- url     : https://prove2.me/submissions/5aaa95ab-d1da-4dfc-a06a-a9bff3f57e1d

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
theorem support_rectangle_w1493_s0_0 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-426543467/2500000000 : ℝ)*x 0 + (237104323/400000000 : ℝ)*x 1 + (969421159/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (426543467/2500000000 : ℝ)^4483 ≤ (10108157110247/100000000000000 : ℝ)^3459 := by
    have hnat : (426543467 : ℕ)^4483*100000000000000^3459 ≤ 10108157110247^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426543467 2500000000 10108157110247 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (237104323/400000000 : ℝ)^4483 ≤ (2030967009181/4000000000000 : ℝ)^3459 := by
    have hnat : (237104323 : ℕ)^4483*4000000000000^3459 ≤ 2030967009181^3459*400000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237104323 400000000 2030967009181 4000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (969421159/2000000000 : ℝ)^4483 ≤ (3911766764631/10000000000000 : ℝ)^3459 := by
    have hnat : (969421159 : ℕ)^4483*10000000000000^3459 ≤ 3911766764631^3459*2000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969421159 2000000000 3911766764631 10000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-426543467/2500000000 : ℝ), (237104323/400000000 : ℝ), (969421159/2000000000 : ℝ)] ![(10108157110247/100000000000000 : ℝ), (2030967009181/4000000000000 : ℝ), (3911766764631/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-426543467/2500000000 : ℝ)|^4483 ≤ (10108157110247/100000000000000 : ℝ)^3459
        have hw : |(-426543467/2500000000 : ℝ)|=(426543467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(237104323/400000000 : ℝ)|^4483 ≤ (2030967009181/4000000000000 : ℝ)^3459
        have hw : |(237104323/400000000 : ℝ)|=(237104323/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(969421159/2000000000 : ℝ)|^4483 ≤ (3911766764631/10000000000000 : ℝ)^3459
        have hw : |(969421159/2000000000 : ℝ)|=(969421159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s0_1 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42829109/78125000 : ℝ)*x 0 + (-289164417/1250000000 : ℝ)*x 1 + (2423553061/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42829109/78125000 : ℝ)^4483 ≤ (22942337082589/50000000000000 : ℝ)^3459 := by
    have hnat : (42829109 : ℕ)^4483*50000000000000^3459 ≤ 22942337082589^3459*78125000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42829109 78125000 22942337082589 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (289164417/1250000000 : ℝ)^4483 ≤ (7498827376579/50000000000000 : ℝ)^3459 := by
    have hnat : (289164417 : ℕ)^4483*50000000000000^3459 ≤ 7498827376579^3459*1250000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289164417 1250000000 7498827376579 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2423553061/5000000000 : ℝ)^4483 ≤ (39117671066549/100000000000000 : ℝ)^3459 := by
    have hnat : (2423553061 : ℕ)^4483*100000000000000^3459 ≤ 39117671066549^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2423553061 5000000000 39117671066549 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42829109/78125000 : ℝ), (-289164417/1250000000 : ℝ), (2423553061/5000000000 : ℝ)] ![(22942337082589/50000000000000 : ℝ), (7498827376579/50000000000000 : ℝ), (39117671066549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42829109/78125000 : ℝ)|^4483 ≤ (22942337082589/50000000000000 : ℝ)^3459
        have hw : |(42829109/78125000 : ℝ)|=(42829109/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-289164417/1250000000 : ℝ)|^4483 ≤ (7498827376579/50000000000000 : ℝ)^3459
        have hw : |(-289164417/1250000000 : ℝ)|=(289164417/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2423553061/5000000000 : ℝ)|^4483 ≤ (39117671066549/100000000000000 : ℝ)^3459
        have hw : |(2423553061/5000000000 : ℝ)|=(2423553061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s0_2 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1370531457/2500000000 : ℝ)*x 0 + (4847107279/10000000000 : ℝ)*x 1 + (-289164257/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1370531457/2500000000 : ℝ)^4483 ≤ (22942336410033/50000000000000 : ℝ)^3459 := by
    have hnat : (1370531457 : ℕ)^4483*50000000000000^3459 ≤ 22942336410033^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370531457 2500000000 22942336410033 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4847107279/10000000000 : ℝ)^4483 ≤ (39117683168127/100000000000000 : ℝ)^3459 := by
    have hnat : (4847107279 : ℕ)^4483*100000000000000^3459 ≤ 39117683168127^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4847107279 10000000000 39117683168127 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (289164257/1250000000 : ℝ)^4483 ≤ (3749410999501/25000000000000 : ℝ)^3459 := by
    have hnat : (289164257 : ℕ)^4483*25000000000000^3459 ≤ 3749410999501^3459*1250000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289164257 1250000000 3749410999501 25000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1370531457/2500000000 : ℝ), (4847107279/10000000000 : ℝ), (-289164257/1250000000 : ℝ)] ![(22942336410033/50000000000000 : ℝ), (39117683168127/100000000000000 : ℝ), (3749410999501/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1370531457/2500000000 : ℝ)|^4483 ≤ (22942336410033/50000000000000 : ℝ)^3459
        have hw : |(1370531457/2500000000 : ℝ)|=(1370531457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4847107279/10000000000 : ℝ)|^4483 ≤ (39117683168127/100000000000000 : ℝ)^3459
        have hw : |(4847107279/10000000000 : ℝ)|=(4847107279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-289164257/1250000000 : ℝ)|^4483 ≤ (3749410999501/25000000000000 : ℝ)^3459
        have hw : |(-289164257/1250000000 : ℝ)|=(289164257/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s0_3 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (129697071/312500000 : ℝ)*x 0 + (1545640201/5000000000 : ℝ)*x 1 + (2754319661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129697071/312500000 : ℝ)^4483 ≤ (31990192531089/100000000000000 : ℝ)^3459 := by
    have hnat : (129697071 : ℕ)^4483*100000000000000^3459 ≤ 31990192531089^3459*312500000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129697071 312500000 31990192531089 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1545640201/5000000000 : ℝ)^4483 ≤ (2729664888931/12500000000000 : ℝ)^3459 := by
    have hnat : (1545640201 : ℕ)^4483*12500000000000^3459 ≤ 2729664888931^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1545640201 5000000000 2729664888931 12500000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2754319661/5000000000 : ℝ)^4483 ≤ (46172488346127/100000000000000 : ℝ)^3459 := by
    have hnat : (2754319661 : ℕ)^4483*100000000000000^3459 ≤ 46172488346127^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754319661 5000000000 46172488346127 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129697071/312500000 : ℝ), (1545640201/5000000000 : ℝ), (2754319661/5000000000 : ℝ)] ![(31990192531089/100000000000000 : ℝ), (2729664888931/12500000000000 : ℝ), (46172488346127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129697071/312500000 : ℝ)|^4483 ≤ (31990192531089/100000000000000 : ℝ)^3459
        have hw : |(129697071/312500000 : ℝ)|=(129697071/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1545640201/5000000000 : ℝ)|^4483 ≤ (2729664888931/12500000000000 : ℝ)^3459
        have hw : |(1545640201/5000000000 : ℝ)|=(1545640201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2754319661/5000000000 : ℝ)|^4483 ≤ (46172488346127/100000000000000 : ℝ)^3459
        have hw : |(2754319661/5000000000 : ℝ)|=(2754319661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s0_4 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-854929203/5000000000 : ℝ)*x 0 + (2437382019/5000000000 : ℝ)*x 1 + (2949478861/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (854929203/5000000000 : ℝ)^4483 ≤ (5068228627129/50000000000000 : ℝ)^3459 := by
    have hnat : (854929203 : ℕ)^4483*50000000000000^3459 ≤ 5068228627129^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854929203 5000000000 5068228627129 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2437382019/5000000000 : ℝ)^4483 ≤ (4925900190589/12500000000000 : ℝ)^3459 := by
    have hnat : (2437382019 : ℕ)^4483*12500000000000^3459 ≤ 4925900190589^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2437382019 5000000000 4925900190589 12500000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2949478861/5000000000 : ℝ)^4483 ≤ (25228170606283/50000000000000 : ℝ)^3459 := by
    have hnat : (2949478861 : ℕ)^4483*50000000000000^3459 ≤ 25228170606283^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2949478861 5000000000 25228170606283 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-854929203/5000000000 : ℝ), (2437382019/5000000000 : ℝ), (2949478861/5000000000 : ℝ)] ![(5068228627129/50000000000000 : ℝ), (4925900190589/12500000000000 : ℝ), (25228170606283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-854929203/5000000000 : ℝ)|^4483 ≤ (5068228627129/50000000000000 : ℝ)^3459
        have hw : |(-854929203/5000000000 : ℝ)|=(854929203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2437382019/5000000000 : ℝ)|^4483 ≤ (4925900190589/12500000000000 : ℝ)^3459
        have hw : |(2437382019/5000000000 : ℝ)|=(2437382019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2949478861/5000000000 : ℝ)|^4483 ≤ (25228170606283/50000000000000 : ℝ)^3459
        have hw : |(2949478861/5000000000 : ℝ)|=(2949478861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s0_5 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5187019873/10000000000 : ℝ)*x 0 + (-1261463481/10000000000 : ℝ)*x 1 + (2949478747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5187019873/10000000000 : ℝ)^4483 ≤ (42709295240173/100000000000000 : ℝ)^3459 := by
    have hnat : (5187019873 : ℕ)^4483*100000000000000^3459 ≤ 42709295240173^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187019873 10000000000 42709295240173 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1261463481/10000000000 : ℝ)^4483 ≤ (1708591515511/25000000000000 : ℝ)^3459 := by
    have hnat : (1261463481 : ℕ)^4483*25000000000000^3459 ≤ 1708591515511^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1261463481 10000000000 1708591515511 25000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2949478747/5000000000 : ℝ)^4483 ≤ (12614084671263/25000000000000 : ℝ)^3459 := by
    have hnat : (2949478747 : ℕ)^4483*25000000000000^3459 ≤ 12614084671263^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2949478747 5000000000 12614084671263 25000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5187019873/10000000000 : ℝ), (-1261463481/10000000000 : ℝ), (2949478747/5000000000 : ℝ)] ![(42709295240173/100000000000000 : ℝ), (1708591515511/25000000000000 : ℝ), (12614084671263/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5187019873/10000000000 : ℝ)|^4483 ≤ (42709295240173/100000000000000 : ℝ)^3459
        have hw : |(5187019873/10000000000 : ℝ)|=(5187019873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1261463481/10000000000 : ℝ)|^4483 ≤ (1708591515511/25000000000000 : ℝ)^3459
        have hw : |(-1261463481/10000000000 : ℝ)|=(1261463481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2949478747/5000000000 : ℝ)|^4483 ≤ (12614084671263/25000000000000 : ℝ)^3459
        have hw : |(2949478747/5000000000 : ℝ)|=(2949478747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s0_6 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1296754981/2500000000 : ℝ)*x 0 + (5898957573/10000000000 : ℝ)*x 1 + (-1261463279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1296754981/2500000000 : ℝ)^4483 ≤ (1334665493263/3125000000000 : ℝ)^3459 := by
    have hnat : (1296754981 : ℕ)^4483*3125000000000^3459 ≤ 1334665493263^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296754981 2500000000 1334665493263 3125000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5898957573/10000000000 : ℝ)^4483 ≤ (25228169780407/50000000000000 : ℝ)^3459 := by
    have hnat : (5898957573 : ℕ)^4483*50000000000000^3459 ≤ 25228169780407^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5898957573 10000000000 25228169780407 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1261463279/10000000000 : ℝ)^4483 ≤ (3417182321831/50000000000000 : ℝ)^3459 := by
    have hnat : (1261463279 : ℕ)^4483*50000000000000^3459 ≤ 3417182321831^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1261463279 10000000000 3417182321831 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1296754981/2500000000 : ℝ), (5898957573/10000000000 : ℝ), (-1261463279/10000000000 : ℝ)] ![(1334665493263/3125000000000 : ℝ), (25228169780407/50000000000000 : ℝ), (3417182321831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1296754981/2500000000 : ℝ)|^4483 ≤ (1334665493263/3125000000000 : ℝ)^3459
        have hw : |(1296754981/2500000000 : ℝ)|=(1296754981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5898957573/10000000000 : ℝ)|^4483 ≤ (25228169780407/50000000000000 : ℝ)^3459
        have hw : |(5898957573/10000000000 : ℝ)|=(5898957573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1261463279/10000000000 : ℝ)|^4483 ≤ (3417182321831/50000000000000 : ℝ)^3459
        have hw : |(-1261463279/10000000000 : ℝ)|=(1261463279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s0_7 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039638397/2500000000 : ℝ)*x 0 + (680845491/1250000000 : ℝ)*x 1 + (1577688803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039638397/2500000000 : ℝ)^4483 ≤ (3207260542861/10000000000000 : ℝ)^3459 := by
    have hnat : (1039638397 : ℕ)^4483*10000000000000^3459 ≤ 3207260542861^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039638397 2500000000 3207260542861 10000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680845491/1250000000 : ℝ)^4483 ≤ (142192015919/312500000000 : ℝ)^3459 := by
    have hnat : (680845491 : ℕ)^4483*312500000000^3459 ≤ 142192015919^3459*1250000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680845491 1250000000 142192015919 312500000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1577688803/5000000000 : ℝ)^4483 ≤ (22425949464371/100000000000000 : ℝ)^3459 := by
    have hnat : (1577688803 : ℕ)^4483*100000000000000^3459 ≤ 22425949464371^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577688803 5000000000 22425949464371 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039638397/2500000000 : ℝ), (680845491/1250000000 : ℝ), (1577688803/5000000000 : ℝ)] ![(3207260542861/10000000000000 : ℝ), (142192015919/312500000000 : ℝ), (22425949464371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039638397/2500000000 : ℝ)|^4483 ≤ (3207260542861/10000000000000 : ℝ)^3459
        have hw : |(1039638397/2500000000 : ℝ)|=(1039638397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(680845491/1250000000 : ℝ)|^4483 ≤ (142192015919/312500000000 : ℝ)^3459
        have hw : |(680845491/1250000000 : ℝ)|=(680845491/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1577688803/5000000000 : ℝ)|^4483 ≤ (22425949464371/100000000000000 : ℝ)^3459
        have hw : |(1577688803/5000000000 : ℝ)|=(1577688803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1493_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161862961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2579/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6433/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4481/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4481 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4481*1^1024 ≤ 0^1024*1^4481 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4481 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4481/1024 : ℝ) ≤ (906971944364252357/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4481 ≤ (906971944364252357/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4481*50000000000000000000^1024 ≤ 906971944364252357^1024*5^4481 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 906971944364252357 50000000000000000000 4481 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (906971944364252357/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4481 := by
      have hnat : (1 : ℕ)^1024*1^4481 ≤ 1^4481*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50906971944364252357/50000000000000000000 : ℝ) ≤ (2510291335974061/2500000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (50906971944364252357/50000000000000000000 : ℝ)^1024 ≤ (2510291335974061/2500000000000000 : ℝ)^4481 := by
      have hnat : (50906971944364252357 : ℕ)^1024*2500000000000000^4481 ≤ 2510291335974061^4481*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50906971944364252357 50000000000000000000 2510291335974061 2500000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2510291335974061/2500000000000000 : ℝ)) (X := (50906971944364252357/50000000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25906971944364252357/25000000000000000000 : ℝ) ≤ (1260291335974061/1250000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (25906971944364252357/25000000000000000000 : ℝ)^1024 ≤ (1260291335974061/1250000000000000 : ℝ)^4481 := by
      have hnat : (25906971944364252357 : ℕ)^1024*1250000000000000^4481 ≤ 1260291335974061^4481*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25906971944364252357 25000000000000000000 1260291335974061 1250000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1260291335974061/1250000000000000 : ℝ)) (X := (25906971944364252357/25000000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(10291335974061/1000000000000000 : ℝ)*(0 : ℝ))^(4481/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(10291335974061/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(906971944364252357/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(10291335974061/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4481/1024 : ℝ) := by
    rw [show (1 : ℝ)+(10291335974061/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2510291335974061/2500000000000000 : ℝ) by norm_num, show 1+(906971944364252357/50000000000000000000 : ℝ)+(0 : ℝ)=(50906971944364252357/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(906971944364252357/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(10291335974061/1000000000000000 : ℝ)*(2/5 : ℝ))^(4481/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(10291335974061/1000000000000000 : ℝ)*(2/5 : ℝ)=(1260291335974061/1250000000000000 : ℝ) by norm_num, show 1+2*(906971944364252357/50000000000000000000 : ℝ)=(25906971944364252357/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(10291335974061/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10291335974061/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(10291335974061/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10291335974061/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(10291335974061/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10291335974061/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-426543467/2500000000 : ℝ)*X 0 0+(237104323/400000000 : ℝ)*X 0 1+(969421159/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((42829109/78125000 : ℝ)*X 1 0+(-289164417/1250000000 : ℝ)*X 1 1+(2423553061/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1370531457/2500000000 : ℝ)*X 2 0+(4847107279/10000000000 : ℝ)*X 2 1+(-289164257/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((129697071/312500000 : ℝ)*X 0 0+(1545640201/5000000000 : ℝ)*X 0 1+(2754319661/5000000000 : ℝ)*X 0 2+(129697071/312500000 : ℝ)*X 1 0+(1545640201/5000000000 : ℝ)*X 1 1+(2754319661/5000000000 : ℝ)*X 1 2+(129697071/312500000 : ℝ)*X 2 0+(1545640201/5000000000 : ℝ)*X 2 1+(2754319661/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-854929203/5000000000 : ℝ)*X 0 0+(2437382019/5000000000 : ℝ)*X 0 1+(2949478861/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5187019873/10000000000 : ℝ)*X 1 0+(-1261463481/10000000000 : ℝ)*X 1 1+(2949478747/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1296754981/2500000000 : ℝ)*X 2 0+(5898957573/10000000000 : ℝ)*X 2 1+(-1261463279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1039638397/2500000000 : ℝ)*X 0 0+(680845491/1250000000 : ℝ)*X 0 1+(1577688803/5000000000 : ℝ)*X 0 2+(1039638397/2500000000 : ℝ)*X 1 0+(680845491/1250000000 : ℝ)*X 1 1+(1577688803/5000000000 : ℝ)*X 1 2+(1039638397/2500000000 : ℝ)*X 2 0+(680845491/1250000000 : ℝ)*X 2 1+(1577688803/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4752768275144149208031/781250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1980013683/100000000000000 : ℝ)*(base19) + (1706384853/100000000000000 : ℝ)*(base23) + (224865697/100000000000000 : ℝ)*(upper3) + (138530477/100000000000000 : ℝ)*(upper4) + (176317333/50000000000000 : ℝ)*(upper5) + (83699346598597/12500000000000 : ℝ)*(major0) + (83699346598597/12500000000000 : ℝ)*(major1) + (83699346598597/12500000000000 : ℝ)*(major2) + (925501446250217/100000000000000 : ℝ)*(sp0) + (925507315996313/100000000000000 : ℝ)*(sp1) + (925507589625143/100000000000000 : ℝ)*(sp2) + (103419352014293/25000000000000 : ℝ)*(sp3) + (3924879889/50000000000000 : ℝ)*(sp4) + (2638725597/100000000000000 : ℝ)*(sp7) + (41368004678277/10000000000000 : ℝ)*(f.failure) + (231377324002499/25000000000000 : ℝ)*(f.sum) + (9571348517417/6250000000000000000000000000 : ℝ)*base65 + (43729496004917/12500000000000000000000000000 : ℝ)*base67 + (59317778529917/12500000000000000000000000000 : ℝ)*base69 + (29390701457583/12500000000000000000000000000 : ℝ)*base72 + (33087596042417/6250000000000000000000000000 : ℝ)*base73 + (80093658407583/12500000000000000000000000000 : ℝ)*base76 + (17451681807583/12500000000000000000000000000 : ℝ)*base78 + (56567379720083/12500000000000000000000000000 : ℝ)*base80 + (32859245004917/6250000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (7598197/1000000000000000000000 : ℝ)*base89 + (7598197/1000000000000000000000 : ℝ)*base91 + (7598197/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17216230857422888748651/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9959703/2000000000000 : ℝ)*(base19) + (259603543/50000000000000 : ℝ)*(base23) + (5065583/20000000000000 : ℝ)*(base32) + (16622707/25000000000000 : ℝ)*(upper3) + (29781077/50000000000000 : ℝ)*(upper5) + (88299679399397/12500000000000 : ℝ)*(major0) + (88299679399397/12500000000000 : ℝ)*(major1) + (88299679399397/12500000000000 : ℝ)*(major2) + (1097812753/100000000000000 : ℝ)*(sp1) + (651045219/50000000000000 : ℝ)*(sp2) + (976377805329009/100000000000000 : ℝ)*(sp4) + (488188104765553/50000000000000 : ℝ)*(sp5) + (195275196806297/20000000000000 : ℝ)*(sp6) + (436416947913527/100000000000000 : ℝ)*(sp7) + (218208486620721/50000000000000 : ℝ)*(f.failure) + (976377805329009/100000000000000 : ℝ)*(f.sum) + (9932418403717/6250000000000000000000000000 : ℝ)*base65 + (52137453933783/12500000000000000000000000000 : ℝ)*base68 + (6552472208783/12500000000000000000000000000 : ℝ)*base70 + (49048552333783/12500000000000000000000000000 : ℝ)*base72 + (6428511846283/6250000000000000000000000000 : ℝ)*base74 + (25327218641217/12500000000000000000000000000 : ℝ)*base75 + (6528607458783/12500000000000000000000000000 : ℝ)*base78 + (22461275996283/12500000000000000000000000000 : ℝ)*base80 + (2313322797467/6250000000000000000000000000 : ℝ)*base81 + (14985119/5000000000000000000000 : ℝ)*base90 + (14985119/5000000000000000000000 : ℝ)*base92 + (14985119/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1493_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161862961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2579/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6433/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1493_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1493_s1_0 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-233127699/1250000000 : ℝ)*x 0 + (279173547/500000000 : ℝ)*x 1 + (5089231181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (233127699/1250000000 : ℝ)^4483 ≤ (226885952973/2000000000000 : ℝ)^3459 := by
    have hnat : (233127699 : ℕ)^4483*2000000000000^3459 ≤ 226885952973^3459*1250000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233127699 1250000000 226885952973 2000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (279173547/500000000 : ℝ)^4483 ≤ (23493513668203/50000000000000 : ℝ)^3459 := by
    have hnat : (279173547 : ℕ)^4483*50000000000000^3459 ≤ 23493513668203^3459*500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279173547 500000000 23493513668203 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5089231181/10000000000 : ℝ)^4483 ≤ (20834337496441/50000000000000 : ℝ)^3459 := by
    have hnat : (5089231181 : ℕ)^4483*50000000000000^3459 ≤ 20834337496441^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5089231181 10000000000 20834337496441 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-233127699/1250000000 : ℝ), (279173547/500000000 : ℝ), (5089231181/10000000000 : ℝ)] ![(226885952973/2000000000000 : ℝ), (23493513668203/50000000000000 : ℝ), (20834337496441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-233127699/1250000000 : ℝ)|^4483 ≤ (226885952973/2000000000000 : ℝ)^3459
        have hw : |(-233127699/1250000000 : ℝ)|=(233127699/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(279173547/500000000 : ℝ)|^4483 ≤ (23493513668203/50000000000000 : ℝ)^3459
        have hw : |(279173547/500000000 : ℝ)|=(279173547/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5089231181/10000000000 : ℝ)|^4483 ≤ (20834337496441/50000000000000 : ℝ)^3459
        have hw : |(5089231181/10000000000 : ℝ)|=(5089231181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s1_1 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5390121479/10000000000 : ℝ)*x 0 + (-2125906279/10000000000 : ℝ)*x 1 + (15903843/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5390121479/10000000000 : ℝ)^4483 ≤ (2805570518731/6250000000000 : ℝ)^3459 := by
    have hnat : (5390121479 : ℕ)^4483*6250000000000^3459 ≤ 2805570518731^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390121479 10000000000 2805570518731 6250000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2125906279/10000000000 : ℝ)^4483 ≤ (13442211773563/100000000000000 : ℝ)^3459 := by
    have hnat : (2125906279 : ℕ)^4483*100000000000000^3459 ≤ 13442211773563^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125906279 10000000000 13442211773563 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15903843/31250000 : ℝ)^4483 ≤ (41668659913979/100000000000000 : ℝ)^3459 := by
    have hnat : (15903843 : ℕ)^4483*100000000000000^3459 ≤ 41668659913979^3459*31250000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15903843 31250000 41668659913979 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5390121479/10000000000 : ℝ), (-2125906279/10000000000 : ℝ), (15903843/31250000 : ℝ)] ![(2805570518731/6250000000000 : ℝ), (13442211773563/100000000000000 : ℝ), (41668659913979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5390121479/10000000000 : ℝ)|^4483 ≤ (2805570518731/6250000000000 : ℝ)^3459
        have hw : |(5390121479/10000000000 : ℝ)|=(5390121479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2125906279/10000000000 : ℝ)|^4483 ≤ (13442211773563/100000000000000 : ℝ)^3459
        have hw : |(-2125906279/10000000000 : ℝ)|=(2125906279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(15903843/31250000 : ℝ)|^4483 ≤ (41668659913979/100000000000000 : ℝ)^3459
        have hw : |(15903843/31250000 : ℝ)|=(15903843/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s1_2 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5390120583/10000000000 : ℝ)*x 0 + (5089230513/10000000000 : ℝ)*x 1 + (-531476621/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5390120583/10000000000 : ℝ)^4483 ≤ (44889118628753/100000000000000 : ℝ)^3459 := by
    have hnat : (5390120583 : ℕ)^4483*100000000000000^3459 ≤ 44889118628753^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390120583 10000000000 44889118628753 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5089230513/10000000000 : ℝ)^4483 ≤ (20834333952209/50000000000000 : ℝ)^3459 := by
    have hnat : (5089230513 : ℕ)^4483*50000000000000^3459 ≤ 20834333952209^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5089230513 10000000000 20834333952209 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531476621/2500000000 : ℝ)^4483 ≤ (13442213453521/100000000000000 : ℝ)^3459 := by
    have hnat : (531476621 : ℕ)^4483*100000000000000^3459 ≤ 13442213453521^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531476621 2500000000 13442213453521 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5390120583/10000000000 : ℝ), (5089230513/10000000000 : ℝ), (-531476621/2500000000 : ℝ)] ![(44889118628753/100000000000000 : ℝ), (20834333952209/50000000000000 : ℝ), (13442213453521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5390120583/10000000000 : ℝ)|^4483 ≤ (44889118628753/100000000000000 : ℝ)^3459
        have hw : |(5390120583/10000000000 : ℝ)|=(5390120583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5089230513/10000000000 : ℝ)|^4483 ≤ (20834333952209/50000000000000 : ℝ)^3459
        have hw : |(5089230513/10000000000 : ℝ)|=(5089230513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-531476621/2500000000 : ℝ)|^4483 ≤ (13442213453521/100000000000000 : ℝ)^3459
        have hw : |(-531476621/2500000000 : ℝ)|=(531476621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s1_3 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (266033643/625000000 : ℝ)*x 0 + (933614591/2500000000 : ℝ)*x 1 + (4840202633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266033643/625000000 : ℝ)^4483 ≤ (4131927662429/12500000000000 : ℝ)^3459 := by
    have hnat : (266033643 : ℕ)^4483*12500000000000^3459 ≤ 4131927662429^3459*625000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266033643 625000000 4131927662429 12500000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (933614591/2500000000 : ℝ)^4483 ≤ (13949549526499/50000000000000 : ℝ)^3459 := by
    have hnat : (933614591 : ℕ)^4483*50000000000000^3459 ≤ 13949549526499^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933614591 2500000000 13949549526499 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4840202633/10000000000 : ℝ)^4483 ≤ (39045479630769/100000000000000 : ℝ)^3459 := by
    have hnat : (4840202633 : ℕ)^4483*100000000000000^3459 ≤ 39045479630769^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4840202633 10000000000 39045479630769 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(266033643/625000000 : ℝ), (933614591/2500000000 : ℝ), (4840202633/10000000000 : ℝ)] ![(4131927662429/12500000000000 : ℝ), (13949549526499/50000000000000 : ℝ), (39045479630769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(266033643/625000000 : ℝ)|^4483 ≤ (4131927662429/12500000000000 : ℝ)^3459
        have hw : |(266033643/625000000 : ℝ)|=(266033643/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(933614591/2500000000 : ℝ)|^4483 ≤ (13949549526499/50000000000000 : ℝ)^3459
        have hw : |(933614591/2500000000 : ℝ)|=(933614591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4840202633/10000000000 : ℝ)|^4483 ≤ (39045479630769/100000000000000 : ℝ)^3459
        have hw : |(4840202633/10000000000 : ℝ)|=(4840202633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s1_4 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-466340541/2500000000 : ℝ)*x 0 + (1018981573/2000000000 : ℝ)*x 1 + (697212491/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (466340541/2500000000 : ℝ)^4483 ≤ (28367456441/250000000000 : ℝ)^3459 := by
    have hnat : (466340541 : ℕ)^4483*250000000000^3459 ≤ 28367456441^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466340541 2500000000 28367456441 250000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1018981573/2000000000 : ℝ)^4483 ≤ (260805768231/625000000000 : ℝ)^3459 := by
    have hnat : (1018981573 : ℕ)^4483*625000000000^3459 ≤ 260805768231^3459*2000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018981573 2000000000 260805768231 625000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (697212491/1250000000 : ℝ)^4483 ≤ (2932755905403/6250000000000 : ℝ)^3459 := by
    have hnat : (697212491 : ℕ)^4483*6250000000000^3459 ≤ 2932755905403^3459*1250000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      697212491 1250000000 2932755905403 6250000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-466340541/2500000000 : ℝ), (1018981573/2000000000 : ℝ), (697212491/1250000000 : ℝ)] ![(28367456441/250000000000 : ℝ), (260805768231/625000000000 : ℝ), (2932755905403/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-466340541/2500000000 : ℝ)|^4483 ≤ (28367456441/250000000000 : ℝ)^3459
        have hw : |(-466340541/2500000000 : ℝ)|=(466340541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1018981573/2000000000 : ℝ)|^4483 ≤ (260805768231/625000000000 : ℝ)^3459
        have hw : |(1018981573/2000000000 : ℝ)|=(1018981573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(697212491/1250000000 : ℝ)|^4483 ≤ (2932755905403/6250000000000 : ℝ)^3459
        have hw : |(697212491/1250000000 : ℝ)|=(697212491/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s1_5 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105204939/200000000 : ℝ)*x 0 + (-1637436179/10000000000 : ℝ)*x 1 + (2788850009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105204939/200000000 : ℝ)^4483 ≤ (43492360509397/100000000000000 : ℝ)^3459 := by
    have hnat : (105204939 : ℕ)^4483*100000000000000^3459 ≤ 43492360509397^3459*200000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105204939 200000000 43492360509397 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1637436179/10000000000 : ℝ)^4483 ≤ (4791772005429/50000000000000 : ℝ)^3459 := by
    have hnat : (1637436179 : ℕ)^4483*50000000000000^3459 ≤ 4791772005429^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1637436179 10000000000 4791772005429 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2788850009/5000000000 : ℝ)^4483 ≤ (46924095467747/100000000000000 : ℝ)^3459 := by
    have hnat : (2788850009 : ℕ)^4483*100000000000000^3459 ≤ 46924095467747^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2788850009 5000000000 46924095467747 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105204939/200000000 : ℝ), (-1637436179/10000000000 : ℝ), (2788850009/5000000000 : ℝ)] ![(43492360509397/100000000000000 : ℝ), (4791772005429/50000000000000 : ℝ), (46924095467747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105204939/200000000 : ℝ)|^4483 ≤ (43492360509397/100000000000000 : ℝ)^3459
        have hw : |(105204939/200000000 : ℝ)|=(105204939/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1637436179/10000000000 : ℝ)|^4483 ≤ (4791772005429/50000000000000 : ℝ)^3459
        have hw : |(-1637436179/10000000000 : ℝ)|=(1637436179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2788850009/5000000000 : ℝ)|^4483 ≤ (46924095467747/100000000000000 : ℝ)^3459
        have hw : |(2788850009/5000000000 : ℝ)|=(2788850009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s1_6 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2630123447/5000000000 : ℝ)*x 0 + (278885001/500000000 : ℝ)*x 1 + (-51169883/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2630123447/5000000000 : ℝ)^4483 ≤ (43492359909311/100000000000000 : ℝ)^3459 := by
    have hnat : (2630123447 : ℕ)^4483*100000000000000^3459 ≤ 43492359909311^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630123447 5000000000 43492359909311 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (278885001/500000000 : ℝ)^4483 ≤ (23462047744777/50000000000000 : ℝ)^3459 := by
    have hnat : (278885001 : ℕ)^4483*50000000000000^3459 ≤ 23462047744777^3459*500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278885001 500000000 23462047744777 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51169883/312500000 : ℝ)^4483 ≤ (1916708918987/20000000000000 : ℝ)^3459 := by
    have hnat : (51169883 : ℕ)^4483*20000000000000^3459 ≤ 1916708918987^3459*312500000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51169883 312500000 1916708918987 20000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2630123447/5000000000 : ℝ), (278885001/500000000 : ℝ), (-51169883/312500000 : ℝ)] ![(43492359909311/100000000000000 : ℝ), (23462047744777/50000000000000 : ℝ), (1916708918987/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2630123447/5000000000 : ℝ)|^4483 ≤ (43492359909311/100000000000000 : ℝ)^3459
        have hw : |(2630123447/5000000000 : ℝ)|=(2630123447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(278885001/500000000 : ℝ)|^4483 ≤ (23462047744777/50000000000000 : ℝ)^3459
        have hw : |(278885001/500000000 : ℝ)|=(278885001/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51169883/312500000 : ℝ)|^4483 ≤ (1916708918987/20000000000000 : ℝ)^3459
        have hw : |(-51169883/312500000 : ℝ)|=(51169883/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s1_7 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4257299201/10000000000 : ℝ)*x 0 + (4827501743/10000000000 : ℝ)*x 1 + (1873684953/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4257299201/10000000000 : ℝ)^4483 ≤ (3306307992477/10000000000000 : ℝ)^3459 := by
    have hnat : (4257299201 : ℕ)^4483*10000000000000^3459 ≤ 3306307992477^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4257299201 10000000000 3306307992477 10000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4827501743/10000000000 : ℝ)^4483 ≤ (2432046438661/6250000000000 : ℝ)^3459 := by
    have hnat : (4827501743 : ℕ)^4483*6250000000000^3459 ≤ 2432046438661^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4827501743 10000000000 2432046438661 6250000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1873684953/5000000000 : ℝ)^4483 ≤ (7006044258747/25000000000000 : ℝ)^3459 := by
    have hnat : (1873684953 : ℕ)^4483*25000000000000^3459 ≤ 7006044258747^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873684953 5000000000 7006044258747 25000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4257299201/10000000000 : ℝ), (4827501743/10000000000 : ℝ), (1873684953/5000000000 : ℝ)] ![(3306307992477/10000000000000 : ℝ), (2432046438661/6250000000000 : ℝ), (7006044258747/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4257299201/10000000000 : ℝ)|^4483 ≤ (3306307992477/10000000000000 : ℝ)^3459
        have hw : |(4257299201/10000000000 : ℝ)|=(4257299201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4827501743/10000000000 : ℝ)|^4483 ≤ (2432046438661/6250000000000 : ℝ)^3459
        have hw : |(4827501743/10000000000 : ℝ)|=(4827501743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1873684953/5000000000 : ℝ)|^4483 ≤ (7006044258747/25000000000000 : ℝ)^3459
        have hw : |(1873684953/5000000000 : ℝ)|=(1873684953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1493_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161862961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6433/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2579/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4047/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1159/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6433/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2579/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6433/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2579/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6433/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2579/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6433/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2579/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6433/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2579/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6433/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2579/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2579/100000 : ℝ) ^ (4481/1024 : ℝ) ≤ (11182741987477/100000000000000000000 : ℝ) := by
    have hpowers : (2579/100000 : ℝ)^4481 ≤ (11182741987477/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2579 : ℕ)^4481*100000000000000000000^1024 ≤ 11182741987477^1024*100000^4481 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2579 100000 11182741987477 100000000000000000000 4481 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2579/100000 : ℝ)) (X := (11182741987477/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6433/25000 : ℝ) ^ (4481/1024 : ℝ) ≤ (263175853466640921/100000000000000000000 : ℝ) := by
    have hpowers : (6433/25000 : ℝ)^4481 ≤ (263175853466640921/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6433 : ℕ)^4481*100000000000000000000^1024 ≤ 263175853466640921^1024*25000^4481 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6433 25000 263175853466640921 100000000000000000000 4481 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6433/25000 : ℝ)) (X := (263175853466640921/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000011182741987477/50000000000000000000 : ℝ) ≤ (2000000102219387/2000000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (50000011182741987477/50000000000000000000 : ℝ)^1024 ≤ (2000000102219387/2000000000000000 : ℝ)^4481 := by
      have hnat : (50000011182741987477 : ℕ)^1024*2000000000000000^4481 ≤ 2000000102219387^4481*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000011182741987477 50000000000000000000 2000000102219387 2000000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000102219387/2000000000000000 : ℝ)) (X := (50000011182741987477/50000000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50131593518104314199/50000000000000000000 : ℝ) ≤ (2001201652956573/2000000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (50131593518104314199/50000000000000000000 : ℝ)^1024 ≤ (2001201652956573/2000000000000000 : ℝ)^4481 := by
      have hnat : (50131593518104314199 : ℕ)^1024*2000000000000000^4481 ≤ 2001201652956573^4481*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50131593518104314199 50000000000000000000 2001201652956573 2000000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001201652956573/2000000000000000 : ℝ)) (X := (50131593518104314199/50000000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50263175853466640921/50000000000000000000 : ℝ) ≤ (2002403203693759/2000000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (50263175853466640921/50000000000000000000 : ℝ)^1024 ≤ (2002403203693759/2000000000000000 : ℝ)^4481 := by
      have hnat : (50263175853466640921 : ℕ)^1024*2000000000000000^4481 ≤ 2002403203693759^4481*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50263175853466640921 50000000000000000000 2002403203693759 2000000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002403203693759/2000000000000000 : ℝ)) (X := (50263175853466640921/50000000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(11182741987477/100000000000000000000 : ℝ) ≤ ((46299804767983061823/46306000000000000000 : ℝ)+2*(600775368593/231530000000000 : ℝ)*(2579/100000 : ℝ))^(4481/1024 : ℝ) := by
    rw [show (46299804767983061823/46306000000000000000 : ℝ)+2*(600775368593/231530000000000 : ℝ)*(2579/100000 : ℝ)=(2000000102219387/2000000000000000 : ℝ) by norm_num, show 1+2*(11182741987477/100000000000000000000 : ℝ)=(50000011182741987477/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(263175853466640921/100000000000000000000 : ℝ)+(11182741987477/100000000000000000000 : ℝ) ≤ ((46299804767983061823/46306000000000000000 : ℝ)+(600775368593/231530000000000 : ℝ)*((6433/25000 : ℝ)+(2579/100000 : ℝ)))^(4481/1024 : ℝ) := by
    rw [show (46299804767983061823/46306000000000000000 : ℝ)+(600775368593/231530000000000 : ℝ)*((6433/25000 : ℝ)+(2579/100000 : ℝ))=(2001201652956573/2000000000000000 : ℝ) by norm_num, show 1+(263175853466640921/100000000000000000000 : ℝ)+(11182741987477/100000000000000000000 : ℝ)=(50131593518104314199/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(263175853466640921/100000000000000000000 : ℝ) ≤ ((46299804767983061823/46306000000000000000 : ℝ)+2*(600775368593/231530000000000 : ℝ)*(6433/25000 : ℝ))^(4481/1024 : ℝ) := by
    rw [show (46299804767983061823/46306000000000000000 : ℝ)+2*(600775368593/231530000000000 : ℝ)*(6433/25000 : ℝ)=(2002403203693759/2000000000000000 : ℝ) by norm_num, show 1+2*(263175853466640921/100000000000000000000 : ℝ)=(50263175853466640921/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46299804767983061823/46306000000000000000 : ℝ)*(X 1 0+X 2 0)+(600775368593/231530000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (2579/100000 : ℝ)) (hi := (6433/25000 : ℝ)) (c := (46299804767983061823/46306000000000000000 : ℝ)) (alpha := (600775368593/231530000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46299804767983061823/46306000000000000000 : ℝ)*(X 0 1+X 2 1)+(600775368593/231530000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (2579/100000 : ℝ)) (hi := (6433/25000 : ℝ)) (c := (46299804767983061823/46306000000000000000 : ℝ)) (alpha := (600775368593/231530000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46299804767983061823/46306000000000000000 : ℝ)*(X 0 2+X 1 2)+(600775368593/231530000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (2579/100000 : ℝ)) (hi := (6433/25000 : ℝ)) (c := (46299804767983061823/46306000000000000000 : ℝ)) (alpha := (600775368593/231530000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-233127699/1250000000 : ℝ)*X 0 0+(279173547/500000000 : ℝ)*X 0 1+(5089231181/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5390121479/10000000000 : ℝ)*X 1 0+(-2125906279/10000000000 : ℝ)*X 1 1+(15903843/31250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5390120583/10000000000 : ℝ)*X 2 0+(5089230513/10000000000 : ℝ)*X 2 1+(-531476621/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((266033643/625000000 : ℝ)*X 0 0+(933614591/2500000000 : ℝ)*X 0 1+(4840202633/10000000000 : ℝ)*X 0 2+(266033643/625000000 : ℝ)*X 1 0+(933614591/2500000000 : ℝ)*X 1 1+(4840202633/10000000000 : ℝ)*X 1 2+(266033643/625000000 : ℝ)*X 2 0+(933614591/2500000000 : ℝ)*X 2 1+(4840202633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-466340541/2500000000 : ℝ)*X 0 0+(1018981573/2000000000 : ℝ)*X 0 1+(697212491/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((105204939/200000000 : ℝ)*X 1 0+(-1637436179/10000000000 : ℝ)*X 1 1+(2788850009/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2630123447/5000000000 : ℝ)*X 2 0+(278885001/500000000 : ℝ)*X 2 1+(-51169883/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4257299201/10000000000 : ℝ)*X 0 0+(4827501743/10000000000 : ℝ)*X 0 1+(1873684953/5000000000 : ℝ)*X 0 2+(4257299201/10000000000 : ℝ)*X 1 0+(4827501743/10000000000 : ℝ)*X 1 1+(1873684953/5000000000 : ℝ)*X 1 2+(4257299201/10000000000 : ℝ)*X 2 0+(4827501743/10000000000 : ℝ)*X 2 1+(1873684953/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3429622641483116214712104021/578825000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (100167969/50000000000000 : ℝ)*(base1) + (185409303/20000000000000 : ℝ)*(base19) + (27310909/5000000000000 : ℝ)*(base23) + (16445833/25000000000000 : ℝ)*(upper3) + (3886427/4000000000000 : ℝ)*(upper5) + (365959990853597/25000000000000 : ℝ)*(major0) + (365959990853597/25000000000000 : ℝ)*(major1) + (365959990853597/25000000000000 : ℝ)*(major2) + (2023309989575529/100000000000000 : ℝ)*(sp0) + (505827215548269/25000000000000 : ℝ)*(sp1) + (2023307396412531/100000000000000 : ℝ)*(sp2) + (904369272823431/100000000000000 : ℝ)*(sp3) + (23082611/1250000000000 : ℝ)*(sp6) + (23346247/5000000000000 : ℝ)*(sp7) + (226092485021077/25000000000000 : ℝ)*(f.failure) + (2023309789239591/100000000000000 : ℝ)*(f.sum) + (1989022816617/5788250000000000000000000000 : ℝ)*base65 + (9006736163682527331/1157650000000000000000000000000000 : ℝ)*base67 + (6551366709425327331/1157650000000000000000000000000000 : ℝ)*base69 + (2987935642086327331/1157650000000000000000000000000000 : ℝ)*base71 + (24503022011967/5788250000000000000000000000 : ℝ)*base73 + (1800635040891177331/1157650000000000000000000000000000 : ℝ)*base75 + (3957623928335477331/1157650000000000000000000000000000 : ℝ)*base77 + (553218447348577331/1157650000000000000000000000000000 : ℝ)*base79 + (90666287602781/23153000000000000000000000000 : ℝ)*base81 + (29371003/2500000000000000000000 : ℝ)*base90 + (29371003/2500000000000000000000 : ℝ)*base92 + (29371003/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1923876500204051751654053151/578825000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (661390861/100000000000000 : ℝ)*(base19) + (673674223/100000000000000 : ℝ)*(base23) + (51728589/50000000000000 : ℝ)*(upper3) + (12659033/100000000000000 : ℝ)*(lower4) + (3741057/10000000000000 : ℝ)*(upper5) + (374637166766979/25000000000000 : ℝ)*(major0) + (374637166766979/25000000000000 : ℝ)*(major1) + (374637166766979/25000000000000 : ℝ)*(major2) + (1062865417/25000000000000 : ℝ)*(sp1) + (4667393683/100000000000000 : ℝ)*(sp2) + (517821004566493/25000000000000 : ℝ)*(sp4) + (2071279105413443/100000000000000 : ℝ)*(sp5) + (2071278677198067/100000000000000 : ℝ)*(sp6) + (28931662658681/3125000000000 : ℝ)*(sp7) + (28931662658681/3125000000000 : ℝ)*(f.failure) + (517821004566493/25000000000000 : ℝ)*(f.sum) + (3663264288447/2894125000000000000000000000 : ℝ)*base66 + (891711117354057283/1157650000000000000000000000000000 : ℝ)*base68 + (2535593024093857283/1157650000000000000000000000000000 : ℝ)*base70 + (1909224472294242717/1157650000000000000000000000000000 : ℝ)*base71 + (15647824643207/4630600000000000000000000000 : ℝ)*base74 + (1522975485175442717/1157650000000000000000000000000000 : ℝ)*base75 + (3184800494233007283/1157650000000000000000000000000000 : ℝ)*base78 + (6856202840387407283/1157650000000000000000000000000000 : ℝ)*base80 + (11340732300827/5788250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1514441/312500000000000000000 : ℝ)*base89 + (1514441/312500000000000000000 : ℝ)*base91 + (1514441/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1493_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161862961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6433/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2579/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4047/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1159/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1493_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1493_s2_0 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1891808829/10000000000 : ℝ)*x 0 + (2732127921/5000000000 : ℝ)*x 1 + (2595565061/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1891808829/10000000000 : ℝ)^4483 ≤ (11555918808189/100000000000000 : ℝ)^3459 := by
    have hnat : (1891808829 : ℕ)^4483*100000000000000^3459 ≤ 11555918808189^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1891808829 10000000000 11555918808189 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2732127921/5000000000 : ℝ)^4483 ≤ (11422729638663/25000000000000 : ℝ)^3459 := by
    have hnat : (2732127921 : ℕ)^4483*25000000000000^3459 ≤ 11422729638663^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732127921 5000000000 11422729638663 25000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2595565061/5000000000 : ℝ)^4483 ≤ (42753162623463/100000000000000 : ℝ)^3459 := by
    have hnat : (2595565061 : ℕ)^4483*100000000000000^3459 ≤ 42753162623463^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2595565061 5000000000 42753162623463 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1891808829/10000000000 : ℝ), (2732127921/5000000000 : ℝ), (2595565061/5000000000 : ℝ)] ![(11555918808189/100000000000000 : ℝ), (11422729638663/25000000000000 : ℝ), (42753162623463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1891808829/10000000000 : ℝ)|^4483 ≤ (11555918808189/100000000000000 : ℝ)^3459
        have hw : |(-1891808829/10000000000 : ℝ)|=(1891808829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2732127921/5000000000 : ℝ)|^4483 ≤ (11422729638663/25000000000000 : ℝ)^3459
        have hw : |(2732127921/5000000000 : ℝ)|=(2732127921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2595565061/5000000000 : ℝ)|^4483 ≤ (42753162623463/100000000000000 : ℝ)^3459
        have hw : |(2595565061/5000000000 : ℝ)|=(2595565061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s2_1 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2680007761/5000000000 : ℝ)*x 0 + (-1016287517/5000000000 : ℝ)*x 1 + (2595564857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680007761/5000000000 : ℝ)^4483 ≤ (8912889955609/20000000000000 : ℝ)^3459 := by
    have hnat : (2680007761 : ℕ)^4483*20000000000000^3459 ≤ 8912889955609^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680007761 5000000000 8912889955609 20000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016287517/5000000000 : ℝ)^4483 ≤ (198162374031/1562500000000 : ℝ)^3459 := by
    have hnat : (1016287517 : ℕ)^4483*1562500000000^3459 ≤ 198162374031^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016287517 5000000000 198162374031 1562500000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2595564857/5000000000 : ℝ)^4483 ≤ (21376579134249/50000000000000 : ℝ)^3459 := by
    have hnat : (2595564857 : ℕ)^4483*50000000000000^3459 ≤ 21376579134249^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2595564857 5000000000 21376579134249 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680007761/5000000000 : ℝ), (-1016287517/5000000000 : ℝ), (2595564857/5000000000 : ℝ)] ![(8912889955609/20000000000000 : ℝ), (198162374031/1562500000000 : ℝ), (21376579134249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680007761/5000000000 : ℝ)|^4483 ≤ (8912889955609/20000000000000 : ℝ)^3459
        have hw : |(2680007761/5000000000 : ℝ)|=(2680007761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1016287517/5000000000 : ℝ)|^4483 ≤ (198162374031/1562500000000 : ℝ)^3459
        have hw : |(-1016287517/5000000000 : ℝ)|=(1016287517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2595564857/5000000000 : ℝ)|^4483 ≤ (21376579134249/50000000000000 : ℝ)^3459
        have hw : |(2595564857/5000000000 : ℝ)|=(2595564857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s2_2 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5360015603/10000000000 : ℝ)*x 0 + (5191129407/10000000000 : ℝ)*x 1 + (-2032575331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5360015603/10000000000 : ℝ)^4483 ≤ (44564450650867/100000000000000 : ℝ)^3459 := by
    have hnat : (5360015603 : ℕ)^4483*100000000000000^3459 ≤ 44564450650867^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5360015603 10000000000 44564450650867 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5191129407/10000000000 : ℝ)^4483 ≤ (42753154991601/100000000000000 : ℝ)^3459 := by
    have hnat : (5191129407 : ℕ)^4483*100000000000000^3459 ≤ 42753154991601^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191129407 10000000000 42753154991601 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2032575331/10000000000 : ℝ)^4483 ≤ (12682394339741/100000000000000 : ℝ)^3459 := by
    have hnat : (2032575331 : ℕ)^4483*100000000000000^3459 ≤ 12682394339741^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2032575331 10000000000 12682394339741 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5360015603/10000000000 : ℝ), (5191129407/10000000000 : ℝ), (-2032575331/10000000000 : ℝ)] ![(44564450650867/100000000000000 : ℝ), (42753154991601/100000000000000 : ℝ), (12682394339741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5360015603/10000000000 : ℝ)|^4483 ≤ (44564450650867/100000000000000 : ℝ)^3459
        have hw : |(5360015603/10000000000 : ℝ)|=(5360015603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5191129407/10000000000 : ℝ)|^4483 ≤ (42753154991601/100000000000000 : ℝ)^3459
        have hw : |(5191129407/10000000000 : ℝ)|=(5191129407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2032575331/10000000000 : ℝ)|^4483 ≤ (12682394339741/100000000000000 : ℝ)^3459
        have hw : |(-2032575331/10000000000 : ℝ)|=(2032575331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s2_3 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534462751/1250000000 : ℝ)*x 0 + (397958101/1000000000 : ℝ)*x 1 + (918126883/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534462751/1250000000 : ℝ)^4483 ≤ (16624214172681/50000000000000 : ℝ)^3459 := by
    have hnat : (534462751 : ℕ)^4483*50000000000000^3459 ≤ 16624214172681^3459*1250000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534462751 1250000000 16624214172681 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397958101/1000000000 : ℝ)^4483 ≤ (15147587720593/50000000000000 : ℝ)^3459 := by
    have hnat : (397958101 : ℕ)^4483*50000000000000^3459 ≤ 15147587720593^3459*1000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397958101 1000000000 15147587720593 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (918126883/2000000000 : ℝ)^4483 ≤ (36456396198371/100000000000000 : ℝ)^3459 := by
    have hnat : (918126883 : ℕ)^4483*100000000000000^3459 ≤ 36456396198371^3459*2000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      918126883 2000000000 36456396198371 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534462751/1250000000 : ℝ), (397958101/1000000000 : ℝ), (918126883/2000000000 : ℝ)] ![(16624214172681/50000000000000 : ℝ), (15147587720593/50000000000000 : ℝ), (36456396198371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534462751/1250000000 : ℝ)|^4483 ≤ (16624214172681/50000000000000 : ℝ)^3459
        have hw : |(534462751/1250000000 : ℝ)|=(534462751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(397958101/1000000000 : ℝ)|^4483 ≤ (15147587720593/50000000000000 : ℝ)^3459
        have hw : |(397958101/1000000000 : ℝ)|=(397958101/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(918126883/2000000000 : ℝ)|^4483 ≤ (36456396198371/100000000000000 : ℝ)^3459
        have hw : |(918126883/2000000000 : ℝ)|=(918126883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s2_4 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-472966223/2500000000 : ℝ)*x 0 + (2596437293/5000000000 : ℝ)*x 1 + (1092499307/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (472966223/2500000000 : ℝ)^4483 ≤ (5778181322669/50000000000000 : ℝ)^3459 := by
    have hnat : (472966223 : ℕ)^4483*50000000000000^3459 ≤ 5778181322669^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472966223 2500000000 5778181322669 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2596437293/5000000000 : ℝ)^4483 ≤ (10692945960749/25000000000000 : ℝ)^3459 := by
    have hnat : (2596437293 : ℕ)^4483*25000000000000^3459 ≤ 10692945960749^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596437293 5000000000 10692945960749 25000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092499307/2000000000 : ℝ)^4483 ≤ (45671853503627/100000000000000 : ℝ)^3459 := by
    have hnat : (1092499307 : ℕ)^4483*100000000000000^3459 ≤ 45671853503627^3459*2000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092499307 2000000000 45671853503627 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-472966223/2500000000 : ℝ), (2596437293/5000000000 : ℝ), (1092499307/2000000000 : ℝ)] ![(5778181322669/50000000000000 : ℝ), (10692945960749/25000000000000 : ℝ), (45671853503627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-472966223/2500000000 : ℝ)|^4483 ≤ (5778181322669/50000000000000 : ℝ)^3459
        have hw : |(-472966223/2500000000 : ℝ)|=(472966223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2596437293/5000000000 : ℝ)|^4483 ≤ (10692945960749/25000000000000 : ℝ)^3459
        have hw : |(2596437293/5000000000 : ℝ)|=(2596437293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092499307/2000000000 : ℝ)|^4483 ≤ (45671853503627/100000000000000 : ℝ)^3459
        have hw : |(1092499307/2000000000 : ℝ)|=(1092499307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s2_5 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322126109/2500000000 : ℝ)*x 0 + (-1761208107/10000000000 : ℝ)*x 1 + (5462497723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322126109/2500000000 : ℝ)^4483 ≤ (43795402842021/100000000000000 : ℝ)^3459 := by
    have hnat : (1322126109 : ℕ)^4483*100000000000000^3459 ≤ 43795402842021^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322126109 2500000000 43795402842021 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1761208107/10000000000 : ℝ)^4483 ≤ (5266365381829/50000000000000 : ℝ)^3459 := by
    have hnat : (1761208107 : ℕ)^4483*50000000000000^3459 ≤ 5266365381829^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1761208107 10000000000 5266365381829 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5462497723/10000000000 : ℝ)^4483 ≤ (45671866376993/100000000000000 : ℝ)^3459 := by
    have hnat : (5462497723 : ℕ)^4483*100000000000000^3459 ≤ 45671866376993^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462497723 10000000000 45671866376993 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322126109/2500000000 : ℝ), (-1761208107/10000000000 : ℝ), (5462497723/10000000000 : ℝ)] ![(43795402842021/100000000000000 : ℝ), (5266365381829/50000000000000 : ℝ), (45671866376993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322126109/2500000000 : ℝ)|^4483 ≤ (43795402842021/100000000000000 : ℝ)^3459
        have hw : |(1322126109/2500000000 : ℝ)|=(1322126109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1761208107/10000000000 : ℝ)|^4483 ≤ (5266365381829/50000000000000 : ℝ)^3459
        have hw : |(-1761208107/10000000000 : ℝ)|=(1761208107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5462497723/10000000000 : ℝ)|^4483 ≤ (45671866376993/100000000000000 : ℝ)^3459
        have hw : |(5462497723/10000000000 : ℝ)|=(5462497723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s2_6 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288505139/10000000000 : ℝ)*x 0 + (5462495961/10000000000 : ℝ)*x 1 + (-1761209597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288505139/10000000000 : ℝ)^4483 ≤ (43795410387193/100000000000000 : ℝ)^3459 := by
    have hnat : (5288505139 : ℕ)^4483*100000000000000^3459 ≤ 43795410387193^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288505139 10000000000 43795410387193 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462495961/10000000000 : ℝ)^4483 ≤ (11417961820917/25000000000000 : ℝ)^3459 := by
    have hnat : (5462495961 : ℕ)^4483*25000000000000^3459 ≤ 11417961820917^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462495961 10000000000 11417961820917 25000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1761209597/10000000000 : ℝ)^4483 ≤ (10532742312403/100000000000000 : ℝ)^3459 := by
    have hnat : (1761209597 : ℕ)^4483*100000000000000^3459 ≤ 10532742312403^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1761209597 10000000000 10532742312403 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288505139/10000000000 : ℝ), (5462495961/10000000000 : ℝ), (-1761209597/10000000000 : ℝ)] ![(43795410387193/100000000000000 : ℝ), (11417961820917/25000000000000 : ℝ), (10532742312403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288505139/10000000000 : ℝ)|^4483 ≤ (43795410387193/100000000000000 : ℝ)^3459
        have hw : |(5288505139/10000000000 : ℝ)|=(5288505139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462495961/10000000000 : ℝ)|^4483 ≤ (11417961820917/25000000000000 : ℝ)^3459
        have hw : |(5462495961/10000000000 : ℝ)|=(5462495961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1761209597/10000000000 : ℝ)|^4483 ≤ (10532742312403/100000000000000 : ℝ)^3459
        have hw : |(-1761209597/10000000000 : ℝ)|=(1761209597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s2_7 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4275832557/10000000000 : ℝ)*x 0 + (1146684009/2500000000 : ℝ)*x 1 + (796702667/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4275832557/10000000000 : ℝ)^4483 ≤ (33249744046893/100000000000000 : ℝ)^3459 := by
    have hnat : (4275832557 : ℕ)^4483*100000000000000^3459 ≤ 33249744046893^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4275832557 10000000000 33249744046893 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1146684009/2500000000 : ℝ)^4483 ≤ (36416277331479/100000000000000 : ℝ)^3459 := by
    have hnat : (1146684009 : ℕ)^4483*100000000000000^3459 ≤ 36416277331479^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146684009 2500000000 36416277331479 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (796702667/2000000000 : ℝ)^4483 ≤ (15166989305513/50000000000000 : ℝ)^3459 := by
    have hnat : (796702667 : ℕ)^4483*50000000000000^3459 ≤ 15166989305513^3459*2000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796702667 2000000000 15166989305513 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4275832557/10000000000 : ℝ), (1146684009/2500000000 : ℝ), (796702667/2000000000 : ℝ)] ![(33249744046893/100000000000000 : ℝ), (36416277331479/100000000000000 : ℝ), (15166989305513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4275832557/10000000000 : ℝ)|^4483 ≤ (33249744046893/100000000000000 : ℝ)^3459
        have hw : |(4275832557/10000000000 : ℝ)|=(4275832557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1146684009/2500000000 : ℝ)|^4483 ≤ (36416277331479/100000000000000 : ℝ)^3459
        have hw : |(1146684009/2500000000 : ℝ)|=(1146684009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(796702667/2000000000 : ℝ)|^4483 ≤ (15166989305513/50000000000000 : ℝ)^3459
        have hw : |(796702667/2000000000 : ℝ)|=(796702667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1493_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161862961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1159/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4047/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5147/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16073/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1159/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4047/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1159/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4047/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1159/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4047/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1159/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4047/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1159/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4047/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1159/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4047/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4047/50000 : ℝ) ^ (4481/1024 : ℝ) ≤ (1667814531065507/100000000000000000000 : ℝ) := by
    have hpowers : (4047/50000 : ℝ)^4481 ≤ (1667814531065507/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4047 : ℕ)^4481*100000000000000000000^1024 ≤ 1667814531065507^1024*50000^4481 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4047 50000 1667814531065507 100000000000000000000 4481 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4047/50000 : ℝ)) (X := (1667814531065507/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1159/6250 : ℝ) ^ (4481/1024 : ℝ) ≤ (62758898328120067/100000000000000000000 : ℝ) := by
    have hpowers : (1159/6250 : ℝ)^4481 ≤ (62758898328120067/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1159 : ℕ)^4481*100000000000000000000^1024 ≤ 62758898328120067^1024*6250^4481 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1159 6250 62758898328120067 100000000000000000000 4481 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1159/6250 : ℝ)) (X := (62758898328120067/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001667814531065507/50000000000000000000 : ℝ) ≤ (5000038112477253/5000000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (50001667814531065507/50000000000000000000 : ℝ)^1024 ≤ (5000038112477253/5000000000000000 : ℝ)^4481 := by
      have hnat : (50001667814531065507 : ℕ)^1024*5000000000000000^4481 ≤ 5000038112477253^4481*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001667814531065507 50000000000000000000 5000038112477253 5000000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000038112477253/5000000000000000 : ℝ)) (X := (50001667814531065507/50000000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50032213356429592787/50000000000000000000 : ℝ) ≤ (1250183989524211/1250000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (50032213356429592787/50000000000000000000 : ℝ)^1024 ≤ (1250183989524211/1250000000000000 : ℝ)^4481 := by
      have hnat : (50032213356429592787 : ℕ)^1024*1250000000000000^4481 ≤ 1250183989524211^4481*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032213356429592787 50000000000000000000 1250183989524211 1250000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250183989524211/1250000000000000 : ℝ)) (X := (50032213356429592787/50000000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50062758898328120067/50000000000000000000 : ℝ) ≤ (1000286760743287/1000000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (50062758898328120067/50000000000000000000 : ℝ)^1024 ≤ (1000286760743287/1000000000000000 : ℝ)^4481 := by
      have hnat : (50062758898328120067 : ℕ)^1024*1000000000000000^4481 ≤ 1000286760743287^4481*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50062758898328120067 50000000000000000000 1000286760743287 1000000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000286760743287/1000000000000000 : ℝ)) (X := (50062758898328120067/50000000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1667814531065507/100000000000000000000 : ℝ) ≤ ((1374713198697298809/1375000000000000000 : ℝ)+2*(697845619591/522500000000000 : ℝ)*(4047/50000 : ℝ))^(4481/1024 : ℝ) := by
    rw [show (1374713198697298809/1375000000000000000 : ℝ)+2*(697845619591/522500000000000 : ℝ)*(4047/50000 : ℝ)=(5000038112477253/5000000000000000 : ℝ) by norm_num, show 1+2*(1667814531065507/100000000000000000000 : ℝ)=(50001667814531065507/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(62758898328120067/100000000000000000000 : ℝ)+(1667814531065507/100000000000000000000 : ℝ) ≤ ((1374713198697298809/1375000000000000000 : ℝ)+(697845619591/522500000000000 : ℝ)*((1159/6250 : ℝ)+(4047/50000 : ℝ)))^(4481/1024 : ℝ) := by
    rw [show (1374713198697298809/1375000000000000000 : ℝ)+(697845619591/522500000000000 : ℝ)*((1159/6250 : ℝ)+(4047/50000 : ℝ))=(1250183989524211/1250000000000000 : ℝ) by norm_num, show 1+(62758898328120067/100000000000000000000 : ℝ)+(1667814531065507/100000000000000000000 : ℝ)=(50032213356429592787/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(62758898328120067/100000000000000000000 : ℝ) ≤ ((1374713198697298809/1375000000000000000 : ℝ)+2*(697845619591/522500000000000 : ℝ)*(1159/6250 : ℝ))^(4481/1024 : ℝ) := by
    rw [show (1374713198697298809/1375000000000000000 : ℝ)+2*(697845619591/522500000000000 : ℝ)*(1159/6250 : ℝ)=(1000286760743287/1000000000000000 : ℝ) by norm_num, show 1+2*(62758898328120067/100000000000000000000 : ℝ)=(50062758898328120067/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1374713198697298809/1375000000000000000 : ℝ)*(X 1 0+X 2 0)+(697845619591/522500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (4047/50000 : ℝ)) (hi := (1159/6250 : ℝ)) (c := (1374713198697298809/1375000000000000000 : ℝ)) (alpha := (697845619591/522500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1374713198697298809/1375000000000000000 : ℝ)*(X 0 1+X 2 1)+(697845619591/522500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (4047/50000 : ℝ)) (hi := (1159/6250 : ℝ)) (c := (1374713198697298809/1375000000000000000 : ℝ)) (alpha := (697845619591/522500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1374713198697298809/1375000000000000000 : ℝ)*(X 0 2+X 1 2)+(697845619591/522500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (4047/50000 : ℝ)) (hi := (1159/6250 : ℝ)) (c := (1374713198697298809/1375000000000000000 : ℝ)) (alpha := (697845619591/522500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1891808829/10000000000 : ℝ)*X 0 0+(2732127921/5000000000 : ℝ)*X 0 1+(2595565061/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2680007761/5000000000 : ℝ)*X 1 0+(-1016287517/5000000000 : ℝ)*X 1 1+(2595564857/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5360015603/10000000000 : ℝ)*X 2 0+(5191129407/10000000000 : ℝ)*X 2 1+(-2032575331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((534462751/1250000000 : ℝ)*X 0 0+(397958101/1000000000 : ℝ)*X 0 1+(918126883/2000000000 : ℝ)*X 0 2+(534462751/1250000000 : ℝ)*X 1 0+(397958101/1000000000 : ℝ)*X 1 1+(918126883/2000000000 : ℝ)*X 1 2+(534462751/1250000000 : ℝ)*X 2 0+(397958101/1000000000 : ℝ)*X 2 1+(918126883/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-472966223/2500000000 : ℝ)*X 0 0+(2596437293/5000000000 : ℝ)*X 0 1+(1092499307/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1322126109/2500000000 : ℝ)*X 1 0+(-1761208107/10000000000 : ℝ)*X 1 1+(5462497723/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5288505139/10000000000 : ℝ)*X 2 0+(5462495961/10000000000 : ℝ)*X 2 1+(-1761209597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4275832557/10000000000 : ℝ)*X 0 0+(1146684009/2500000000 : ℝ)*X 0 1+(796702667/2000000000 : ℝ)*X 0 2+(4275832557/10000000000 : ℝ)*X 1 0+(1146684009/2500000000 : ℝ)*X 1 1+(796702667/2000000000 : ℝ)*X 1 2+(4275832557/10000000000 : ℝ)*X 2 0+(1146684009/2500000000 : ℝ)*X 2 1+(796702667/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (645662718887349111963450507/130625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (555303353/25000000000000 : ℝ)*(base19) + (2117795803/100000000000000 : ℝ)*(base23) + (8628251/20000000000000 : ℝ)*(upper2) + (338980661/100000000000000 : ℝ)*(upper3) + (64115153/50000000000000 : ℝ)*(upper4) + (264895389038739/10000000000000 : ℝ)*(major0) + (264895389038739/10000000000000 : ℝ)*(major1) + (264895389038739/10000000000000 : ℝ)*(major2) + (3661345145589121/100000000000000 : ℝ)*(sp0) + (1830682144945107/50000000000000 : ℝ)*(sp1) + (228835274581739/6250000000000 : ℝ)*(sp2) + (818263920208949/50000000000000 : ℝ)*(sp3) + (10682757253/50000000000000 : ℝ)*(sp4) + (6632245417/50000000000000 : ℝ)*(sp7) + (409135276227183/25000000000000 : ℝ)*(f.failure) + (1830683255551813/50000000000000 : ℝ)*(f.sum) + (3002048827773/5225000000000000000000000000 : ℝ)*base65 + (1746291949903374831/261250000000000000000000000000000 : ℝ)*base68 + (3183903708865874831/261250000000000000000000000000000 : ℝ)*base70 + (603057971531625169/261250000000000000000000000000000 : ℝ)*base71 + (1197073971349/2612500000000000000000000000 : ℝ)*base73 + (758819057260874831/261250000000000000000000000000000 : ℝ)*base76 + (418595573686625169/261250000000000000000000000000000 : ℝ)*base77 + (1535186528315874831/261250000000000000000000000000000 : ℝ)*base80 + (6562502147699/2612500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (931137/2500000000000000000000 : ℝ)*base90 + (931137/2500000000000000000000 : ℝ)*base92 + (931137/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14047025670831453207819/1632812500000000000000000000 : ℝ) := by norm_num
    linear_combination (344394299/20000000000000 : ℝ)*(base23) + (12746043/50000000000000 : ℝ)*(lower2) + (30135841/12500000000000 : ℝ)*(upper3) + (168114479/25000000000000 : ℝ)*(lower4) + (335416500689119/12500000000000 : ℝ)*(major0) + (335416500689119/12500000000000 : ℝ)*(major1) + (335416500689119/12500000000000 : ℝ)*(major2) + (1470539161/20000000000000 : ℝ)*(sp1) + (121365737/1562500000000 : ℝ)*(sp2) + (556036683/6250000000000 : ℝ)*(sp3) + (1854441797060633/50000000000000 : ℝ)*(sp4) + (1854438120712731/50000000000000 : ℝ)*(sp5) + (927218526185651/25000000000000 : ℝ)*(sp6) + (828885616776133/50000000000000 : ℝ)*(sp7) + (828890065069597/50000000000000 : ℝ)*(f.failure) + (1854441797060633/50000000000000 : ℝ)*(f.sum) + (42728532494691/13062500000000000000000000000 : ℝ)*base65 + (74501777726073851/326562500000000000000000000000000 : ℝ)*base68 + (4040784374036426149/326562500000000000000000000000000 : ℝ)*base69 + (656583652486426149/326562500000000000000000000000000 : ℝ)*base71 + (1114388583533/6531250000000000000000000000 : ℝ)*base73 + (496167864360448851/326562500000000000000000000000000 : ℝ)*base76 + (2365926199108301149/326562500000000000000000000000000 : ℝ)*base77 + (6615047687563573851/326562500000000000000000000000000 : ℝ)*base80 + (15704846410309/13062500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (41496717/5000000000000000000000 : ℝ)*base89 + (41496717/5000000000000000000000 : ℝ)*base91 + (41496717/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1493_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161862961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1159/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4047/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5147/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16073/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1493_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1493_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161862961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5147/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16073/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1493_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1493_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1493_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161862961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5147/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16073/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1493_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
