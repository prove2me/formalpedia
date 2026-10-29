-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1347_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:06:37.875915+00:00
-- url     : https://prove2.me/submissions/c2062ed2-1b1e-4a70-8049-3600fc32861b

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
theorem support_rectangle_w1347_box_0 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1872809869/10000000000 : ℝ)*x 0 + (336858041/625000000 : ℝ)*x 1 + (538972907/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1872809869/10000000000 : ℝ)^4307 ≤ (5553251181311/50000000000000 : ℝ)^3283 := by
    have hnat : (1872809869 : ℕ)^4307*50000000000000^3283 ≤ 5553251181311^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872809869 10000000000 5553251181311 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336858041/625000000 : ℝ)^4307 ≤ (8889349314987/20000000000000 : ℝ)^3283 := by
    have hnat : (336858041 : ℕ)^4307*20000000000000^3283 ≤ 8889349314987^3283*625000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336858041 625000000 8889349314987 20000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538972907/1000000000 : ℝ)^4307 ≤ (44446751053897/100000000000000 : ℝ)^3283 := by
    have hnat : (538972907 : ℕ)^4307*100000000000000^3283 ≤ 44446751053897^3283*1000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538972907 1000000000 44446751053897 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1872809869/10000000000 : ℝ), (336858041/625000000 : ℝ), (538972907/1000000000 : ℝ)] ![(5553251181311/50000000000000 : ℝ), (8889349314987/20000000000000 : ℝ), (44446751053897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1872809869/10000000000 : ℝ)|^4307 ≤ (5553251181311/50000000000000 : ℝ)^3283
        have hw : |(-1872809869/10000000000 : ℝ)|=(1872809869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336858041/625000000 : ℝ)|^4307 ≤ (8889349314987/20000000000000 : ℝ)^3283
        have hw : |(336858041/625000000 : ℝ)|=(336858041/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538972907/1000000000 : ℝ)|^4307 ≤ (44446751053897/100000000000000 : ℝ)^3283
        have hw : |(538972907/1000000000 : ℝ)|=(538972907/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_box_1 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285233263/10000000000 : ℝ)*x 0 + (-100799807/500000000 : ℝ)*x 1 + (538972989/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285233263/10000000000 : ℝ)^4307 ≤ (21659835334779/50000000000000 : ℝ)^3283 := by
    have hnat : (5285233263 : ℕ)^4307*50000000000000^3283 ≤ 21659835334779^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285233263 10000000000 21659835334779 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100799807/500000000 : ℝ)^4307 ≤ (3058392347451/25000000000000 : ℝ)^3283 := by
    have hnat : (100799807 : ℕ)^4307*25000000000000^3283 ≤ 3058392347451^3283*500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100799807 500000000 3058392347451 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538972989/1000000000 : ℝ)^4307 ≤ (5555844990659/12500000000000 : ℝ)^3283 := by
    have hnat : (538972989 : ℕ)^4307*12500000000000^3283 ≤ 5555844990659^3283*1000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538972989 1000000000 5555844990659 12500000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285233263/10000000000 : ℝ), (-100799807/500000000 : ℝ), (538972989/1000000000 : ℝ)] ![(21659835334779/50000000000000 : ℝ), (3058392347451/25000000000000 : ℝ), (5555844990659/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285233263/10000000000 : ℝ)|^4307 ≤ (21659835334779/50000000000000 : ℝ)^3283
        have hw : |(5285233263/10000000000 : ℝ)|=(5285233263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-100799807/500000000 : ℝ)|^4307 ≤ (3058392347451/25000000000000 : ℝ)^3283
        have hw : |(-100799807/500000000 : ℝ)|=(100799807/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538972989/1000000000 : ℝ)|^4307 ≤ (5555844990659/12500000000000 : ℝ)^3283
        have hw : |(538972989/1000000000 : ℝ)|=(538972989/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_box_2 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285233879/10000000000 : ℝ)*x 0 + (1077945807/2000000000 : ℝ)*x 1 + (-2015996469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285233879/10000000000 : ℝ)^4307 ≤ (8663935458667/20000000000000 : ℝ)^3283 := by
    have hnat : (5285233879 : ℕ)^4307*20000000000000^3283 ≤ 8663935458667^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285233879 10000000000 8663935458667 20000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077945807/2000000000 : ℝ)^4307 ≤ (44446750675241/100000000000000 : ℝ)^3283 := by
    have hnat : (1077945807 : ℕ)^4307*100000000000000^3283 ≤ 44446750675241^3283*2000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077945807 2000000000 44446750675241 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015996469/10000000000 : ℝ)^4307 ≤ (3058393002243/25000000000000 : ℝ)^3283 := by
    have hnat : (2015996469 : ℕ)^4307*25000000000000^3283 ≤ 3058393002243^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015996469 10000000000 3058393002243 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285233879/10000000000 : ℝ), (1077945807/2000000000 : ℝ), (-2015996469/10000000000 : ℝ)] ![(8663935458667/20000000000000 : ℝ), (44446750675241/100000000000000 : ℝ), (3058393002243/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285233879/10000000000 : ℝ)|^4307 ≤ (8663935458667/20000000000000 : ℝ)^3283
        have hw : |(5285233879/10000000000 : ℝ)|=(5285233879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1077945807/2000000000 : ℝ)|^4307 ≤ (44446750675241/100000000000000 : ℝ)^3283
        have hw : |(1077945807/2000000000 : ℝ)|=(1077945807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2015996469/10000000000 : ℝ)|^4307 ≤ (3058393002243/25000000000000 : ℝ)^3283
        have hw : |(-2015996469/10000000000 : ℝ)|=(2015996469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_box_3 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2236691491/5000000000 : ℝ)*x 0 + (2127580699/5000000000 : ℝ)*x 1 + (4255160931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2236691491/5000000000 : ℝ)^4307 ≤ (8701738869513/25000000000000 : ℝ)^3283 := by
    have hnat : (2236691491 : ℕ)^4307*25000000000000^3283 ≤ 8701738869513^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236691491 5000000000 8701738869513 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2127580699/5000000000 : ℝ)^4307 ≤ (4074565575433/12500000000000 : ℝ)^3283 := by
    have hnat : (2127580699 : ℕ)^4307*12500000000000^3283 ≤ 4074565575433^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127580699 5000000000 4074565575433 12500000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4255160931/10000000000 : ℝ)^4307 ≤ (8149129977547/25000000000000 : ℝ)^3283 := by
    have hnat : (4255160931 : ℕ)^4307*25000000000000^3283 ≤ 8149129977547^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4255160931 10000000000 8149129977547 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2236691491/5000000000 : ℝ), (2127580699/5000000000 : ℝ), (4255160931/10000000000 : ℝ)] ![(8701738869513/25000000000000 : ℝ), (4074565575433/12500000000000 : ℝ), (8149129977547/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2236691491/5000000000 : ℝ)|^4307 ≤ (8701738869513/25000000000000 : ℝ)^3283
        have hw : |(2236691491/5000000000 : ℝ)|=(2236691491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2127580699/5000000000 : ℝ)|^4307 ≤ (4074565575433/12500000000000 : ℝ)^3283
        have hw : |(2127580699/5000000000 : ℝ)|=(2127580699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4255160931/10000000000 : ℝ)|^4307 ≤ (8149129977547/25000000000000 : ℝ)^3283
        have hw : |(4255160931/10000000000 : ℝ)|=(4255160931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_box_4 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-552316163/2500000000 : ℝ)*x 0 + (2632519449/5000000000 : ℝ)*x 1 + (1053007743/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (552316163/2500000000 : ℝ)^4307 ≤ (13794696935409/100000000000000 : ℝ)^3283 := by
    have hnat : (552316163 : ℕ)^4307*100000000000000^3283 ≤ 13794696935409^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552316163 2500000000 13794696935409 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632519449/5000000000 : ℝ)^4307 ≤ (4310265250717/10000000000000 : ℝ)^3283 := by
    have hnat : (2632519449 : ℕ)^4307*10000000000000^3283 ≤ 4310265250717^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632519449 5000000000 4310265250717 10000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053007743/2000000000 : ℝ)^4307 ≤ (2155132527087/5000000000000 : ℝ)^3283 := by
    have hnat : (1053007743 : ℕ)^4307*5000000000000^3283 ≤ 2155132527087^3283*2000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053007743 2000000000 2155132527087 5000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-552316163/2500000000 : ℝ), (2632519449/5000000000 : ℝ), (1053007743/2000000000 : ℝ)] ![(13794696935409/100000000000000 : ℝ), (4310265250717/10000000000000 : ℝ), (2155132527087/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-552316163/2500000000 : ℝ)|^4307 ≤ (13794696935409/100000000000000 : ℝ)^3283
        have hw : |(-552316163/2500000000 : ℝ)|=(552316163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632519449/5000000000 : ℝ)|^4307 ≤ (4310265250717/10000000000000 : ℝ)^3283
        have hw : |(2632519449/5000000000 : ℝ)|=(2632519449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053007743/2000000000 : ℝ)|^4307 ≤ (2155132527087/5000000000000 : ℝ)^3283
        have hw : |(1053007743/2000000000 : ℝ)|=(1053007743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_box_5 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5372795469/10000000000 : ℝ)*x 0 + (-2066065781/10000000000 : ℝ)*x 1 + (5265038721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372795469/10000000000 : ℝ)^4307 ≤ (22131820246173/50000000000000 : ℝ)^3283 := by
    have hnat : (5372795469 : ℕ)^4307*50000000000000^3283 ≤ 22131820246173^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372795469 10000000000 22131820246173 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2066065781/10000000000 : ℝ)^4307 ≤ (6316854445811/50000000000000 : ℝ)^3283 := by
    have hnat : (2066065781 : ℕ)^4307*50000000000000^3283 ≤ 6316854445811^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066065781 10000000000 6316854445811 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265038721/10000000000 : ℝ)^4307 ≤ (43102650606181/100000000000000 : ℝ)^3283 := by
    have hnat : (5265038721 : ℕ)^4307*100000000000000^3283 ≤ 43102650606181^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265038721 10000000000 43102650606181 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372795469/10000000000 : ℝ), (-2066065781/10000000000 : ℝ), (5265038721/10000000000 : ℝ)] ![(22131820246173/50000000000000 : ℝ), (6316854445811/50000000000000 : ℝ), (43102650606181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372795469/10000000000 : ℝ)|^4307 ≤ (22131820246173/50000000000000 : ℝ)^3283
        have hw : |(5372795469/10000000000 : ℝ)|=(5372795469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2066065781/10000000000 : ℝ)|^4307 ≤ (6316854445811/50000000000000 : ℝ)^3283
        have hw : |(-2066065781/10000000000 : ℝ)|=(2066065781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265038721/10000000000 : ℝ)|^4307 ≤ (43102650606181/100000000000000 : ℝ)^3283
        have hw : |(5265038721/10000000000 : ℝ)|=(5265038721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_box_6 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1343198819/2500000000 : ℝ)*x 0 + (2632519423/5000000000 : ℝ)*x 1 + (-2066065873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343198819/2500000000 : ℝ)^4307 ≤ (5532954800797/12500000000000 : ℝ)^3283 := by
    have hnat : (1343198819 : ℕ)^4307*12500000000000^3283 ≤ 5532954800797^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343198819 2500000000 5532954800797 12500000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632519423/5000000000 : ℝ)^4307 ≤ (43102651948687/100000000000000 : ℝ)^3283 := by
    have hnat : (2632519423 : ℕ)^4307*100000000000000^3283 ≤ 43102651948687^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632519423 5000000000 43102651948687 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2066065873/10000000000 : ℝ)^4307 ≤ (631685481483/5000000000000 : ℝ)^3283 := by
    have hnat : (2066065873 : ℕ)^4307*5000000000000^3283 ≤ 631685481483^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066065873 10000000000 631685481483 5000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343198819/2500000000 : ℝ), (2632519423/5000000000 : ℝ), (-2066065873/10000000000 : ℝ)] ![(5532954800797/12500000000000 : ℝ), (43102651948687/100000000000000 : ℝ), (631685481483/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343198819/2500000000 : ℝ)|^4307 ≤ (5532954800797/12500000000000 : ℝ)^3283
        have hw : |(1343198819/2500000000 : ℝ)|=(1343198819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632519423/5000000000 : ℝ)|^4307 ≤ (43102651948687/100000000000000 : ℝ)^3283
        have hw : |(2632519423/5000000000 : ℝ)|=(2632519423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2066065873/10000000000 : ℝ)|^4307 ≤ (631685481483/5000000000000 : ℝ)^3283
        have hw : |(-2066065873/10000000000 : ℝ)|=(2066065873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_box_7 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4176316873/10000000000 : ℝ)*x 0 + (4403640667/10000000000 : ℝ)*x 1 + (1100910231/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4176316873/10000000000 : ℝ)^4307 ≤ (31806449098903/100000000000000 : ℝ)^3283 := by
    have hnat : (4176316873 : ℕ)^4307*100000000000000^3283 ≤ 31806449098903^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4176316873 10000000000 31806449098903 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4403640667/10000000000 : ℝ)^4307 ≤ (532762095889/1562500000000 : ℝ)^3283 := by
    have hnat : (4403640667 : ℕ)^4307*1562500000000^3283 ≤ 532762095889^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4403640667 10000000000 532762095889 1562500000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1100910231/2500000000 : ℝ)^4307 ≤ (6819355349497/20000000000000 : ℝ)^3283 := by
    have hnat : (1100910231 : ℕ)^4307*20000000000000^3283 ≤ 6819355349497^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100910231 2500000000 6819355349497 20000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4176316873/10000000000 : ℝ), (4403640667/10000000000 : ℝ), (1100910231/2500000000 : ℝ)] ![(31806449098903/100000000000000 : ℝ), (532762095889/1562500000000 : ℝ), (6819355349497/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4176316873/10000000000 : ℝ)|^4307 ≤ (31806449098903/100000000000000 : ℝ)^3283
        have hw : |(4176316873/10000000000 : ℝ)|=(4176316873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4403640667/10000000000 : ℝ)|^4307 ≤ (532762095889/1562500000000 : ℝ)^3283
        have hw : |(4403640667/10000000000 : ℝ)|=(4403640667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1100910231/2500000000 : ℝ)|^4307 ≤ (6819355349497/20000000000000 : ℝ)^3283
        have hw : |(1100910231/2500000000 : ℝ)|=(1100910231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_box_8 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2138596509/10000000000 : ℝ)*x 0 + (1294793669/2500000000 : ℝ)*x 1 + (2701872989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138596509/10000000000 : ℝ)^4307 ≤ (3304680372769/25000000000000 : ℝ)^3283 := by
    have hnat : (2138596509 : ℕ)^4307*25000000000000^3283 ≤ 3304680372769^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138596509 10000000000 3304680372769 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294793669/2500000000 : ℝ)^4307 ≤ (10545705138943/25000000000000 : ℝ)^3283 := by
    have hnat : (1294793669 : ℕ)^4307*25000000000000^3283 ≤ 10545705138943^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294793669 2500000000 10545705138943 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701872989/5000000000 : ℝ)^4307 ≤ (22299228971277/50000000000000 : ℝ)^3283 := by
    have hnat : (2701872989 : ℕ)^4307*50000000000000^3283 ≤ 22299228971277^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701872989 5000000000 22299228971277 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2138596509/10000000000 : ℝ), (1294793669/2500000000 : ℝ), (2701872989/5000000000 : ℝ)] ![(3304680372769/25000000000000 : ℝ), (10545705138943/25000000000000 : ℝ), (22299228971277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2138596509/10000000000 : ℝ)|^4307 ≤ (3304680372769/25000000000000 : ℝ)^3283
        have hw : |(-2138596509/10000000000 : ℝ)|=(2138596509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1294793669/2500000000 : ℝ)|^4307 ≤ (10545705138943/25000000000000 : ℝ)^3283
        have hw : |(1294793669/2500000000 : ℝ)|=(1294793669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701872989/5000000000 : ℝ)|^4307 ≤ (22299228971277/50000000000000 : ℝ)^3283
        have hw : |(2701872989/5000000000 : ℝ)|=(2701872989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_box_9 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275385439/10000000000 : ℝ)*x 0 + (-1005117987/5000000000 : ℝ)*x 1 + (1350936493/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275385439/10000000000 : ℝ)^4307 ≤ (10803452235213/25000000000000 : ℝ)^3283 := by
    have hnat : (5275385439 : ℕ)^4307*25000000000000^3283 ≤ 10803452235213^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275385439 10000000000 10803452235213 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005117987/5000000000 : ℝ)^4307 ≤ (6093866585157/50000000000000 : ℝ)^3283 := by
    have hnat : (1005117987 : ℕ)^4307*50000000000000^3283 ≤ 6093866585157^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005117987 5000000000 6093866585157 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350936493/2500000000 : ℝ)^4307 ≤ (44598457877589/100000000000000 : ℝ)^3283 := by
    have hnat : (1350936493 : ℕ)^4307*100000000000000^3283 ≤ 44598457877589^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350936493 2500000000 44598457877589 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275385439/10000000000 : ℝ), (-1005117987/5000000000 : ℝ), (1350936493/2500000000 : ℝ)] ![(10803452235213/25000000000000 : ℝ), (6093866585157/50000000000000 : ℝ), (44598457877589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275385439/10000000000 : ℝ)|^4307 ≤ (10803452235213/25000000000000 : ℝ)^3283
        have hw : |(5275385439/10000000000 : ℝ)|=(5275385439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1005117987/5000000000 : ℝ)|^4307 ≤ (6093866585157/50000000000000 : ℝ)^3283
        have hw : |(-1005117987/5000000000 : ℝ)|=(1005117987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350936493/2500000000 : ℝ)|^4307 ≤ (44598457877589/100000000000000 : ℝ)^3283
        have hw : |(1350936493/2500000000 : ℝ)|=(1350936493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_box_10 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055077121/2000000000 : ℝ)*x 0 + (5403745949/10000000000 : ℝ)*x 1 + (-2010235781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055077121/2000000000 : ℝ)^4307 ≤ (5401726340599/12500000000000 : ℝ)^3283 := by
    have hnat : (1055077121 : ℕ)^4307*12500000000000^3283 ≤ 5401726340599^3283*2000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055077121 2000000000 5401726340599 12500000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403745949/10000000000 : ℝ)^4307 ≤ (11149614407139/25000000000000 : ℝ)^3283 := by
    have hnat : (5403745949 : ℕ)^4307*25000000000000^3283 ≤ 11149614407139^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403745949 10000000000 11149614407139 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2010235781/10000000000 : ℝ)^4307 ≤ (3046932908803/25000000000000 : ℝ)^3283 := by
    have hnat : (2010235781 : ℕ)^4307*25000000000000^3283 ≤ 3046932908803^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010235781 10000000000 3046932908803 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055077121/2000000000 : ℝ), (5403745949/10000000000 : ℝ), (-2010235781/10000000000 : ℝ)] ![(5401726340599/12500000000000 : ℝ), (11149614407139/25000000000000 : ℝ), (3046932908803/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055077121/2000000000 : ℝ)|^4307 ≤ (5401726340599/12500000000000 : ℝ)^3283
        have hw : |(1055077121/2000000000 : ℝ)|=(1055077121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403745949/10000000000 : ℝ)|^4307 ≤ (11149614407139/25000000000000 : ℝ)^3283
        have hw : |(5403745949/10000000000 : ℝ)|=(5403745949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2010235781/10000000000 : ℝ)|^4307 ≤ (3046932908803/25000000000000 : ℝ)^3283
        have hw : |(-2010235781/10000000000 : ℝ)|=(2010235781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_box_11 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4506218807/10000000000 : ℝ)*x 0 + (2119227977/5000000000 : ℝ)*x 1 + (4238455727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4506218807/10000000000 : ℝ)^4307 ≤ (35142521453299/100000000000000 : ℝ)^3283 := by
    have hnat : (4506218807 : ℕ)^4307*100000000000000^3283 ≤ 35142521453299^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506218807 10000000000 35142521453299 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2119227977/5000000000 : ℝ)^4307 ≤ (16214370204471/50000000000000 : ℝ)^3283 := by
    have hnat : (2119227977 : ℕ)^4307*50000000000000^3283 ≤ 16214370204471^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119227977 5000000000 16214370204471 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4238455727/10000000000 : ℝ)^4307 ≤ (1297149525217/4000000000000 : ℝ)^3283 := by
    have hnat : (4238455727 : ℕ)^4307*4000000000000^3283 ≤ 1297149525217^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238455727 10000000000 1297149525217 4000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4506218807/10000000000 : ℝ), (2119227977/5000000000 : ℝ), (4238455727/10000000000 : ℝ)] ![(35142521453299/100000000000000 : ℝ), (16214370204471/50000000000000 : ℝ), (1297149525217/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4506218807/10000000000 : ℝ)|^4307 ≤ (35142521453299/100000000000000 : ℝ)^3283
        have hw : |(4506218807/10000000000 : ℝ)|=(4506218807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2119227977/5000000000 : ℝ)|^4307 ≤ (16214370204471/50000000000000 : ℝ)^3283
        have hw : |(2119227977/5000000000 : ℝ)|=(2119227977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4238455727/10000000000 : ℝ)|^4307 ≤ (1297149525217/4000000000000 : ℝ)^3283
        have hw : |(4238455727/10000000000 : ℝ)|=(4238455727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_box_12 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-485951549/2500000000 : ℝ)*x 0 + (2736699433/5000000000 : ℝ)*x 1 + (2626982669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (485951549/2500000000 : ℝ)^4307 ≤ (11662101646237/100000000000000 : ℝ)^3283 := by
    have hnat : (485951549 : ℕ)^4307*100000000000000^3283 ≤ 11662101646237^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485951549 2500000000 11662101646237 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2736699433/5000000000 : ℝ)^4307 ≤ (45354137411567/100000000000000 : ℝ)^3283 := by
    have hnat : (2736699433 : ℕ)^4307*100000000000000^3283 ≤ 45354137411567^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736699433 5000000000 45354137411567 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626982669/5000000000 : ℝ)^4307 ≤ (42983760921069/100000000000000 : ℝ)^3283 := by
    have hnat : (2626982669 : ℕ)^4307*100000000000000^3283 ≤ 42983760921069^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626982669 5000000000 42983760921069 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-485951549/2500000000 : ℝ), (2736699433/5000000000 : ℝ), (2626982669/5000000000 : ℝ)] ![(11662101646237/100000000000000 : ℝ), (45354137411567/100000000000000 : ℝ), (42983760921069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-485951549/2500000000 : ℝ)|^4307 ≤ (11662101646237/100000000000000 : ℝ)^3283
        have hw : |(-485951549/2500000000 : ℝ)|=(485951549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2736699433/5000000000 : ℝ)|^4307 ≤ (45354137411567/100000000000000 : ℝ)^3283
        have hw : |(2736699433/5000000000 : ℝ)|=(2736699433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626982669/5000000000 : ℝ)|^4307 ≤ (42983760921069/100000000000000 : ℝ)^3283
        have hw : |(2626982669/5000000000 : ℝ)|=(2626982669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_box_13 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538056941/1000000000 : ℝ)*x 0 + (-2070408479/10000000000 : ℝ)*x 1 + (5253965313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538056941/1000000000 : ℝ)^4307 ≤ (44347681259283/100000000000000 : ℝ)^3283 := by
    have hnat : (538056941 : ℕ)^4307*100000000000000^3283 ≤ 44347681259283^3283*1000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538056941 1000000000 44347681259283 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2070408479/10000000000 : ℝ)^4307 ≤ (12668558075359/100000000000000 : ℝ)^3283 := by
    have hnat : (2070408479 : ℕ)^4307*100000000000000^3283 ≤ 12668558075359^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070408479 10000000000 12668558075359 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253965313/10000000000 : ℝ)^4307 ≤ (5372970081593/12500000000000 : ℝ)^3283 := by
    have hnat : (5253965313 : ℕ)^4307*12500000000000^3283 ≤ 5372970081593^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253965313 10000000000 5372970081593 12500000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538056941/1000000000 : ℝ), (-2070408479/10000000000 : ℝ), (5253965313/10000000000 : ℝ)] ![(44347681259283/100000000000000 : ℝ), (12668558075359/100000000000000 : ℝ), (5372970081593/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538056941/1000000000 : ℝ)|^4307 ≤ (44347681259283/100000000000000 : ℝ)^3283
        have hw : |(538056941/1000000000 : ℝ)|=(538056941/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2070408479/10000000000 : ℝ)|^4307 ≤ (12668558075359/100000000000000 : ℝ)^3283
        have hw : |(-2070408479/10000000000 : ℝ)|=(2070408479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253965313/10000000000 : ℝ)|^4307 ≤ (5372970081593/12500000000000 : ℝ)^3283
        have hw : |(5253965313/10000000000 : ℝ)|=(5253965313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_box_14 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380570321/10000000000 : ℝ)*x 0 + (5253964697/10000000000 : ℝ)*x 1 + (-82816323/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380570321/10000000000 : ℝ)^4307 ≤ (44347691109937/100000000000000 : ℝ)^3283 := by
    have hnat : (5380570321 : ℕ)^4307*100000000000000^3283 ≤ 44347691109937^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380570321 10000000000 44347691109937 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253964697/10000000000 : ℝ)^4307 ≤ (8596750808243/20000000000000 : ℝ)^3283 := by
    have hnat : (5253964697 : ℕ)^4307*20000000000000^3283 ≤ 8596750808243^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253964697 10000000000 8596750808243 20000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82816323/400000000 : ℝ)^4307 ≤ (12668554832287/100000000000000 : ℝ)^3283 := by
    have hnat : (82816323 : ℕ)^4307*100000000000000^3283 ≤ 12668554832287^3283*400000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82816323 400000000 12668554832287 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380570321/10000000000 : ℝ), (5253964697/10000000000 : ℝ), (-82816323/400000000 : ℝ)] ![(44347691109937/100000000000000 : ℝ), (8596750808243/20000000000000 : ℝ), (12668554832287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380570321/10000000000 : ℝ)|^4307 ≤ (44347691109937/100000000000000 : ℝ)^3283
        have hw : |(5380570321/10000000000 : ℝ)|=(5380570321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253964697/10000000000 : ℝ)|^4307 ≤ (8596750808243/20000000000000 : ℝ)^3283
        have hw : |(5253964697/10000000000 : ℝ)|=(5253964697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-82816323/400000000 : ℝ)|^4307 ≤ (12668554832287/100000000000000 : ℝ)^3283
        have hw : |(-82816323/400000000 : ℝ)|=(82816323/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_box_15 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2074744041/5000000000 : ℝ)*x 0 + (110420383/250000000 : ℝ)*x 1 + (138025513/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2074744041/5000000000 : ℝ)^4307 ≤ (31538661246877/100000000000000 : ℝ)^3283 := by
    have hnat : (2074744041 : ℕ)^4307*100000000000000^3283 ≤ 31538661246877^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074744041 5000000000 31538661246877 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110420383/250000000 : ℝ)^4307 ≤ (3423066379749/10000000000000 : ℝ)^3283 := by
    have hnat : (110420383 : ℕ)^4307*10000000000000^3283 ≤ 3423066379749^3283*250000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110420383 250000000 3423066379749 10000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (138025513/312500000 : ℝ)^4307 ≤ (6846134988193/20000000000000 : ℝ)^3283 := by
    have hnat : (138025513 : ℕ)^4307*20000000000000^3283 ≤ 6846134988193^3283*312500000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138025513 312500000 6846134988193 20000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2074744041/5000000000 : ℝ), (110420383/250000000 : ℝ), (138025513/312500000 : ℝ)] ![(31538661246877/100000000000000 : ℝ), (3423066379749/10000000000000 : ℝ), (6846134988193/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2074744041/5000000000 : ℝ)|^4307 ≤ (31538661246877/100000000000000 : ℝ)^3283
        have hw : |(2074744041/5000000000 : ℝ)|=(2074744041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(110420383/250000000 : ℝ)|^4307 ≤ (3423066379749/10000000000000 : ℝ)^3283
        have hw : |(110420383/250000000 : ℝ)|=(110420383/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(138025513/312500000 : ℝ)|^4307 ≤ (6846134988193/20000000000000 : ℝ)^3283
        have hw : |(138025513/312500000 : ℝ)|=(138025513/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1347_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5581/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62857/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58951/100000 : ℝ) ∧ (4999/6250 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84371/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14709/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5581/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14709/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5581/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14709/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5581/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14709/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5581/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14709/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5581/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14709/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5581/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5581/50000 : ℝ) ^ (2153/512 : ℝ) ≤ (9901039458291073/100000000000000000000 : ℝ) := by
    have hpowers : (5581/50000 : ℝ)^2153 ≤ (9901039458291073/100000000000000000000 : ℝ)^512 := by
      have hnat : (5581 : ℕ)^2153*100000000000000000000^512 ≤ 9901039458291073^512*50000^2153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5581 50000 9901039458291073 100000000000000000000 2153 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5581/50000 : ℝ)) (X := (9901039458291073/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14709/100000 : ℝ) ^ (2153/512 : ℝ) ≤ (31595272445475889/100000000000000000000 : ℝ) := by
    have hpowers : (14709/100000 : ℝ)^2153 ≤ (31595272445475889/100000000000000000000 : ℝ)^512 := by
      have hnat : (14709 : ℕ)^2153*100000000000000000000^512 ≤ 31595272445475889^512*100000^2153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14709 100000 31595272445475889 100000000000000000000 2153 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14709/100000 : ℝ)) (X := (31595272445475889/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009901039458291073/50000000000000000000 : ℝ) ≤ (10000470873171407/10000000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (50009901039458291073/50000000000000000000 : ℝ)^512 ≤ (10000470873171407/10000000000000000 : ℝ)^2153 := by
      have hnat : (50009901039458291073 : ℕ)^512*10000000000000000^2153 ≤ 10000470873171407^2153*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009901039458291073 50000000000000000000 10000470873171407 10000000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000470873171407/10000000000000000 : ℝ)) (X := (50009901039458291073/50000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020748155951883481/50000000000000000000 : ℝ) ≤ (10000986658273823/10000000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (50020748155951883481/50000000000000000000 : ℝ)^512 ≤ (10000986658273823/10000000000000000 : ℝ)^2153 := by
      have hnat : (50020748155951883481 : ℕ)^512*10000000000000000^2153 ≤ 10000986658273823^2153*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020748155951883481 50000000000000000000 10000986658273823 10000000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000986658273823/10000000000000000 : ℝ)) (X := (50020748155951883481/50000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031595272445475889/50000000000000000000 : ℝ) ≤ (10001502443376239/10000000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (50031595272445475889/50000000000000000000 : ℝ)^512 ≤ (10001502443376239/10000000000000000 : ℝ)^2153 := by
      have hnat : (50031595272445475889 : ℕ)^512*10000000000000000^2153 ≤ 10001502443376239^2153*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031595272445475889 50000000000000000000 10001502443376239 10000000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001502443376239/10000000000000000 : ℝ)) (X := (50031595272445475889/50000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9901039458291073/100000000000000000000 : ℝ) ≤ ((7092031160102529169/7094000000000000000 : ℝ)+2*(32236568901/22168750000000 : ℝ)*(5581/50000 : ℝ))^(2153/512 : ℝ) := by
    rw [show (7092031160102529169/7094000000000000000 : ℝ)+2*(32236568901/22168750000000 : ℝ)*(5581/50000 : ℝ)=(10000470873171407/10000000000000000 : ℝ) by norm_num, show 1+2*(9901039458291073/100000000000000000000 : ℝ)=(50009901039458291073/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31595272445475889/100000000000000000000 : ℝ)+(9901039458291073/100000000000000000000 : ℝ) ≤ ((7092031160102529169/7094000000000000000 : ℝ)+(32236568901/22168750000000 : ℝ)*((14709/100000 : ℝ)+(5581/50000 : ℝ)))^(2153/512 : ℝ) := by
    rw [show (7092031160102529169/7094000000000000000 : ℝ)+(32236568901/22168750000000 : ℝ)*((14709/100000 : ℝ)+(5581/50000 : ℝ))=(10000986658273823/10000000000000000 : ℝ) by norm_num, show 1+(31595272445475889/100000000000000000000 : ℝ)+(9901039458291073/100000000000000000000 : ℝ)=(50020748155951883481/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31595272445475889/100000000000000000000 : ℝ) ≤ ((7092031160102529169/7094000000000000000 : ℝ)+2*(32236568901/22168750000000 : ℝ)*(14709/100000 : ℝ))^(2153/512 : ℝ) := by
    rw [show (7092031160102529169/7094000000000000000 : ℝ)+2*(32236568901/22168750000000 : ℝ)*(14709/100000 : ℝ)=(10001502443376239/10000000000000000 : ℝ) by norm_num, show 1+2*(31595272445475889/100000000000000000000 : ℝ)=(50031595272445475889/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7092031160102529169/7094000000000000000 : ℝ)*(X 1 0+X 2 0)+(32236568901/22168750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (5581/50000 : ℝ)) (hi := (14709/100000 : ℝ)) (c := (7092031160102529169/7094000000000000000 : ℝ)) (alpha := (32236568901/22168750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7092031160102529169/7094000000000000000 : ℝ)*(X 0 1+X 2 1)+(32236568901/22168750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (5581/50000 : ℝ)) (hi := (14709/100000 : ℝ)) (c := (7092031160102529169/7094000000000000000 : ℝ)) (alpha := (32236568901/22168750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7092031160102529169/7094000000000000000 : ℝ)*(X 0 2+X 1 2)+(32236568901/22168750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (5581/50000 : ℝ)) (hi := (14709/100000 : ℝ)) (c := (7092031160102529169/7094000000000000000 : ℝ)) (alpha := (32236568901/22168750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1872809869/10000000000 : ℝ)*X 0 0+(336858041/625000000 : ℝ)*X 0 1+(538972907/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285233263/10000000000 : ℝ)*X 1 0+(-100799807/500000000 : ℝ)*X 1 1+(538972989/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285233879/10000000000 : ℝ)*X 2 0+(1077945807/2000000000 : ℝ)*X 2 1+(-2015996469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2236691491/5000000000 : ℝ)*X 0 0+(2127580699/5000000000 : ℝ)*X 0 1+(4255160931/10000000000 : ℝ)*X 0 2+(2236691491/5000000000 : ℝ)*X 1 0+(2127580699/5000000000 : ℝ)*X 1 1+(4255160931/10000000000 : ℝ)*X 1 2+(2236691491/5000000000 : ℝ)*X 2 0+(2127580699/5000000000 : ℝ)*X 2 1+(4255160931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-552316163/2500000000 : ℝ)*X 0 0+(2632519449/5000000000 : ℝ)*X 0 1+(1053007743/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5372795469/10000000000 : ℝ)*X 1 0+(-2066065781/10000000000 : ℝ)*X 1 1+(5265038721/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1343198819/2500000000 : ℝ)*X 2 0+(2632519423/5000000000 : ℝ)*X 2 1+(-2066065873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4176316873/10000000000 : ℝ)*X 0 0+(4403640667/10000000000 : ℝ)*X 0 1+(1100910231/2500000000 : ℝ)*X 0 2+(4176316873/10000000000 : ℝ)*X 1 0+(4403640667/10000000000 : ℝ)*X 1 1+(1100910231/2500000000 : ℝ)*X 1 2+(4176316873/10000000000 : ℝ)*X 2 0+(4403640667/10000000000 : ℝ)*X 2 1+(1100910231/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2138596509/10000000000 : ℝ)*X 0 0+(1294793669/2500000000 : ℝ)*X 0 1+(2701872989/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275385439/10000000000 : ℝ)*X 1 0+(-1005117987/5000000000 : ℝ)*X 1 1+(1350936493/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1055077121/2000000000 : ℝ)*X 2 0+(5403745949/10000000000 : ℝ)*X 2 1+(-2010235781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4506218807/10000000000 : ℝ)*X 0 0+(2119227977/5000000000 : ℝ)*X 0 1+(4238455727/10000000000 : ℝ)*X 0 2+(4506218807/10000000000 : ℝ)*X 1 0+(2119227977/5000000000 : ℝ)*X 1 1+(4238455727/10000000000 : ℝ)*X 1 2+(4506218807/10000000000 : ℝ)*X 2 0+(2119227977/5000000000 : ℝ)*X 2 1+(4238455727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-485951549/2500000000 : ℝ)*X 0 0+(2736699433/5000000000 : ℝ)*X 0 1+(2626982669/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((538056941/1000000000 : ℝ)*X 1 0+(-2070408479/10000000000 : ℝ)*X 1 1+(5253965313/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5380570321/10000000000 : ℝ)*X 2 0+(5253964697/10000000000 : ℝ)*X 2 1+(-82816323/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2074744041/5000000000 : ℝ)*X 0 0+(110420383/250000000 : ℝ)*X 0 1+(138025513/312500000 : ℝ)*X 0 2+(2074744041/5000000000 : ℝ)*X 1 0+(110420383/250000000 : ℝ)*X 1 1+(138025513/312500000 : ℝ)*X 1 2+(2074744041/5000000000 : ℝ)*X 2 0+(110420383/250000000 : ℝ)*X 2 1+(138025513/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62857/100000 : ℝ) ≤ (-13934105259141733103025484219749/22168750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21108417/100000000000000 : ℝ)*(upper0) + (8546729/50000000000000 : ℝ)*(upper2) + (878973/6250000000000 : ℝ)*(upper3) + (25671767/50000000000000 : ℝ)*(lower4) + (182896552073619/6250000000000 : ℝ)*(major0) + (182896552073619/6250000000000 : ℝ)*(major1) + (182896552073619/6250000000000 : ℝ)*(major2) + (936129219/100000000000000 : ℝ)*(sp1) + (127294507/12500000000000 : ℝ)*(sp3) + (3984771050184287/100000000000000 : ℝ)*(sp4) + (996192528513767/25000000000000 : ℝ)*(sp5) + (3984770700173327/100000000000000 : ℝ)*(sp6) + (472217292606441/25000000000000 : ℝ)*(sp7) + (4375137/1250000000000 : ℝ)*(sp14) + (94443509439091/5000000000000 : ℝ)*(f.failure) + (3984771050184287/100000000000000 : ℝ)*(f.sum) + (1898200360427/554218750000000000000000000 : ℝ)*base65 + (187758355686797611/44337500000000000000000000000000 : ℝ)*base67 + (132885437683985111/44337500000000000000000000000000 : ℝ)*base69 + (121469942430585111/44337500000000000000000000000000 : ℝ)*base71 + (1737117569829/4433750000000000000000000000 : ℝ)*base74 + (445319707884597611/44337500000000000000000000000000 : ℝ)*base75 + (219206511082072611/44337500000000000000000000000000 : ℝ)*base77 + (104947254490647611/44337500000000000000000000000000 : ℝ)*base79 + (49418731812671/17735000000000000000000000000 : ℝ)*base82 + (469481/62500000000000000000 : ℝ)*base90 + (469481/62500000000000000000 : ℝ)*base92 + (469481/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58951/100000 : ℝ) ≤ (522769841082339171064891420029/886750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48929647/100000000000000 : ℝ)*(lower0) + (18824037/50000000000000 : ℝ)*(upper1) + (496191/5000000000000 : ℝ)*(upper4) + (14976032511853/500000000000 : ℝ)*(major0) + (14976032511853/500000000000 : ℝ)*(major1) + (14976032511853/500000000000 : ℝ)*(major2) + (2018720013584473/50000000000000 : ℝ)*(sp0) + (4037410151490569/100000000000000 : ℝ)*(sp1) + (2018718710749443/50000000000000 : ℝ)*(sp2) + (7552022430601/390625000000 : ℝ)*(sp3) + (3331199919/10000000000000 : ℝ)*(sp5) + (6041990873/100000000000000 : ℝ)*(sp6) + (161096537/25000000000000 : ℝ)*(sp7) + (3436320813/100000000000000 : ℝ)*(sp12) + (483329596655001/25000000000000 : ℝ)*(f.failure) + (4037443463489759/100000000000000 : ℝ)*(f.sum) + (3568033284329/1773500000000000000000000000 : ℝ)*base66 + (16081770830914157/3547000000000000000000000000000 : ℝ)*base67 + (1857375562293843/3547000000000000000000000000000 : ℝ)*base70 + (17846422786209157/3547000000000000000000000000000 : ℝ)*base71 + (83949186934141/1773500000000000000000000000 : ℝ)*base73 + (7876999227564157/3547000000000000000000000000000 : ℝ)*base75 + (19037477063414157/3547000000000000000000000000000 : ℝ)*base77 + (247626763594016157/3547000000000000000000000000000 : ℝ)*base79 + (1143284228951/709400000000000000000000000 : ℝ)*base82 + (2239291/312500000000000000000 : ℝ)*base90 + (2239291/312500000000000000000 : ℝ)*base92 + (2239291/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (4999/6250 : ℝ) ≤ (141855505102109872352122887486477/177350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29257939/50000000000000 : ℝ)*(lower3) + (22725929/20000000000000 : ℝ)*(upper4) + (44261741/100000000000000 : ℝ)*(lower5) + (1653562742032289/50000000000000 : ℝ)*(major0) + (1653562742032289/50000000000000 : ℝ)*(major1) + (1653562742032289/50000000000000 : ℝ)*(major2) + (1796466209/50000000000000 : ℝ)*(sp0) + (43436030879/100000000000000 : ℝ)*(sp1) + (41878377441/50000000000000 : ℝ)*(sp2) + (46849800433/100000000000000 : ℝ)*(sp3) + (1113233081497739/25000000000000 : ℝ)*(sp8) + (890578496578499/20000000000000 : ℝ)*(sp9) + (4452852162168493/100000000000000 : ℝ)*(sp10) + (1067303068305047/50000000000000 : ℝ)*(sp11) + (66707905825329/3125000000000 : ℝ)*(f.failure) + (2226467959461687/50000000000000 : ℝ)*(f.sum) + (76537119675391/8867500000000000000000000000 : ℝ)*base66 + (4797194472539017841/354700000000000000000000000000000 : ℝ)*base67 + (1077820127878517841/354700000000000000000000000000000 : ℝ)*base69 + (485243405399382159/354700000000000000000000000000000 : ℝ)*base72 + (4082621926937/4433750000000000000000000000 : ℝ)*base73 + (2111704220235117841/354700000000000000000000000000000 : ℝ)*base75 + (1155797392436082159/354700000000000000000000000000000 : ℝ)*base78 + (643166829152917841/354700000000000000000000000000000 : ℝ)*base79 + (26871746810251/8867500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (462011/39062500000000000000 : ℝ)*base89 + (462011/39062500000000000000 : ℝ)*base91 + (462011/39062500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-84371/100000 : ℝ) ≤ (-74814192826262348771710768127307/88675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (92428459/50000000000000 : ℝ)*(lower0) + (620455907/100000000000000 : ℝ)*(lower1) + (194101221/50000000000000 : ℝ)*(lower2) + (1671836151018599/50000000000000 : ℝ)*(major0) + (1671836151018599/50000000000000 : ℝ)*(major1) + (1671836151018599/50000000000000 : ℝ)*(major2) + (1087022139/4000000000000 : ℝ)*(sp0) + (903781766531/100000000000000 : ℝ)*(sp5) + (469164707003/50000000000000 : ℝ)*(sp6) + (3804609769/2500000000000 : ℝ)*(sp7) + (2278598765468067/50000000000000 : ℝ)*(sp12) + (2278160462361539/50000000000000 : ℝ)*(sp13) + (2278143188537801/50000000000000 : ℝ)*(sp14) + (1079045353228203/50000000000000 : ℝ)*(sp15) + (1079121445423583/50000000000000 : ℝ)*(f.failure) + (4557224706489609/100000000000000 : ℝ)*(f.sum) + (55243259145613/17735000000000000000000000000 : ℝ)*base65 + (1916976835512105769/354700000000000000000000000000000 : ℝ)*base68 + (3888074599123905769/354700000000000000000000000000000 : ℝ)*base70 + (2178766117005005769/354700000000000000000000000000000 : ℝ)*base72 + (152014161897623/17735000000000000000000000000 : ℝ)*base73 + (2882393236172005769/354700000000000000000000000000000 : ℝ)*base76 + (162625651513694231/354700000000000000000000000000000 : ℝ)*base77 + (4184430645934305769/354700000000000000000000000000000 : ℝ)*base80 + (5362729734897/4433750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2615347/625000000000000000000 : ℝ)*base89 + (2615347/625000000000000000000 : ℝ)*base91 + (2615347/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1347_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5581/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62857/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58951/100000 : ℝ) else (4999/6250 : ℝ) ≤ X j i ∧ X j i ≤ (84371/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1347_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1347_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5581/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62857/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58951/100000 : ℝ) else (4999/6250 : ℝ) ≤ X j i ∧ X j i ≤ (84371/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1347_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5581/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62857/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58951/100000 : ℝ) else (4999/6250 : ℝ) ≤ X j i ∧ X j i ≤ (84371/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1347_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
