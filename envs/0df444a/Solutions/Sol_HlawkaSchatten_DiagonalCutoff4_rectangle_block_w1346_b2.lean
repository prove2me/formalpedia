-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1346_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:06:02.910835+00:00
-- url     : https://prove2.me/submissions/fdcd915f-35b6-4601-b083-27c8ba5dee7d

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
theorem support_rectangle_w1346_s6_0 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-25506429/125000000 : ℝ)*x 0 + (27062583/50000000 : ℝ)*x 1 + (5244718419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25506429/125000000 : ℝ)^2153 ≤ (6213625236601/50000000000000 : ℝ)^1641 := by
    have hnat : (25506429 : ℕ)^2153*50000000000000^1641 ≤ 6213625236601^1641*125000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25506429 125000000 6213625236601 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27062583/50000000 : ℝ)^2153 ≤ (22345419345369/50000000000000 : ℝ)^1641 := by
    have hnat : (27062583 : ℕ)^2153*50000000000000^1641 ≤ 22345419345369^1641*50000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27062583 50000000 22345419345369 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244718419/10000000000 : ℝ)^2153 ≤ (42881910814863/100000000000000 : ℝ)^1641 := by
    have hnat : (5244718419 : ℕ)^2153*100000000000000^1641 ≤ 42881910814863^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244718419 10000000000 42881910814863 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-25506429/125000000 : ℝ), (27062583/50000000 : ℝ), (5244718419/10000000000 : ℝ)] ![(6213625236601/50000000000000 : ℝ), (22345419345369/50000000000000 : ℝ), (42881910814863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-25506429/125000000 : ℝ)|^2153 ≤ (6213625236601/50000000000000 : ℝ)^1641
        have hw : |(-25506429/125000000 : ℝ)|=(25506429/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27062583/50000000 : ℝ)|^2153 ≤ (22345419345369/50000000000000 : ℝ)^1641
        have hw : |(27062583/50000000 : ℝ)|=(27062583/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244718419/10000000000 : ℝ)|^2153 ≤ (42881910814863/100000000000000 : ℝ)^1641
        have hw : |(5244718419/10000000000 : ℝ)|=(5244718419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s6_1 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337233431/2500000000 : ℝ)*x 0 + (-2126005749/10000000000 : ℝ)*x 1 + (1048943683/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337233431/2500000000 : ℝ)^2153 ≤ (8800660331769/20000000000000 : ℝ)^1641 := by
    have hnat : (1337233431 : ℕ)^2153*20000000000000^1641 ≤ 8800660331769^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337233431 2500000000 8800660331769 20000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126005749/10000000000 : ℝ)^2153 ≤ (1639348444743/12500000000000 : ℝ)^1641 := by
    have hnat : (2126005749 : ℕ)^2153*12500000000000^1641 ≤ 1639348444743^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126005749 10000000000 1639348444743 12500000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048943683/2000000000 : ℝ)^2153 ≤ (21440955385977/50000000000000 : ℝ)^1641 := by
    have hnat : (1048943683 : ℕ)^2153*50000000000000^1641 ≤ 21440955385977^1641*2000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048943683 2000000000 21440955385977 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337233431/2500000000 : ℝ), (-2126005749/10000000000 : ℝ), (1048943683/2000000000 : ℝ)] ![(8800660331769/20000000000000 : ℝ), (1639348444743/12500000000000 : ℝ), (21440955385977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337233431/2500000000 : ℝ)|^2153 ≤ (8800660331769/20000000000000 : ℝ)^1641
        have hw : |(1337233431/2500000000 : ℝ)|=(1337233431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2126005749/10000000000 : ℝ)|^2153 ≤ (1639348444743/12500000000000 : ℝ)^1641
        have hw : |(-2126005749/10000000000 : ℝ)|=(2126005749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048943683/2000000000 : ℝ)|^2153 ≤ (21440955385977/50000000000000 : ℝ)^1641
        have hw : |(1048943683/2000000000 : ℝ)|=(1048943683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s6_2 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348933703/10000000000 : ℝ)*x 0 + (2622359211/5000000000 : ℝ)*x 1 + (-2126005767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348933703/10000000000 : ℝ)^2153 ≤ (22001650716093/50000000000000 : ℝ)^1641 := by
    have hnat : (5348933703 : ℕ)^2153*50000000000000^1641 ≤ 22001650716093^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348933703 10000000000 22001650716093 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622359211/5000000000 : ℝ)^2153 ≤ (10720477711761/25000000000000 : ℝ)^1641 := by
    have hnat : (2622359211 : ℕ)^2153*25000000000000^1641 ≤ 10720477711761^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622359211 5000000000 10720477711761 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2126005767/10000000000 : ℝ)^2153 ≤ (104918301629/800000000000 : ℝ)^1641 := by
    have hnat : (2126005767 : ℕ)^2153*800000000000^1641 ≤ 104918301629^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126005767 10000000000 104918301629 800000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348933703/10000000000 : ℝ), (2622359211/5000000000 : ℝ), (-2126005767/10000000000 : ℝ)] ![(22001650716093/50000000000000 : ℝ), (10720477711761/25000000000000 : ℝ), (104918301629/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348933703/10000000000 : ℝ)|^2153 ≤ (22001650716093/50000000000000 : ℝ)^1641
        have hw : |(5348933703/10000000000 : ℝ)|=(5348933703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622359211/5000000000 : ℝ)|^2153 ≤ (10720477711761/25000000000000 : ℝ)^1641
        have hw : |(2622359211/5000000000 : ℝ)|=(2622359211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2126005767/10000000000 : ℝ)|^2153 ≤ (104918301629/800000000000 : ℝ)^1641
        have hw : |(-2126005767/10000000000 : ℝ)|=(2126005767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s6_3 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2162786443/5000000000 : ℝ)*x 0 + (4152916001/10000000000 : ℝ)*x 1 + (900982101/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162786443/5000000000 : ℝ)^2153 ≤ (33303315666749/100000000000000 : ℝ)^1641 := by
    have hnat : (2162786443 : ℕ)^2153*100000000000000^1641 ≤ 33303315666749^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162786443 5000000000 33303315666749 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4152916001/10000000000 : ℝ)^2153 ≤ (3946276226957/12500000000000 : ℝ)^1641 := by
    have hnat : (4152916001 : ℕ)^2153*12500000000000^1641 ≤ 3946276226957^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152916001 10000000000 3946276226957 12500000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900982101/2000000000 : ℝ)^2153 ≤ (35126474503443/100000000000000 : ℝ)^1641 := by
    have hnat : (900982101 : ℕ)^2153*100000000000000^1641 ≤ 35126474503443^1641*2000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900982101 2000000000 35126474503443 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162786443/5000000000 : ℝ), (4152916001/10000000000 : ℝ), (900982101/2000000000 : ℝ)] ![(33303315666749/100000000000000 : ℝ), (3946276226957/12500000000000 : ℝ), (35126474503443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162786443/5000000000 : ℝ)|^2153 ≤ (33303315666749/100000000000000 : ℝ)^1641
        have hw : |(2162786443/5000000000 : ℝ)|=(2162786443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4152916001/10000000000 : ℝ)|^2153 ≤ (3946276226957/12500000000000 : ℝ)^1641
        have hw : |(4152916001/10000000000 : ℝ)|=(4152916001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(900982101/2000000000 : ℝ)|^2153 ≤ (35126474503443/100000000000000 : ℝ)^1641
        have hw : |(900982101/2000000000 : ℝ)|=(900982101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s6_4 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-408105317/2000000000 : ℝ)*x 0 + (2622659671/5000000000 : ℝ)*x 1 + (1082382497/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (408105317/2000000000 : ℝ)^2153 ≤ (12427348476077/100000000000000 : ℝ)^1641 := by
    have hnat : (408105317 : ℕ)^2153*100000000000000^1641 ≤ 12427348476077^1641*2000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408105317 2000000000 12427348476077 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622659671/5000000000 : ℝ)^2153 ≤ (21444178583241/50000000000000 : ℝ)^1641 := by
    have hnat : (2622659671 : ℕ)^2153*50000000000000^1641 ≤ 21444178583241^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622659671 5000000000 21444178583241 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082382497/2000000000 : ℝ)^2153 ≤ (11171073584237/25000000000000 : ℝ)^1641 := by
    have hnat : (1082382497 : ℕ)^2153*25000000000000^1641 ≤ 11171073584237^1641*2000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082382497 2000000000 11171073584237 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-408105317/2000000000 : ℝ), (2622659671/5000000000 : ℝ), (1082382497/2000000000 : ℝ)] ![(12427348476077/100000000000000 : ℝ), (21444178583241/50000000000000 : ℝ), (11171073584237/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-408105317/2000000000 : ℝ)|^2153 ≤ (12427348476077/100000000000000 : ℝ)^1641
        have hw : |(-408105317/2000000000 : ℝ)|=(408105317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622659671/5000000000 : ℝ)|^2153 ≤ (21444178583241/50000000000000 : ℝ)^1641
        have hw : |(2622659671/5000000000 : ℝ)|=(2622659671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082382497/2000000000 : ℝ)|^2153 ≤ (11171073584237/25000000000000 : ℝ)^1641
        have hw : |(1082382497/2000000000 : ℝ)|=(1082382497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s6_5 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305692517/10000000000 : ℝ)*x 0 + (-39176233/200000000 : ℝ)*x 1 + (338244547/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305692517/10000000000 : ℝ)^2153 ≤ (1741487073351/4000000000000 : ℝ)^1641 := by
    have hnat : (5305692517 : ℕ)^2153*4000000000000^1641 ≤ 1741487073351^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305692517 10000000000 1741487073351 4000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (39176233/200000000 : ℝ)^2153 ≤ (11778525929951/100000000000000 : ℝ)^1641 := by
    have hnat : (39176233 : ℕ)^2153*100000000000000^1641 ≤ 11778525929951^1641*200000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39176233 200000000 11778525929951 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338244547/625000000 : ℝ)^2153 ≤ (22342148614649/50000000000000 : ℝ)^1641 := by
    have hnat : (338244547 : ℕ)^2153*50000000000000^1641 ≤ 22342148614649^1641*625000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338244547 625000000 22342148614649 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305692517/10000000000 : ℝ), (-39176233/200000000 : ℝ), (338244547/625000000 : ℝ)] ![(1741487073351/4000000000000 : ℝ), (11778525929951/100000000000000 : ℝ), (22342148614649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305692517/10000000000 : ℝ)|^2153 ≤ (1741487073351/4000000000000 : ℝ)^1641
        have hw : |(5305692517/10000000000 : ℝ)|=(5305692517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-39176233/200000000 : ℝ)|^2153 ≤ (11778525929951/100000000000000 : ℝ)^1641
        have hw : |(-39176233/200000000 : ℝ)|=(39176233/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338244547/625000000 : ℝ)|^2153 ≤ (22342148614649/50000000000000 : ℝ)^1641
        have hw : |(338244547/625000000 : ℝ)|=(338244547/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s6_6 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (212227711/400000000 : ℝ)*x 0 + (676489051/1250000000 : ℝ)*x 1 + (-1958811769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212227711/400000000 : ℝ)^2153 ≤ (21768589805699/50000000000000 : ℝ)^1641 := by
    have hnat : (212227711 : ℕ)^2153*50000000000000^1641 ≤ 21768589805699^1641*400000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212227711 400000000 21768589805699 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676489051/1250000000 : ℝ)^2153 ≤ (1787371740113/4000000000000 : ℝ)^1641 := by
    have hnat : (676489051 : ℕ)^2153*4000000000000^1641 ≤ 1787371740113^1641*1250000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676489051 1250000000 1787371740113 4000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1958811769/10000000000 : ℝ)^2153 ≤ (11778526868767/100000000000000 : ℝ)^1641 := by
    have hnat : (1958811769 : ℕ)^2153*100000000000000^1641 ≤ 11778526868767^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1958811769 10000000000 11778526868767 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212227711/400000000 : ℝ), (676489051/1250000000 : ℝ), (-1958811769/10000000000 : ℝ)] ![(21768589805699/50000000000000 : ℝ), (1787371740113/4000000000000 : ℝ), (11778526868767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212227711/400000000 : ℝ)|^2153 ≤ (21768589805699/50000000000000 : ℝ)^1641
        have hw : |(212227711/400000000 : ℝ)|=(212227711/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676489051/1250000000 : ℝ)|^2153 ≤ (1787371740113/4000000000000 : ℝ)^1641
        have hw : |(676489051/1250000000 : ℝ)|=(676489051/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1958811769/10000000000 : ℝ)|^2153 ≤ (11778526868767/100000000000000 : ℝ)^1641
        have hw : |(-1958811769/10000000000 : ℝ)|=(1958811769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s6_7 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4325598489/10000000000 : ℝ)*x 0 + (4503649451/10000000000 : ℝ)*x 1 + (1038545857/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325598489/10000000000 : ℝ)^2153 ≤ (16651787145887/50000000000000 : ℝ)^1641 := by
    have hnat : (4325598489 : ℕ)^2153*50000000000000^1641 ≤ 16651787145887^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325598489 10000000000 16651787145887 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4503649451/10000000000 : ℝ)^2153 ≤ (35113574240523/100000000000000 : ℝ)^1641 := by
    have hnat : (4503649451 : ℕ)^2153*100000000000000^1641 ≤ 35113574240523^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503649451 10000000000 35113574240523 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1038545857/2500000000 : ℝ)^2153 ≤ (6316570291021/20000000000000 : ℝ)^1641 := by
    have hnat : (1038545857 : ℕ)^2153*20000000000000^1641 ≤ 6316570291021^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038545857 2500000000 6316570291021 20000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325598489/10000000000 : ℝ), (4503649451/10000000000 : ℝ), (1038545857/2500000000 : ℝ)] ![(16651787145887/50000000000000 : ℝ), (35113574240523/100000000000000 : ℝ), (6316570291021/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325598489/10000000000 : ℝ)|^2153 ≤ (16651787145887/50000000000000 : ℝ)^1641
        have hw : |(4325598489/10000000000 : ℝ)|=(4325598489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4503649451/10000000000 : ℝ)|^2153 ≤ (35113574240523/100000000000000 : ℝ)^1641
        have hw : |(4503649451/10000000000 : ℝ)|=(4503649451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1038545857/2500000000 : ℝ)|^2153 ≤ (6316570291021/20000000000000 : ℝ)^1641
        have hw : |(1038545857/2500000000 : ℝ)|=(1038545857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1346_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9680391/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7359/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11151/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5579/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1471/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7359/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11151/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7359/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11151/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7359/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11151/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7359/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11151/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7359/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11151/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7359/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11151/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11151/100000 : ℝ) ^ (4305/1024 : ℝ) ≤ (9881218993530519/100000000000000000000 : ℝ) := by
    have hpowers : (11151/100000 : ℝ)^4305 ≤ (9881218993530519/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11151 : ℕ)^4305*100000000000000000000^1024 ≤ 9881218993530519^1024*100000^4305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11151 100000 9881218993530519 100000000000000000000 4305 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11151/100000 : ℝ)) (X := (9881218993530519/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7359/50000 : ℝ) ^ (4305/1024 : ℝ) ≤ (31735974164400367/100000000000000000000 : ℝ) := by
    have hpowers : (7359/50000 : ℝ)^4305 ≤ (31735974164400367/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7359 : ℕ)^4305*100000000000000000000^1024 ≤ 31735974164400367^1024*50000^4305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7359 50000 31735974164400367 100000000000000000000 4305 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7359/50000 : ℝ)) (X := (31735974164400367/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009881218993530519/50000000000000000000 : ℝ) ≤ (10000470039783479/10000000000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (50009881218993530519/50000000000000000000 : ℝ)^1024 ≤ (10000470039783479/10000000000000000 : ℝ)^4305 := by
      have hnat : (50009881218993530519 : ℕ)^1024*10000000000000000^4305 ≤ 10000470039783479^4305*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009881218993530519 50000000000000000000 10000470039783479 10000000000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000470039783479/10000000000000000 : ℝ)) (X := (50009881218993530519/50000000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020808596578965443/50000000000000000000 : ℝ) ≤ (10000989761880883/10000000000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (50020808596578965443/50000000000000000000 : ℝ)^1024 ≤ (10000989761880883/10000000000000000 : ℝ)^4305 := by
      have hnat : (50020808596578965443 : ℕ)^1024*10000000000000000^4305 ≤ 10000989761880883^4305*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020808596578965443 50000000000000000000 10000989761880883 10000000000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000989761880883/10000000000000000 : ℝ)) (X := (50020808596578965443/50000000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031735974164400367/50000000000000000000 : ℝ) ≤ (10001509483978287/10000000000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (50031735974164400367/50000000000000000000 : ℝ)^1024 ≤ (10001509483978287/10000000000000000 : ℝ)^4305 := by
      have hnat : (50031735974164400367 : ℕ)^1024*10000000000000000^4305 ≤ 10001509483978287^4305*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031735974164400367 50000000000000000000 10001509483978287 10000000000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001509483978287/10000000000000000 : ℝ)) (X := (50031735974164400367/50000000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9881218993530519/100000000000000000000 : ℝ) ≤ ((2377339052646091039/2378000000000000000 : ℝ)+2*(129930524351/89175000000000 : ℝ)*(11151/100000 : ℝ))^(4305/1024 : ℝ) := by
    rw [show (2377339052646091039/2378000000000000000 : ℝ)+2*(129930524351/89175000000000 : ℝ)*(11151/100000 : ℝ)=(10000470039783479/10000000000000000 : ℝ) by norm_num, show 1+2*(9881218993530519/100000000000000000000 : ℝ)=(50009881218993530519/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31735974164400367/100000000000000000000 : ℝ)+(9881218993530519/100000000000000000000 : ℝ) ≤ ((2377339052646091039/2378000000000000000 : ℝ)+(129930524351/89175000000000 : ℝ)*((7359/50000 : ℝ)+(11151/100000 : ℝ)))^(4305/1024 : ℝ) := by
    rw [show (2377339052646091039/2378000000000000000 : ℝ)+(129930524351/89175000000000 : ℝ)*((7359/50000 : ℝ)+(11151/100000 : ℝ))=(10000989761880883/10000000000000000 : ℝ) by norm_num, show 1+(31735974164400367/100000000000000000000 : ℝ)+(9881218993530519/100000000000000000000 : ℝ)=(50020808596578965443/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31735974164400367/100000000000000000000 : ℝ) ≤ ((2377339052646091039/2378000000000000000 : ℝ)+2*(129930524351/89175000000000 : ℝ)*(7359/50000 : ℝ))^(4305/1024 : ℝ) := by
    rw [show (2377339052646091039/2378000000000000000 : ℝ)+2*(129930524351/89175000000000 : ℝ)*(7359/50000 : ℝ)=(10001509483978287/10000000000000000 : ℝ) by norm_num, show 1+2*(31735974164400367/100000000000000000000 : ℝ)=(50031735974164400367/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2377339052646091039/2378000000000000000 : ℝ)*(X 1 0+X 2 0)+(129930524351/89175000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (11151/100000 : ℝ)) (hi := (7359/50000 : ℝ)) (c := (2377339052646091039/2378000000000000000 : ℝ)) (alpha := (129930524351/89175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2377339052646091039/2378000000000000000 : ℝ)*(X 0 1+X 2 1)+(129930524351/89175000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (11151/100000 : ℝ)) (hi := (7359/50000 : ℝ)) (c := (2377339052646091039/2378000000000000000 : ℝ)) (alpha := (129930524351/89175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2377339052646091039/2378000000000000000 : ℝ)*(X 0 2+X 1 2)+(129930524351/89175000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (11151/100000 : ℝ)) (hi := (7359/50000 : ℝ)) (c := (2377339052646091039/2378000000000000000 : ℝ)) (alpha := (129930524351/89175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-25506429/125000000 : ℝ)*X 0 0+(27062583/50000000 : ℝ)*X 0 1+(5244718419/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337233431/2500000000 : ℝ)*X 1 0+(-2126005749/10000000000 : ℝ)*X 1 1+(1048943683/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348933703/10000000000 : ℝ)*X 2 0+(2622359211/5000000000 : ℝ)*X 2 1+(-2126005767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2162786443/5000000000 : ℝ)*X 0 0+(4152916001/10000000000 : ℝ)*X 0 1+(900982101/2000000000 : ℝ)*X 0 2+(2162786443/5000000000 : ℝ)*X 1 0+(4152916001/10000000000 : ℝ)*X 1 1+(900982101/2000000000 : ℝ)*X 1 2+(2162786443/5000000000 : ℝ)*X 2 0+(4152916001/10000000000 : ℝ)*X 2 1+(900982101/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-408105317/2000000000 : ℝ)*X 0 0+(2622659671/5000000000 : ℝ)*X 0 1+(1082382497/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305692517/10000000000 : ℝ)*X 1 0+(-39176233/200000000 : ℝ)*X 1 1+(338244547/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212227711/400000000 : ℝ)*X 2 0+(676489051/1250000000 : ℝ)*X 2 1+(-1958811769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4325598489/10000000000 : ℝ)*X 0 0+(4503649451/10000000000 : ℝ)*X 0 1+(1038545857/2500000000 : ℝ)*X 0 2+(4325598489/10000000000 : ℝ)*X 1 0+(4503649451/10000000000 : ℝ)*X 1 1+(1038545857/2500000000 : ℝ)*X 1 2+(4325598489/10000000000 : ℝ)*X 2 0+(4503649451/10000000000 : ℝ)*X 2 1+(1038545857/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (895333830736280362413619/164000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (201808029/20000000000000 : ℝ)*(base19) + (91694007/10000000000000 : ℝ)*(base23) + (36748597/100000000000000 : ℝ)*(lower2) + (138187109/100000000000000 : ℝ)*(upper3) + (60990971/100000000000000 : ℝ)*(upper5) + (176011145323601/4000000000000 : ℝ)*(major0) + (176011145323601/4000000000000 : ℝ)*(major1) + (176011145323601/4000000000000 : ℝ)*(major2) + (2979781276901483/50000000000000 : ℝ)*(sp0) + (744947729489643/12500000000000 : ℝ)*(sp1) + (5959581928017219/100000000000000 : ℝ)*(sp2) + (2840963137973617/100000000000000 : ℝ)*(sp3) + (5072788581/25000000000000 : ℝ)*(sp4) + (11101270713/100000000000000 : ℝ)*(sp7) + (284097423924433/10000000000000 : ℝ)*(f.failure) + (5959582844957289/100000000000000 : ℝ)*(f.sum) + (8271924499633/3567000000000000000000000000 : ℝ)*base66 + (577143084443153683/28536000000000000000000000000000 : ℝ)*base68 + (507578367644633683/28536000000000000000000000000000 : ℝ)*base70 + (257135272128185683/28536000000000000000000000000000 : ℝ)*base72 + (212772933461/445875000000000000000000000 : ℝ)*base74 + (454976271396809683/28536000000000000000000000000000 : ℝ)*base76 + (447244036043921683/28536000000000000000000000000000 : ℝ)*base78 + (81590846696513683/28536000000000000000000000000000 : ℝ)*base80 + (2316696448757/891750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (268303/62500000000000000000 : ℝ)*base89 + (268303/62500000000000000000 : ℝ)*base91 + (268303/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (625842937534912416007661423/118900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (807960419/100000000000000 : ℝ)*(base19) + (10395641/1000000000000 : ℝ)*(base23) + (264529/50000000000000 : ℝ)*(upper2) + (39363063/50000000000000 : ℝ)*(upper3) + (45076599/20000000000000 : ℝ)*(upper5) + (4432081318633381/100000000000000 : ℝ)*(major0) + (4432081318633381/100000000000000 : ℝ)*(major1) + (4432081318633381/100000000000000 : ℝ)*(major2) + (3381125737/12500000000000 : ℝ)*(sp1) + (9764755709/50000000000000 : ℝ)*(sp2) + (1500663823300511/25000000000000 : ℝ)*(sp4) + (6002627436235729/100000000000000 : ℝ)*(sp5) + (3001317362063263/50000000000000 : ℝ)*(sp6) + (1430753584305563/50000000000000 : ℝ)*(sp7) + (1430753584305563/50000000000000 : ℝ)*(f.failure) + (1500663823300511/25000000000000 : ℝ)*(f.sum) + (7766891587567/8917500000000000000000000000 : ℝ)*base65 + (1311768005482001423/713400000000000000000000000000000 : ℝ)*base68 + (4268865992638398577/713400000000000000000000000000000 : ℝ)*base69 + (1246447915097801423/713400000000000000000000000000000 : ℝ)*base72 + (3864701217701/4458750000000000000000000000 : ℝ)*base73 + (10477749056151198577/713400000000000000000000000000000 : ℝ)*base75 + (2852039431648398577/713400000000000000000000000000000 : ℝ)*base77 + (715613523107598577/713400000000000000000000000000000 : ℝ)*base79 + (2781627870659/1114687500000000000000000000 : ℝ)*base81 + (2309867/312500000000000000000 : ℝ)*base90 + (2309867/312500000000000000000 : ℝ)*base92 + (2309867/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1346_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9680391/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7359/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11151/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5579/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1471/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1346_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1346_s7_0 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-102026147/500000000 : ℝ)*x 0 + (5412453653/10000000000 : ℝ)*x 1 + (5244775567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (102026147/500000000 : ℝ)^2153 ≤ (6213659675433/50000000000000 : ℝ)^1641 := by
    have hnat : (102026147 : ℕ)^2153*50000000000000^1641 ≤ 6213659675433^1641*500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102026147 500000000 6213659675433 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412453653/10000000000 : ℝ)^2153 ≤ (44690156777751/100000000000000 : ℝ)^1641 := by
    have hnat : (5412453653 : ℕ)^2153*100000000000000^1641 ≤ 44690156777751^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412453653 10000000000 44690156777751 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244775567/10000000000 : ℝ)^2153 ≤ (343060190843/800000000000 : ℝ)^1641 := by
    have hnat : (5244775567 : ℕ)^2153*800000000000^1641 ≤ 343060190843^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244775567 10000000000 343060190843 800000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-102026147/500000000 : ℝ), (5412453653/10000000000 : ℝ), (5244775567/10000000000 : ℝ)] ![(6213659675433/50000000000000 : ℝ), (44690156777751/100000000000000 : ℝ), (343060190843/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-102026147/500000000 : ℝ)|^2153 ≤ (6213659675433/50000000000000 : ℝ)^1641
        have hw : |(-102026147/500000000 : ℝ)|=(102026147/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412453653/10000000000 : ℝ)|^2153 ≤ (44690156777751/100000000000000 : ℝ)^1641
        have hw : |(5412453653/10000000000 : ℝ)|=(5412453653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244775567/10000000000 : ℝ)|^2153 ≤ (343060190843/800000000000 : ℝ)^1641
        have hw : |(5244775567/10000000000 : ℝ)|=(5244775567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s7_1 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674458601/5000000000 : ℝ)*x 0 + (-1062976033/5000000000 : ℝ)*x 1 + (5244775541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674458601/5000000000 : ℝ)^2153 ≤ (22001561666169/50000000000000 : ℝ)^1641 := by
    have hnat : (2674458601 : ℕ)^2153*50000000000000^1641 ≤ 22001561666169^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674458601 5000000000 22001561666169 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062976033/5000000000 : ℝ)^2153 ≤ (13114353080393/100000000000000 : ℝ)^1641 := by
    have hnat : (1062976033 : ℕ)^2153*100000000000000^1641 ≤ 13114353080393^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062976033 5000000000 13114353080393 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244775541/10000000000 : ℝ)^2153 ≤ (21441261788233/50000000000000 : ℝ)^1641 := by
    have hnat : (5244775541 : ℕ)^2153*50000000000000^1641 ≤ 21441261788233^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244775541 10000000000 21441261788233 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674458601/5000000000 : ℝ), (-1062976033/5000000000 : ℝ), (5244775541/10000000000 : ℝ)] ![(22001561666169/50000000000000 : ℝ), (13114353080393/100000000000000 : ℝ), (21441261788233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674458601/5000000000 : ℝ)|^2153 ≤ (22001561666169/50000000000000 : ℝ)^1641
        have hw : |(2674458601/5000000000 : ℝ)|=(2674458601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1062976033/5000000000 : ℝ)|^2153 ≤ (13114353080393/100000000000000 : ℝ)^1641
        have hw : |(-1062976033/5000000000 : ℝ)|=(1062976033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244775541/10000000000 : ℝ)|^2153 ≤ (21441261788233/50000000000000 : ℝ)^1641
        have hw : |(5244775541/10000000000 : ℝ)|=(5244775541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s7_2 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069783437/2000000000 : ℝ)*x 0 + (104895511/200000000 : ℝ)*x 1 + (-531488019/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069783437/2000000000 : ℝ)^2153 ≤ (11000780787213/25000000000000 : ℝ)^1641 := by
    have hnat : (1069783437 : ℕ)^2153*25000000000000^1641 ≤ 11000780787213^1641*2000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069783437 2000000000 11000780787213 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104895511/200000000 : ℝ)^2153 ≤ (10720630918253/25000000000000 : ℝ)^1641 := by
    have hnat : (104895511 : ℕ)^2153*25000000000000^1641 ≤ 10720630918253^1641*200000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104895511 200000000 10720630918253 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531488019/2500000000 : ℝ)^2153 ≤ (13114353161327/100000000000000 : ℝ)^1641 := by
    have hnat : (531488019 : ℕ)^2153*100000000000000^1641 ≤ 13114353161327^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531488019 2500000000 13114353161327 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069783437/2000000000 : ℝ), (104895511/200000000 : ℝ), (-531488019/2500000000 : ℝ)] ![(11000780787213/25000000000000 : ℝ), (10720630918253/25000000000000 : ℝ), (13114353161327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069783437/2000000000 : ℝ)|^2153 ≤ (11000780787213/25000000000000 : ℝ)^1641
        have hw : |(1069783437/2000000000 : ℝ)|=(1069783437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104895511/200000000 : ℝ)|^2153 ≤ (10720630918253/25000000000000 : ℝ)^1641
        have hw : |(104895511/200000000 : ℝ)|=(104895511/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-531488019/2500000000 : ℝ)|^2153 ≤ (13114353161327/100000000000000 : ℝ)^1641
        have hw : |(-531488019/2500000000 : ℝ)|=(531488019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s7_3 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (216278859/500000000 : ℝ)*x 0 + (4153041383/10000000000 : ℝ)*x 1 + (180191361/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216278859/500000000 : ℝ)^2153 ≤ (33303359041939/100000000000000 : ℝ)^1641 := by
    have hnat : (216278859 : ℕ)^2153*100000000000000^1641 ≤ 33303359041939^1641*500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216278859 500000000 33303359041939 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4153041383/10000000000 : ℝ)^2153 ≤ (7892865088497/25000000000000 : ℝ)^1641 := by
    have hnat : (4153041383 : ℕ)^2153*25000000000000^1641 ≤ 7892865088497^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153041383 10000000000 7892865088497 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (180191361/400000000 : ℝ)^2153 ≤ (35125180594247/100000000000000 : ℝ)^1641 := by
    have hnat : (180191361 : ℕ)^2153*100000000000000^1641 ≤ 35125180594247^1641*400000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180191361 400000000 35125180594247 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216278859/500000000 : ℝ), (4153041383/10000000000 : ℝ), (180191361/400000000 : ℝ)] ![(33303359041939/100000000000000 : ℝ), (7892865088497/25000000000000 : ℝ), (35125180594247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216278859/500000000 : ℝ)|^2153 ≤ (33303359041939/100000000000000 : ℝ)^1641
        have hw : |(216278859/500000000 : ℝ)|=(216278859/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4153041383/10000000000 : ℝ)|^2153 ≤ (7892865088497/25000000000000 : ℝ)^1641
        have hw : |(4153041383/10000000000 : ℝ)|=(4153041383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(180191361/400000000 : ℝ)|^2153 ≤ (35125180594247/100000000000000 : ℝ)^1641
        have hw : |(180191361/400000000 : ℝ)|=(180191361/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s7_4 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2040534683/10000000000 : ℝ)*x 0 + (131134403/250000000 : ℝ)*x 1 + (1082370057/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2040534683/10000000000 : ℝ)^2153 ≤ (2485482636569/20000000000000 : ℝ)^1641 := by
    have hnat : (2040534683 : ℕ)^2153*20000000000000^1641 ≤ 2485482636569^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040534683 10000000000 2485482636569 20000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131134403/250000000 : ℝ)^2153 ≤ (268056039123/625000000000 : ℝ)^1641 := by
    have hnat : (131134403 : ℕ)^2153*625000000000^1641 ≤ 268056039123^1641*250000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131134403 250000000 268056039123 625000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082370057/2000000000 : ℝ)^2153 ≤ (44683620539761/100000000000000 : ℝ)^1641 := by
    have hnat : (1082370057 : ℕ)^2153*100000000000000^1641 ≤ 44683620539761^1641*2000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082370057 2000000000 44683620539761 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2040534683/10000000000 : ℝ), (131134403/250000000 : ℝ), (1082370057/2000000000 : ℝ)] ![(2485482636569/20000000000000 : ℝ), (268056039123/625000000000 : ℝ), (44683620539761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2040534683/10000000000 : ℝ)|^2153 ≤ (2485482636569/20000000000000 : ℝ)^1641
        have hw : |(-2040534683/10000000000 : ℝ)|=(2040534683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131134403/250000000 : ℝ)|^2153 ≤ (268056039123/625000000000 : ℝ)^1641
        have hw : |(131134403/250000000 : ℝ)|=(131134403/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082370057/2000000000 : ℝ)|^2153 ≤ (44683620539761/100000000000000 : ℝ)^1641
        have hw : |(1082370057/2000000000 : ℝ)|=(1082370057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s7_5 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061141447/2000000000 : ℝ)*x 0 + (-1958877203/10000000000 : ℝ)*x 1 + (5411850383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061141447/2000000000 : ℝ)^2153 ≤ (43537335287561/100000000000000 : ℝ)^1641 := by
    have hnat : (1061141447 : ℕ)^2153*100000000000000^1641 ≤ 43537335287561^1641*2000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061141447 2000000000 43537335287561 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1958877203/10000000000 : ℝ)^2153 ≤ (11779043094267/100000000000000 : ℝ)^1641 := by
    have hnat : (1958877203 : ℕ)^2153*100000000000000^1641 ≤ 11779043094267^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1958877203 10000000000 11779043094267 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411850383/10000000000 : ℝ)^2153 ≤ (44683621601369/100000000000000 : ℝ)^1641 := by
    have hnat : (5411850383 : ℕ)^2153*100000000000000^1641 ≤ 44683621601369^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411850383 10000000000 44683621601369 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061141447/2000000000 : ℝ), (-1958877203/10000000000 : ℝ), (5411850383/10000000000 : ℝ)] ![(43537335287561/100000000000000 : ℝ), (11779043094267/100000000000000 : ℝ), (44683621601369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061141447/2000000000 : ℝ)|^2153 ≤ (43537335287561/100000000000000 : ℝ)^1641
        have hw : |(1061141447/2000000000 : ℝ)|=(1061141447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1958877203/10000000000 : ℝ)|^2153 ≤ (11779043094267/100000000000000 : ℝ)^1641
        have hw : |(-1958877203/10000000000 : ℝ)|=(1958877203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411850383/10000000000 : ℝ)|^2153 ≤ (44683621601369/100000000000000 : ℝ)^1641
        have hw : |(5411850383/10000000000 : ℝ)|=(5411850383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s7_6 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305707119/10000000000 : ℝ)*x 0 + (54118507/100000000 : ℝ)*x 1 + (-78355077/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305707119/10000000000 : ℝ)^2153 ≤ (21768667019353/50000000000000 : ℝ)^1641 := by
    have hnat : (5305707119 : ℕ)^2153*50000000000000^1641 ≤ 21768667019353^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305707119 10000000000 21768667019353 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54118507/100000000 : ℝ)^2153 ≤ (8936725007069/20000000000000 : ℝ)^1641 := by
    have hnat : (54118507 : ℕ)^2153*20000000000000^1641 ≤ 8936725007069^1641*100000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54118507 100000000 8936725007069 20000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (78355077/400000000 : ℝ)^2153 ≤ (11779040901043/100000000000000 : ℝ)^1641 := by
    have hnat : (78355077 : ℕ)^2153*100000000000000^1641 ≤ 11779040901043^1641*400000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78355077 400000000 11779040901043 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305707119/10000000000 : ℝ), (54118507/100000000 : ℝ), (-78355077/400000000 : ℝ)] ![(21768667019353/50000000000000 : ℝ), (8936725007069/20000000000000 : ℝ), (11779040901043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305707119/10000000000 : ℝ)|^2153 ≤ (21768667019353/50000000000000 : ℝ)^1641
        have hw : |(5305707119/10000000000 : ℝ)|=(5305707119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54118507/100000000 : ℝ)|^2153 ≤ (8936725007069/20000000000000 : ℝ)^1641
        have hw : |(54118507/100000000 : ℝ)|=(54118507/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-78355077/400000000 : ℝ)|^2153 ≤ (11779040901043/100000000000000 : ℝ)^1641
        have hw : |(-78355077/400000000 : ℝ)|=(78355077/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_s7_7 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4325602619/10000000000 : ℝ)*x 0 + (2251762409/5000000000 : ℝ)*x 1 + (2077153529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325602619/10000000000 : ℝ)^2153 ≤ (1665180800521/5000000000000 : ℝ)^1641 := by
    have hnat : (4325602619 : ℕ)^2153*5000000000000^1641 ≤ 1665180800521^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325602619 10000000000 1665180800521 5000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251762409/5000000000 : ℝ)^2153 ≤ (35112299337701/100000000000000 : ℝ)^1641 := by
    have hnat : (2251762409 : ℕ)^2153*100000000000000^1641 ≤ 35112299337701^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251762409 5000000000 35112299337701 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2077153529/5000000000 : ℝ)^2153 ≤ (31584084636611/100000000000000 : ℝ)^1641 := by
    have hnat : (2077153529 : ℕ)^2153*100000000000000^1641 ≤ 31584084636611^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077153529 5000000000 31584084636611 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325602619/10000000000 : ℝ), (2251762409/5000000000 : ℝ), (2077153529/5000000000 : ℝ)] ![(1665180800521/5000000000000 : ℝ), (35112299337701/100000000000000 : ℝ), (31584084636611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325602619/10000000000 : ℝ)|^2153 ≤ (1665180800521/5000000000000 : ℝ)^1641
        have hw : |(4325602619/10000000000 : ℝ)|=(4325602619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2251762409/5000000000 : ℝ)|^2153 ≤ (35112299337701/100000000000000 : ℝ)^1641
        have hw : |(2251762409/5000000000 : ℝ)|=(2251762409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2077153529/5000000000 : ℝ)|^2153 ≤ (31584084636611/100000000000000 : ℝ)^1641
        have hw : |(2077153529/5000000000 : ℝ)|=(2077153529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1346_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9680391/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1471/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5579/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11159/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14709/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1471/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5579/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1471/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5579/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1471/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5579/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1471/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5579/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1471/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5579/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1471/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5579/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5579/50000 : ℝ) ^ (4305/1024 : ℝ) ≤ (9907322851128061/100000000000000000000 : ℝ) := by
    have hpowers : (5579/50000 : ℝ)^4305 ≤ (9907322851128061/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5579 : ℕ)^4305*100000000000000000000^1024 ≤ 9907322851128061^1024*50000^4305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5579 50000 9907322851128061 100000000000000000000 4305 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5579/50000 : ℝ)) (X := (9907322851128061/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1471/10000 : ℝ) ^ (4305/1024 : ℝ) ≤ (31663515883663807/100000000000000000000 : ℝ) := by
    have hpowers : (1471/10000 : ℝ)^4305 ≤ (31663515883663807/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1471 : ℕ)^4305*100000000000000000000^1024 ≤ 31663515883663807^1024*10000^4305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1471 10000 31663515883663807 100000000000000000000 4305 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1471/10000 : ℝ)) (X := (31663515883663807/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009907322851128061/50000000000000000000 : ℝ) ≤ (500023564071217/500000000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (50009907322851128061/50000000000000000000 : ℝ)^1024 ≤ (500023564071217/500000000000000 : ℝ)^4305 := by
      have hnat : (50009907322851128061 : ℕ)^1024*500000000000000^4305 ≤ 500023564071217^4305*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009907322851128061 50000000000000000000 500023564071217 500000000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500023564071217/500000000000000 : ℝ)) (X := (50009907322851128061/50000000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010392709683697967/25000000000000000000 : ℝ) ≤ (10000988659630299/10000000000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (25010392709683697967/25000000000000000000 : ℝ)^1024 ≤ (10000988659630299/10000000000000000 : ℝ)^4305 := by
      have hnat : (25010392709683697967 : ℕ)^1024*10000000000000000^4305 ≤ 10000988659630299^4305*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010392709683697967 25000000000000000000 10000988659630299 10000000000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000988659630299/10000000000000000 : ℝ)) (X := (25010392709683697967/25000000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031663515883663807/50000000000000000000 : ℝ) ≤ (5000753018918129/5000000000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (50031663515883663807/50000000000000000000 : ℝ)^1024 ≤ (5000753018918129/5000000000000000 : ℝ)^4305 := by
      have hnat : (50031663515883663807 : ℕ)^1024*5000000000000000^4305 ≤ 5000753018918129^4305*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031663515883663807 50000000000000000000 5000753018918129 5000000000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000753018918129/5000000000000000 : ℝ)) (X := (50031663515883663807/50000000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9907322851128061/100000000000000000000 : ℝ) ≤ ((8877532044893768659/8880000000000000000 : ℝ)+2*(517378205959/355200000000000 : ℝ)*(5579/50000 : ℝ))^(4305/1024 : ℝ) := by
    rw [show (8877532044893768659/8880000000000000000 : ℝ)+2*(517378205959/355200000000000 : ℝ)*(5579/50000 : ℝ)=(500023564071217/500000000000000 : ℝ) by norm_num, show 1+2*(9907322851128061/100000000000000000000 : ℝ)=(50009907322851128061/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31663515883663807/100000000000000000000 : ℝ)+(9907322851128061/100000000000000000000 : ℝ) ≤ ((8877532044893768659/8880000000000000000 : ℝ)+(517378205959/355200000000000 : ℝ)*((1471/10000 : ℝ)+(5579/50000 : ℝ)))^(4305/1024 : ℝ) := by
    rw [show (8877532044893768659/8880000000000000000 : ℝ)+(517378205959/355200000000000 : ℝ)*((1471/10000 : ℝ)+(5579/50000 : ℝ))=(10000988659630299/10000000000000000 : ℝ) by norm_num, show 1+(31663515883663807/100000000000000000000 : ℝ)+(9907322851128061/100000000000000000000 : ℝ)=(25010392709683697967/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31663515883663807/100000000000000000000 : ℝ) ≤ ((8877532044893768659/8880000000000000000 : ℝ)+2*(517378205959/355200000000000 : ℝ)*(1471/10000 : ℝ))^(4305/1024 : ℝ) := by
    rw [show (8877532044893768659/8880000000000000000 : ℝ)+2*(517378205959/355200000000000 : ℝ)*(1471/10000 : ℝ)=(5000753018918129/5000000000000000 : ℝ) by norm_num, show 1+2*(31663515883663807/100000000000000000000 : ℝ)=(50031663515883663807/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8877532044893768659/8880000000000000000 : ℝ)*(X 1 0+X 2 0)+(517378205959/355200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (5579/50000 : ℝ)) (hi := (1471/10000 : ℝ)) (c := (8877532044893768659/8880000000000000000 : ℝ)) (alpha := (517378205959/355200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8877532044893768659/8880000000000000000 : ℝ)*(X 0 1+X 2 1)+(517378205959/355200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (5579/50000 : ℝ)) (hi := (1471/10000 : ℝ)) (c := (8877532044893768659/8880000000000000000 : ℝ)) (alpha := (517378205959/355200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8877532044893768659/8880000000000000000 : ℝ)*(X 0 2+X 1 2)+(517378205959/355200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (5579/50000 : ℝ)) (hi := (1471/10000 : ℝ)) (c := (8877532044893768659/8880000000000000000 : ℝ)) (alpha := (517378205959/355200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-102026147/500000000 : ℝ)*X 0 0+(5412453653/10000000000 : ℝ)*X 0 1+(5244775567/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674458601/5000000000 : ℝ)*X 1 0+(-1062976033/5000000000 : ℝ)*X 1 1+(5244775541/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069783437/2000000000 : ℝ)*X 2 0+(104895511/200000000 : ℝ)*X 2 1+(-531488019/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((216278859/500000000 : ℝ)*X 0 0+(4153041383/10000000000 : ℝ)*X 0 1+(180191361/400000000 : ℝ)*X 0 2+(216278859/500000000 : ℝ)*X 1 0+(4153041383/10000000000 : ℝ)*X 1 1+(180191361/400000000 : ℝ)*X 1 2+(216278859/500000000 : ℝ)*X 2 0+(4153041383/10000000000 : ℝ)*X 2 1+(180191361/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2040534683/10000000000 : ℝ)*X 0 0+(131134403/250000000 : ℝ)*X 0 1+(1082370057/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061141447/2000000000 : ℝ)*X 1 0+(-1958877203/10000000000 : ℝ)*X 1 1+(5411850383/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305707119/10000000000 : ℝ)*X 2 0+(54118507/100000000 : ℝ)*X 2 1+(-78355077/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4325602619/10000000000 : ℝ)*X 0 0+(2251762409/5000000000 : ℝ)*X 0 1+(2077153529/5000000000 : ℝ)*X 0 2+(4325602619/10000000000 : ℝ)*X 1 0+(2251762409/5000000000 : ℝ)*X 1 1+(2077153529/5000000000 : ℝ)*X 1 2+(4325602619/10000000000 : ℝ)*X 2 0+(2251762409/5000000000 : ℝ)*X 2 1+(2077153529/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (557371822544066708739758127/74000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (287091271/20000000000000 : ℝ)*(base19) + (1310114993/100000000000000 : ℝ)*(base23) + (11381097/20000000000000 : ℝ)*(lower2) + (99484617/50000000000000 : ℝ)*(upper3) + (104589501/100000000000000 : ℝ)*(upper5) + (4403441729176353/100000000000000 : ℝ)*(major0) + (4403441729176353/100000000000000 : ℝ)*(major1) + (4403441729176353/100000000000000 : ℝ)*(major2) + (74547984298287/1250000000000 : ℝ)*(sp0) + (5963865326794661/100000000000000 : ℝ)*(sp1) + (2981932726068011/50000000000000 : ℝ)*(sp2) + (2843001132735509/100000000000000 : ℝ)*(sp3) + (3502298507/12500000000000 : ℝ)*(sp4) + (957018611/6250000000000 : ℝ)*(sp7) + (710754111258321/25000000000000 : ℝ)*(f.failure) + (745483345281377/12500000000000 : ℝ)*(f.sum) + (33764260828211/5920000000000000000000000000 : ℝ)*base66 + (3465469375778834791/296000000000000000000000000000000 : ℝ)*base68 + (3111646278386834791/296000000000000000000000000000000 : ℝ)*base70 + (3336244410394834791/296000000000000000000000000000000 : ℝ)*base72 + (19673138044371/5920000000000000000000000000 : ℝ)*base74 + (6081619205402834791/296000000000000000000000000000000 : ℝ)*base76 + (3125693556602834791/296000000000000000000000000000000 : ℝ)*base78 + (1140040060221165209/296000000000000000000000000000000 : ℝ)*base79 + (25241554998611/5920000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2278989/156250000000000000000 : ℝ)*base90 + (2278989/156250000000000000000 : ℝ)*base92 + (2278989/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27725664045223184741829/2960000000000000000000000000 : ℝ) := by norm_num
    linear_combination (439188387/50000000000000 : ℝ)*(base19) + (15274497/1000000000000 : ℝ)*(base23) + (15223969/5000000000000 : ℝ)*(lower1) + (157400721/100000000000000 : ℝ)*(upper3) + (300053091/100000000000000 : ℝ)*(lower4) + (1759403/100000000000000 : ℝ)*(upper5) + (2217610557506977/50000000000000 : ℝ)*(major0) + (2217610557506977/50000000000000 : ℝ)*(major1) + (2217610557506977/50000000000000 : ℝ)*(major2) + (13192076277/50000000000000 : ℝ)*(sp2) + (15017268966273/250000000000 : ℝ)*(sp4) + (3003453354066213/50000000000000 : ℝ)*(sp5) + (1201375934981389/20000000000000 : ℝ)*(sp6) + (572706866258547/20000000000000 : ℝ)*(sp7) + (572706866258547/20000000000000 : ℝ)*(f.failure) + (15017268966273/250000000000 : ℝ)*(f.sum) + (14977148085257/8880000000000000000000000000 : ℝ)*base66 + (31216900768004991157/444000000000000000000000000000000 : ℝ)*base68 + (2458862881604991157/444000000000000000000000000000000 : ℝ)*base70 + (61851601555184991157/444000000000000000000000000000000 : ℝ)*base72 + (9880235761817/8880000000000000000000000000 : ℝ)*base74 + (787799580243008843/444000000000000000000000000000000 : ℝ)*base75 + (2290867398075008843/444000000000000000000000000000000 : ℝ)*base77 + (2712663615195008843/444000000000000000000000000000000 : ℝ)*base79 + (57972225844937/8880000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (448123/125000000000000000000 : ℝ)*base90 + (448123/125000000000000000000 : ℝ)*base92 + (448123/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1346_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9680391/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1471/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5579/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11159/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1346_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1346_box_0 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-374716107/2000000000 : ℝ)*x 0 + (1077954961/2000000000 : ℝ)*x 1 + (2694887389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (374716107/2000000000 : ℝ)^2153 ≤ (5555365052721/50000000000000 : ℝ)^1641 := by
    have hnat : (374716107 : ℕ)^2153*50000000000000^1641 ≤ 5555365052721^1641*2000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374716107 2000000000 5555365052721 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077954961/2000000000 : ℝ)^2153 ≤ (177778540327/400000000000 : ℝ)^1641 := by
    have hnat : (1077954961 : ℕ)^2153*400000000000^1641 ≤ 177778540327^1641*2000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077954961 2000000000 177778540327 400000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2694887389/5000000000 : ℝ)^2153 ≤ (44444634789639/100000000000000 : ℝ)^1641 := by
    have hnat : (2694887389 : ℕ)^2153*100000000000000^1641 ≤ 44444634789639^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694887389 5000000000 44444634789639 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-374716107/2000000000 : ℝ), (1077954961/2000000000 : ℝ), (2694887389/5000000000 : ℝ)] ![(5555365052721/50000000000000 : ℝ), (177778540327/400000000000 : ℝ), (44444634789639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-374716107/2000000000 : ℝ)|^2153 ≤ (5555365052721/50000000000000 : ℝ)^1641
        have hw : |(-374716107/2000000000 : ℝ)|=(374716107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1077954961/2000000000 : ℝ)|^2153 ≤ (177778540327/400000000000 : ℝ)^1641
        have hw : |(1077954961/2000000000 : ℝ)|=(1077954961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2694887389/5000000000 : ℝ)|^2153 ≤ (44444634789639/100000000000000 : ℝ)^1641
        have hw : |(2694887389/5000000000 : ℝ)|=(2694887389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_box_1 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5285217959/10000000000 : ℝ)*x 0 + (-201684749/1000000000 : ℝ)*x 1 + (5389774699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285217959/10000000000 : ℝ)^2153 ≤ (10829220234029/25000000000000 : ℝ)^1641 := by
    have hnat : (5285217959 : ℕ)^2153*25000000000000^1641 ≤ 10829220234029^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285217959 10000000000 10829220234029 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201684749/1000000000 : ℝ)^2153 ≤ (6119242552119/50000000000000 : ℝ)^1641 := by
    have hnat : (201684749 : ℕ)^2153*50000000000000^1641 ≤ 6119242552119^1641*1000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201684749 1000000000 6119242552119 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5389774699/10000000000 : ℝ)^2153 ≤ (1388894810467/3125000000000 : ℝ)^1641 := by
    have hnat : (5389774699 : ℕ)^2153*3125000000000^1641 ≤ 1388894810467^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389774699 10000000000 1388894810467 3125000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285217959/10000000000 : ℝ), (-201684749/1000000000 : ℝ), (5389774699/10000000000 : ℝ)] ![(10829220234029/25000000000000 : ℝ), (6119242552119/50000000000000 : ℝ), (1388894810467/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285217959/10000000000 : ℝ)|^2153 ≤ (10829220234029/25000000000000 : ℝ)^1641
        have hw : |(5285217959/10000000000 : ℝ)|=(5285217959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-201684749/1000000000 : ℝ)|^2153 ≤ (6119242552119/50000000000000 : ℝ)^1641
        have hw : |(-201684749/1000000000 : ℝ)|=(201684749/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5389774699/10000000000 : ℝ)|^2153 ≤ (1388894810467/3125000000000 : ℝ)^1641
        have hw : |(5389774699/10000000000 : ℝ)|=(5389774699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_box_2 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1321304491/2500000000 : ℝ)*x 0 + (1347443689/2500000000 : ℝ)*x 1 + (-1008423703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321304491/2500000000 : ℝ)^2153 ≤ (43316880989881/100000000000000 : ℝ)^1641 := by
    have hnat : (1321304491 : ℕ)^2153*100000000000000^1641 ≤ 43316880989881^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321304491 2500000000 43316880989881 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347443689/2500000000 : ℝ)^2153 ≤ (44444634551623/100000000000000 : ℝ)^1641 := by
    have hnat : (1347443689 : ℕ)^2153*100000000000000^1641 ≤ 44444634551623^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347443689 2500000000 44444634551623 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1008423703/5000000000 : ℝ)^2153 ≤ (305962110887/2500000000000 : ℝ)^1641 := by
    have hnat : (1008423703 : ℕ)^2153*2500000000000^1641 ≤ 305962110887^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008423703 5000000000 305962110887 2500000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321304491/2500000000 : ℝ), (1347443689/2500000000 : ℝ), (-1008423703/5000000000 : ℝ)] ![(43316880989881/100000000000000 : ℝ), (44444634551623/100000000000000 : ℝ), (305962110887/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321304491/2500000000 : ℝ)|^2153 ≤ (43316880989881/100000000000000 : ℝ)^1641
        have hw : |(1321304491/2500000000 : ℝ)|=(1321304491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347443689/2500000000 : ℝ)|^2153 ≤ (44444634551623/100000000000000 : ℝ)^1641
        have hw : |(1347443689/2500000000 : ℝ)|=(1347443689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1008423703/5000000000 : ℝ)|^2153 ≤ (305962110887/2500000000000 : ℝ)^1641
        have hw : |(-1008423703/5000000000 : ℝ)|=(1008423703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_box_3 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (279604797/625000000 : ℝ)*x 0 + (425540773/1000000000 : ℝ)*x 1 + (4255407729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (279604797/625000000 : ℝ)^2153 ≤ (17403646661581/50000000000000 : ℝ)^1641 := by
    have hnat : (279604797 : ℕ)^2153*50000000000000^1641 ≤ 17403646661581^1641*625000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279604797 625000000 17403646661581 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (425540773/1000000000 : ℝ)^2153 ≤ (8149088333849/25000000000000 : ℝ)^1641 := by
    have hnat : (425540773 : ℕ)^2153*25000000000000^1641 ≤ 8149088333849^1641*1000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425540773 1000000000 8149088333849 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4255407729/10000000000 : ℝ)^2153 ≤ (32596353325347/100000000000000 : ℝ)^1641 := by
    have hnat : (4255407729 : ℕ)^2153*100000000000000^1641 ≤ 32596353325347^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4255407729 10000000000 32596353325347 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(279604797/625000000 : ℝ), (425540773/1000000000 : ℝ), (4255407729/10000000000 : ℝ)] ![(17403646661581/50000000000000 : ℝ), (8149088333849/25000000000000 : ℝ), (32596353325347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(279604797/625000000 : ℝ)|^2153 ≤ (17403646661581/50000000000000 : ℝ)^1641
        have hw : |(279604797/625000000 : ℝ)|=(279604797/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(425540773/1000000000 : ℝ)|^2153 ≤ (8149088333849/25000000000000 : ℝ)^1641
        have hw : |(425540773/1000000000 : ℝ)|=(425540773/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4255407729/10000000000 : ℝ)|^2153 ≤ (32596353325347/100000000000000 : ℝ)^1641
        have hw : |(4255407729/10000000000 : ℝ)|=(4255407729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_box_4 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1105107883/5000000000 : ℝ)*x 0 + (1053002491/2000000000 : ℝ)*x 1 + (2632506679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1105107883/5000000000 : ℝ)^2153 ≤ (3450127168629/25000000000000 : ℝ)^1641 := by
    have hnat : (1105107883 : ℕ)^2153*25000000000000^1641 ≤ 3450127168629^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105107883 5000000000 3450127168629 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053002491/2000000000 : ℝ)^2153 ≤ (430997408061/1000000000000 : ℝ)^1641 := by
    have hnat : (1053002491 : ℕ)^2153*1000000000000^1641 ≤ 430997408061^1641*2000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053002491 2000000000 430997408061 1000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632506679/5000000000 : ℝ)^2153 ≤ (43099750504463/100000000000000 : ℝ)^1641 := by
    have hnat : (2632506679 : ℕ)^2153*100000000000000^1641 ≤ 43099750504463^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632506679 5000000000 43099750504463 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1105107883/5000000000 : ℝ), (1053002491/2000000000 : ℝ), (2632506679/5000000000 : ℝ)] ![(3450127168629/25000000000000 : ℝ), (430997408061/1000000000000 : ℝ), (43099750504463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1105107883/5000000000 : ℝ)|^2153 ≤ (3450127168629/25000000000000 : ℝ)^1641
        have hw : |(-1105107883/5000000000 : ℝ)|=(1105107883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053002491/2000000000 : ℝ)|^2153 ≤ (430997408061/1000000000000 : ℝ)^1641
        have hw : |(1053002491/2000000000 : ℝ)|=(1053002491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632506679/5000000000 : ℝ)|^2153 ≤ (43099750504463/100000000000000 : ℝ)^1641
        have hw : |(2632506679/5000000000 : ℝ)|=(2632506679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_box_5 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5372833229/10000000000 : ℝ)*x 0 + (-1033469257/5000000000 : ℝ)*x 1 + (5265013111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372833229/10000000000 : ℝ)^2153 ≤ (11065358839389/25000000000000 : ℝ)^1641 := by
    have hnat : (5372833229 : ℕ)^2153*25000000000000^1641 ≤ 11065358839389^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372833229 10000000000 11065358839389 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033469257/5000000000 : ℝ)^2153 ≤ (12638816773441/100000000000000 : ℝ)^1641 := by
    have hnat : (1033469257 : ℕ)^2153*100000000000000^1641 ≤ 12638816773441^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033469257 5000000000 12638816773441 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265013111/10000000000 : ℝ)^2153 ≤ (10774936962911/25000000000000 : ℝ)^1641 := by
    have hnat : (5265013111 : ℕ)^2153*25000000000000^1641 ≤ 10774936962911^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265013111 10000000000 10774936962911 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372833229/10000000000 : ℝ), (-1033469257/5000000000 : ℝ), (5265013111/10000000000 : ℝ)] ![(11065358839389/25000000000000 : ℝ), (12638816773441/100000000000000 : ℝ), (10774936962911/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372833229/10000000000 : ℝ)|^2153 ≤ (11065358839389/25000000000000 : ℝ)^1641
        have hw : |(5372833229/10000000000 : ℝ)|=(5372833229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1033469257/5000000000 : ℝ)|^2153 ≤ (12638816773441/100000000000000 : ℝ)^1641
        have hw : |(-1033469257/5000000000 : ℝ)|=(1033469257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265013111/10000000000 : ℝ)|^2153 ≤ (10774936962911/25000000000000 : ℝ)^1641
        have hw : |(5265013111/10000000000 : ℝ)|=(5265013111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_box_6 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1074566691/2000000000 : ℝ)*x 0 + (5265012951/10000000000 : ℝ)*x 1 + (-258367303/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074566691/2000000000 : ℝ)^2153 ≤ (44261437800233/100000000000000 : ℝ)^1641 := by
    have hnat : (1074566691 : ℕ)^2153*100000000000000^1641 ≤ 44261437800233^1641*2000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074566691 2000000000 44261437800233 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265012951/10000000000 : ℝ)^2153 ≤ (21549873066609/50000000000000 : ℝ)^1641 := by
    have hnat : (5265012951 : ℕ)^2153*50000000000000^1641 ≤ 21549873066609^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265012951 10000000000 21549873066609 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258367303/1250000000 : ℝ)^2153 ≤ (789926003213/6250000000000 : ℝ)^1641 := by
    have hnat : (258367303 : ℕ)^2153*6250000000000^1641 ≤ 789926003213^1641*1250000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258367303 1250000000 789926003213 6250000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074566691/2000000000 : ℝ), (5265012951/10000000000 : ℝ), (-258367303/1250000000 : ℝ)] ![(44261437800233/100000000000000 : ℝ), (21549873066609/50000000000000 : ℝ), (789926003213/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074566691/2000000000 : ℝ)|^2153 ≤ (44261437800233/100000000000000 : ℝ)^1641
        have hw : |(1074566691/2000000000 : ℝ)|=(1074566691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265012951/10000000000 : ℝ)|^2153 ≤ (21549873066609/50000000000000 : ℝ)^1641
        have hw : |(5265012951/10000000000 : ℝ)|=(5265012951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-258367303/1250000000 : ℝ)|^2153 ≤ (789926003213/6250000000000 : ℝ)^1641
        have hw : |(-258367303/1250000000 : ℝ)|=(258367303/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_box_7 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4176545867/10000000000 : ℝ)*x 0 + (1100980127/2500000000 : ℝ)*x 1 + (4403918909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4176545867/10000000000 : ℝ)^2153 ≤ (15903048909953/50000000000000 : ℝ)^1641 := by
    have hnat : (4176545867 : ℕ)^2153*50000000000000^1641 ≤ 15903048909953^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4176545867 10000000000 15903048909953 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1100980127/2500000000 : ℝ)^2153 ≤ (17048479601313/50000000000000 : ℝ)^1641 := by
    have hnat : (1100980127 : ℕ)^2153*50000000000000^1641 ≤ 17048479601313^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100980127 2500000000 17048479601313 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4403918909/10000000000 : ℝ)^2153 ≤ (34096942959857/100000000000000 : ℝ)^1641 := by
    have hnat : (4403918909 : ℕ)^2153*100000000000000^1641 ≤ 34096942959857^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4403918909 10000000000 34096942959857 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4176545867/10000000000 : ℝ), (1100980127/2500000000 : ℝ), (4403918909/10000000000 : ℝ)] ![(15903048909953/50000000000000 : ℝ), (17048479601313/50000000000000 : ℝ), (34096942959857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4176545867/10000000000 : ℝ)|^2153 ≤ (15903048909953/50000000000000 : ℝ)^1641
        have hw : |(4176545867/10000000000 : ℝ)|=(4176545867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1100980127/2500000000 : ℝ)|^2153 ≤ (17048479601313/50000000000000 : ℝ)^1641
        have hw : |(1100980127/2500000000 : ℝ)|=(1100980127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4403918909/10000000000 : ℝ)|^2153 ≤ (34096942959857/100000000000000 : ℝ)^1641
        have hw : |(4403918909/10000000000 : ℝ)|=(4403918909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_box_8 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-53487807/250000000 : ℝ)*x 0 + (2589552047/5000000000 : ℝ)*x 1 + (540379327/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53487807/250000000 : ℝ)^2153 ≤ (13224209817471/100000000000000 : ℝ)^1641 := by
    have hnat : (53487807 : ℕ)^2153*100000000000000^1641 ≤ 13224209817471^1641*250000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53487807 250000000 13224209817471 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2589552047/5000000000 : ℝ)^2153 ≤ (10544857209317/25000000000000 : ℝ)^1641 := by
    have hnat : (2589552047 : ℕ)^2153*25000000000000^1641 ≤ 10544857209317^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589552047 5000000000 10544857209317 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540379327/1000000000 : ℝ)^2153 ≤ (11149090331759/25000000000000 : ℝ)^1641 := by
    have hnat : (540379327 : ℕ)^2153*25000000000000^1641 ≤ 11149090331759^1641*1000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540379327 1000000000 11149090331759 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53487807/250000000 : ℝ), (2589552047/5000000000 : ℝ), (540379327/1000000000 : ℝ)] ![(13224209817471/100000000000000 : ℝ), (10544857209317/25000000000000 : ℝ), (11149090331759/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53487807/250000000 : ℝ)|^2153 ≤ (13224209817471/100000000000000 : ℝ)^1641
        have hw : |(-53487807/250000000 : ℝ)|=(53487807/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2589552047/5000000000 : ℝ)|^2153 ≤ (10544857209317/25000000000000 : ℝ)^1641
        have hw : |(2589552047/5000000000 : ℝ)|=(2589552047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540379327/1000000000 : ℝ)|^2153 ≤ (11149090331759/25000000000000 : ℝ)^1641
        have hw : |(540379327/1000000000 : ℝ)|=(540379327/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_box_9 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1055073581/2000000000 : ℝ)*x 0 + (-251385869/1250000000 : ℝ)*x 1 + (1080758673/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055073581/2000000000 : ℝ)^2153 ≤ (10802748523547/25000000000000 : ℝ)^1641 := by
    have hnat : (1055073581 : ℕ)^2153*25000000000000^1641 ≤ 10802748523547^1641*2000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055073581 2000000000 10802748523547 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (251385869/1250000000 : ℝ)^2153 ≤ (2438528708219/20000000000000 : ℝ)^1641 := by
    have hnat : (251385869 : ℕ)^2153*20000000000000^1641 ≤ 2438528708219^1641*1250000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251385869 1250000000 2438528708219 20000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080758673/2000000000 : ℝ)^2153 ≤ (44596362355667/100000000000000 : ℝ)^1641 := by
    have hnat : (1080758673 : ℕ)^2153*100000000000000^1641 ≤ 44596362355667^1641*2000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080758673 2000000000 44596362355667 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055073581/2000000000 : ℝ), (-251385869/1250000000 : ℝ), (1080758673/2000000000 : ℝ)] ![(10802748523547/25000000000000 : ℝ), (2438528708219/20000000000000 : ℝ), (44596362355667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055073581/2000000000 : ℝ)|^2153 ≤ (10802748523547/25000000000000 : ℝ)^1641
        have hw : |(1055073581/2000000000 : ℝ)|=(1055073581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-251385869/1250000000 : ℝ)|^2153 ≤ (2438528708219/20000000000000 : ℝ)^1641
        have hw : |(-251385869/1250000000 : ℝ)|=(251385869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080758673/2000000000 : ℝ)|^2153 ≤ (44596362355667/100000000000000 : ℝ)^1641
        have hw : |(1080758673/2000000000 : ℝ)|=(1080758673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_box_10 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1318841997/2500000000 : ℝ)*x 0 + (1080758661/2000000000 : ℝ)*x 1 + (-1005543461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1318841997/2500000000 : ℝ)^2153 ≤ (5401374373271/12500000000000 : ℝ)^1641 := by
    have hnat : (1318841997 : ℕ)^2153*12500000000000^1641 ≤ 5401374373271^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318841997 2500000000 5401374373271 12500000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080758661/2000000000 : ℝ)^2153 ≤ (8919272341201/20000000000000 : ℝ)^1641 := by
    have hnat : (1080758661 : ℕ)^2153*20000000000000^1641 ≤ 8919272341201^1641*2000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080758661 2000000000 8919272341201 20000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1005543461/5000000000 : ℝ)^2153 ≤ (6096321651233/50000000000000 : ℝ)^1641 := by
    have hnat : (1005543461 : ℕ)^2153*50000000000000^1641 ≤ 6096321651233^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005543461 5000000000 6096321651233 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1318841997/2500000000 : ℝ), (1080758661/2000000000 : ℝ), (-1005543461/5000000000 : ℝ)] ![(5401374373271/12500000000000 : ℝ), (8919272341201/20000000000000 : ℝ), (6096321651233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1318841997/2500000000 : ℝ)|^2153 ≤ (5401374373271/12500000000000 : ℝ)^1641
        have hw : |(1318841997/2500000000 : ℝ)|=(1318841997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080758661/2000000000 : ℝ)|^2153 ≤ (8919272341201/20000000000000 : ℝ)^1641
        have hw : |(1080758661/2000000000 : ℝ)|=(1080758661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1005543461/5000000000 : ℝ)|^2153 ≤ (6096321651233/50000000000000 : ℝ)^1641
        have hw : |(-1005543461/5000000000 : ℝ)|=(1005543461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_box_11 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (11266259/25000000 : ℝ)*x 0 + (1059676719/2500000000 : ℝ)*x 1 + (264919177/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11266259/25000000 : ℝ)^2153 ≤ (35142773072461/100000000000000 : ℝ)^1641 := by
    have hnat : (11266259 : ℕ)^2153*100000000000000^1641 ≤ 35142773072461^1641*25000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11266259 25000000 35142773072461 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059676719/2500000000 : ℝ)^2153 ≤ (32428613679147/100000000000000 : ℝ)^1641 := by
    have hnat : (1059676719 : ℕ)^2153*100000000000000^1641 ≤ 32428613679147^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059676719 2500000000 32428613679147 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264919177/625000000 : ℝ)^2153 ≤ (8107153309373/25000000000000 : ℝ)^1641 := by
    have hnat : (264919177 : ℕ)^2153*25000000000000^1641 ≤ 8107153309373^1641*625000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264919177 625000000 8107153309373 25000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(11266259/25000000 : ℝ), (1059676719/2500000000 : ℝ), (264919177/625000000 : ℝ)] ![(35142773072461/100000000000000 : ℝ), (32428613679147/100000000000000 : ℝ), (8107153309373/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(11266259/25000000 : ℝ)|^2153 ≤ (35142773072461/100000000000000 : ℝ)^1641
        have hw : |(11266259/25000000 : ℝ)|=(11266259/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1059676719/2500000000 : ℝ)|^2153 ≤ (32428613679147/100000000000000 : ℝ)^1641
        have hw : |(1059676719/2500000000 : ℝ)|=(1059676719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(264919177/625000000 : ℝ)|^2153 ≤ (8107153309373/25000000000000 : ℝ)^1641
        have hw : |(264919177/625000000 : ℝ)|=(264919177/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_box_12 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-972307017/5000000000 : ℝ)*x 0 + (1368371773/2500000000 : ℝ)*x 1 + (525393967/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (972307017/5000000000 : ℝ)^2153 ≤ (11666644765811/100000000000000 : ℝ)^1641 := by
    have hnat : (972307017 : ℕ)^2153*100000000000000^1641 ≤ 11666644765811^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972307017 5000000000 11666644765811 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368371773/2500000000 : ℝ)^2153 ≤ (5669062355157/12500000000000 : ℝ)^1641 := by
    have hnat : (1368371773 : ℕ)^2153*12500000000000^1641 ≤ 5669062355157^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368371773 2500000000 5669062355157 12500000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525393967/1000000000 : ℝ)^2153 ≤ (42980856372481/100000000000000 : ℝ)^1641 := by
    have hnat : (525393967 : ℕ)^2153*100000000000000^1641 ≤ 42980856372481^1641*1000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525393967 1000000000 42980856372481 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-972307017/5000000000 : ℝ), (1368371773/2500000000 : ℝ), (525393967/1000000000 : ℝ)] ![(11666644765811/100000000000000 : ℝ), (5669062355157/12500000000000 : ℝ), (42980856372481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-972307017/5000000000 : ℝ)|^2153 ≤ (11666644765811/100000000000000 : ℝ)^1641
        have hw : |(-972307017/5000000000 : ℝ)|=(972307017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1368371773/2500000000 : ℝ)|^2153 ≤ (5669062355157/12500000000000 : ℝ)^1641
        have hw : |(1368371773/2500000000 : ℝ)|=(1368371773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(525393967/1000000000 : ℝ)|^2153 ≤ (42980856372481/100000000000000 : ℝ)^1641
        have hw : |(525393967/1000000000 : ℝ)|=(525393967/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_box_13 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (538060731/1000000000 : ℝ)*x 0 + (-1035640307/5000000000 : ℝ)*x 1 + (5253939819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538060731/1000000000 : ℝ)^2153 ≤ (5543184869287/12500000000000 : ℝ)^1641 := by
    have hnat : (538060731 : ℕ)^2153*12500000000000^1641 ≤ 5543184869287^1641*1000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538060731 1000000000 5543184869287 12500000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035640307/5000000000 : ℝ)^2153 ≤ (792103940557/6250000000000 : ℝ)^1641 := by
    have hnat : (1035640307 : ℕ)^2153*6250000000000^1641 ≤ 792103940557^1641*5000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035640307 5000000000 792103940557 6250000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253939819/10000000000 : ℝ)^2153 ≤ (21490428985857/50000000000000 : ℝ)^1641 := by
    have hnat : (5253939819 : ℕ)^2153*50000000000000^1641 ≤ 21490428985857^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253939819 10000000000 21490428985857 50000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538060731/1000000000 : ℝ), (-1035640307/5000000000 : ℝ), (5253939819/10000000000 : ℝ)] ![(5543184869287/12500000000000 : ℝ), (792103940557/6250000000000 : ℝ), (21490428985857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538060731/1000000000 : ℝ)|^2153 ≤ (5543184869287/12500000000000 : ℝ)^1641
        have hw : |(538060731/1000000000 : ℝ)|=(538060731/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1035640307/5000000000 : ℝ)|^2153 ≤ (792103940557/6250000000000 : ℝ)^1641
        have hw : |(-1035640307/5000000000 : ℝ)|=(1035640307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253939819/10000000000 : ℝ)|^2153 ≤ (21490428985857/50000000000000 : ℝ)^1641
        have hw : |(5253939819/10000000000 : ℝ)|=(5253939819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_box_14 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5380608001/10000000000 : ℝ)*x 0 + (5253939353/10000000000 : ℝ)*x 1 + (-2071280307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380608001/10000000000 : ℝ)^2153 ≤ (8869097285241/20000000000000 : ℝ)^1641 := by
    have hnat : (5380608001 : ℕ)^2153*20000000000000^1641 ≤ 8869097285241^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380608001 10000000000 8869097285241 20000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253939353/10000000000 : ℝ)^2153 ≤ (42980852970087/100000000000000 : ℝ)^1641 := by
    have hnat : (5253939353 : ℕ)^2153*100000000000000^1641 ≤ 42980852970087^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253939353 10000000000 42980852970087 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2071280307/10000000000 : ℝ)^2153 ≤ (2534732116873/20000000000000 : ℝ)^1641 := by
    have hnat : (2071280307 : ℕ)^2153*20000000000000^1641 ≤ 2534732116873^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071280307 10000000000 2534732116873 20000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380608001/10000000000 : ℝ), (5253939353/10000000000 : ℝ), (-2071280307/10000000000 : ℝ)] ![(8869097285241/20000000000000 : ℝ), (42980852970087/100000000000000 : ℝ), (2534732116873/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380608001/10000000000 : ℝ)|^2153 ≤ (8869097285241/20000000000000 : ℝ)^1641
        have hw : |(5380608001/10000000000 : ℝ)|=(5380608001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253939353/10000000000 : ℝ)|^2153 ≤ (42980852970087/100000000000000 : ℝ)^1641
        have hw : |(5253939353/10000000000 : ℝ)|=(5253939353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2071280307/10000000000 : ℝ)|^2153 ≤ (2534732116873/20000000000000 : ℝ)^1641
        have hw : |(-2071280307/10000000000 : ℝ)|=(2071280307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1346_box_15 (p : ℝ) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ)) (x : Fin 3 → ℝ) :
    (518715851/1250000000 : ℝ)*x 0 + (1104272387/2500000000 : ℝ)*x 1 + (4417090257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518715851/1250000000 : ℝ)^2153 ≤ (1971150332417/6250000000000 : ℝ)^1641 := by
    have hnat : (518715851 : ℕ)^2153*6250000000000^1641 ≤ 1971150332417^1641*1250000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518715851 1250000000 1971150332417 6250000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1104272387/2500000000 : ℝ)^2153 ≤ (34230793725231/100000000000000 : ℝ)^1641 := by
    have hnat : (1104272387 : ℕ)^2153*100000000000000^1641 ≤ 34230793725231^1641*2500000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104272387 2500000000 34230793725231 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4417090257/10000000000 : ℝ)^2153 ≤ (34230800934023/100000000000000 : ℝ)^1641 := by
    have hnat : (4417090257 : ℕ)^2153*100000000000000^1641 ≤ 34230800934023^1641*10000000000^2153 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4417090257 10000000000 34230800934023 100000000000000 2153 1641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2153/512 : ℝ)) 2153 1641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518715851/1250000000 : ℝ), (1104272387/2500000000 : ℝ), (4417090257/10000000000 : ℝ)] ![(1971150332417/6250000000000 : ℝ), (34230793725231/100000000000000 : ℝ), (34230800934023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518715851/1250000000 : ℝ)|^2153 ≤ (1971150332417/6250000000000 : ℝ)^1641
        have hw : |(518715851/1250000000 : ℝ)|=(518715851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1104272387/2500000000 : ℝ)|^2153 ≤ (34230793725231/100000000000000 : ℝ)^1641
        have hw : |(1104272387/2500000000 : ℝ)|=(1104272387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4417090257/10000000000 : ℝ)|^2153 ≤ (34230800934023/100000000000000 : ℝ)^1641
        have hw : |(4417090257/10000000000 : ℝ)|=(4417090257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1346_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9680391/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11159/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62857/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58949/100000 : ℝ) ∧ (39989/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (5273/6250 : ℝ) := by
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
  have lower0 : (11159/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14709/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11159/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14709/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11159/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14709/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11159/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14709/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11159/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14709/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11159/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11159/100000 : ℝ) ^ (4305/1024 : ℝ) ≤ (309720508113603/3125000000000000000 : ℝ) := by
    have hpowers : (11159/100000 : ℝ)^4305 ≤ (309720508113603/3125000000000000000 : ℝ)^1024 := by
      have hnat : (11159 : ℕ)^4305*3125000000000000000^1024 ≤ 309720508113603^1024*100000^4305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11159 100000 309720508113603 3125000000000000000 4305 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11159/100000 : ℝ)) (X := (309720508113603/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14709/100000 : ℝ) ^ (4305/1024 : ℝ) ≤ (31654467471717473/100000000000000000000 : ℝ) := by
    have hpowers : (14709/100000 : ℝ)^4305 ≤ (31654467471717473/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14709 : ℕ)^4305*100000000000000000000^1024 ≤ 31654467471717473^1024*100000^4305 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14709 100000 31654467471717473 100000000000000000000 4305 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14709/100000 : ℝ)) (X := (31654467471717473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562809720508113603/1562500000000000000 : ℝ) ≤ (1000047145900543/1000000000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (1562809720508113603/1562500000000000000 : ℝ)^1024 ≤ (1000047145900543/1000000000000000 : ℝ)^4305 := by
      have hnat : (1562809720508113603 : ℕ)^1024*1000000000000000^4305 ≤ 1000047145900543^4305*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562809720508113603 1562500000000000000 1000047145900543 1000000000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000047145900543/1000000000000000 : ℝ)) (X := (1562809720508113603/1562500000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041565523731352769/100000000000000000000 : ℝ) ≤ (625061783327881/625000000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (100041565523731352769/100000000000000000000 : ℝ)^1024 ≤ (625061783327881/625000000000000 : ℝ)^4305 := by
      have hnat : (100041565523731352769 : ℕ)^1024*625000000000000^4305 ≤ 625061783327881^4305*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041565523731352769 100000000000000000000 625061783327881 625000000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625061783327881/625000000000000 : ℝ)) (X := (100041565523731352769/100000000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031654467471717473/50000000000000000000 : ℝ) ≤ (5000752803743381/5000000000000000 : ℝ) ^ (4305/1024 : ℝ) := by
    have hpowers : (50031654467471717473/50000000000000000000 : ℝ)^1024 ≤ (5000752803743381/5000000000000000 : ℝ)^4305 := by
      have hnat : (50031654467471717473 : ℕ)^1024*5000000000000000^4305 ≤ 5000752803743381^4305*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031654467471717473 50000000000000000000 5000752803743381 5000000000000000 1024 4305 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000752803743381/5000000000000000 : ℝ)) (X := (50031654467471717473/50000000000000000000 : ℝ)) (by norm_num) 4305 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(309720508113603/3125000000000000000 : ℝ) ≤ ((4436266702070761589/4437500000000000000 : ℝ)+2*(258537120333/177500000000000 : ℝ)*(11159/100000 : ℝ))^(4305/1024 : ℝ) := by
    rw [show (4436266702070761589/4437500000000000000 : ℝ)+2*(258537120333/177500000000000 : ℝ)*(11159/100000 : ℝ)=(1000047145900543/1000000000000000 : ℝ) by norm_num, show 1+2*(309720508113603/3125000000000000000 : ℝ)=(1562809720508113603/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31654467471717473/100000000000000000000 : ℝ)+(309720508113603/3125000000000000000 : ℝ) ≤ ((4436266702070761589/4437500000000000000 : ℝ)+(258537120333/177500000000000 : ℝ)*((14709/100000 : ℝ)+(11159/100000 : ℝ)))^(4305/1024 : ℝ) := by
    rw [show (4436266702070761589/4437500000000000000 : ℝ)+(258537120333/177500000000000 : ℝ)*((14709/100000 : ℝ)+(11159/100000 : ℝ))=(625061783327881/625000000000000 : ℝ) by norm_num, show 1+(31654467471717473/100000000000000000000 : ℝ)+(309720508113603/3125000000000000000 : ℝ)=(100041565523731352769/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31654467471717473/100000000000000000000 : ℝ) ≤ ((4436266702070761589/4437500000000000000 : ℝ)+2*(258537120333/177500000000000 : ℝ)*(14709/100000 : ℝ))^(4305/1024 : ℝ) := by
    rw [show (4436266702070761589/4437500000000000000 : ℝ)+2*(258537120333/177500000000000 : ℝ)*(14709/100000 : ℝ)=(5000752803743381/5000000000000000 : ℝ) by norm_num, show 1+2*(31654467471717473/100000000000000000000 : ℝ)=(50031654467471717473/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4436266702070761589/4437500000000000000 : ℝ)*(X 1 0+X 2 0)+(258537120333/177500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (11159/100000 : ℝ)) (hi := (14709/100000 : ℝ)) (c := (4436266702070761589/4437500000000000000 : ℝ)) (alpha := (258537120333/177500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4436266702070761589/4437500000000000000 : ℝ)*(X 0 1+X 2 1)+(258537120333/177500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (11159/100000 : ℝ)) (hi := (14709/100000 : ℝ)) (c := (4436266702070761589/4437500000000000000 : ℝ)) (alpha := (258537120333/177500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4436266702070761589/4437500000000000000 : ℝ)*(X 0 2+X 1 2)+(258537120333/177500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4305/1024 : ℝ)) (lo := (11159/100000 : ℝ)) (hi := (14709/100000 : ℝ)) (c := (4436266702070761589/4437500000000000000 : ℝ)) (alpha := (258537120333/177500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-374716107/2000000000 : ℝ)*X 0 0+(1077954961/2000000000 : ℝ)*X 0 1+(2694887389/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285217959/10000000000 : ℝ)*X 1 0+(-201684749/1000000000 : ℝ)*X 1 1+(5389774699/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1321304491/2500000000 : ℝ)*X 2 0+(1347443689/2500000000 : ℝ)*X 2 1+(-1008423703/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((279604797/625000000 : ℝ)*X 0 0+(425540773/1000000000 : ℝ)*X 0 1+(4255407729/10000000000 : ℝ)*X 0 2+(279604797/625000000 : ℝ)*X 1 0+(425540773/1000000000 : ℝ)*X 1 1+(4255407729/10000000000 : ℝ)*X 1 2+(279604797/625000000 : ℝ)*X 2 0+(425540773/1000000000 : ℝ)*X 2 1+(4255407729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1105107883/5000000000 : ℝ)*X 0 0+(1053002491/2000000000 : ℝ)*X 0 1+(2632506679/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5372833229/10000000000 : ℝ)*X 1 0+(-1033469257/5000000000 : ℝ)*X 1 1+(5265013111/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1074566691/2000000000 : ℝ)*X 2 0+(5265012951/10000000000 : ℝ)*X 2 1+(-258367303/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4176545867/10000000000 : ℝ)*X 0 0+(1100980127/2500000000 : ℝ)*X 0 1+(4403918909/10000000000 : ℝ)*X 0 2+(4176545867/10000000000 : ℝ)*X 1 0+(1100980127/2500000000 : ℝ)*X 1 1+(4403918909/10000000000 : ℝ)*X 1 2+(4176545867/10000000000 : ℝ)*X 2 0+(1100980127/2500000000 : ℝ)*X 2 1+(4403918909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-53487807/250000000 : ℝ)*X 0 0+(2589552047/5000000000 : ℝ)*X 0 1+(540379327/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1055073581/2000000000 : ℝ)*X 1 0+(-251385869/1250000000 : ℝ)*X 1 1+(1080758673/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1318841997/2500000000 : ℝ)*X 2 0+(1080758661/2000000000 : ℝ)*X 2 1+(-1005543461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((11266259/25000000 : ℝ)*X 0 0+(1059676719/2500000000 : ℝ)*X 0 1+(264919177/625000000 : ℝ)*X 0 2+(11266259/25000000 : ℝ)*X 1 0+(1059676719/2500000000 : ℝ)*X 1 1+(264919177/625000000 : ℝ)*X 1 2+(11266259/25000000 : ℝ)*X 2 0+(1059676719/2500000000 : ℝ)*X 2 1+(264919177/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-972307017/5000000000 : ℝ)*X 0 0+(1368371773/2500000000 : ℝ)*X 0 1+(525393967/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((538060731/1000000000 : ℝ)*X 1 0+(-1035640307/5000000000 : ℝ)*X 1 1+(5253939819/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5380608001/10000000000 : ℝ)*X 2 0+(5253939353/10000000000 : ℝ)*X 2 1+(-2071280307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((518715851/1250000000 : ℝ)*X 0 0+(1104272387/2500000000 : ℝ)*X 0 1+(4417090257/10000000000 : ℝ)*X 0 2+(518715851/1250000000 : ℝ)*X 1 0+(1104272387/2500000000 : ℝ)*X 1 1+(4417090257/10000000000 : ℝ)*X 1 2+(518715851/1250000000 : ℝ)*X 2 0+(1104272387/2500000000 : ℝ)*X 2 1+(4417090257/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1346_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62857/100000 : ℝ) ≤ (-139458294562359513174173789940561/221875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21312323/20000000000000 : ℝ)*(lower0) + (154243571/100000000000000 : ℝ)*(upper1) + (80476517/100000000000000 : ℝ)*(lower2) + (2925033095545217/100000000000000 : ℝ)*(major0) + (2925033095545217/100000000000000 : ℝ)*(major1) + (2925033095545217/100000000000000 : ℝ)*(major2) + (508507521/50000000000000 : ℝ)*(sp3) + (3982511483893793/100000000000000 : ℝ)*(sp4) + (3982461024129629/100000000000000 : ℝ)*(sp5) + (3982473283035077/100000000000000 : ℝ)*(sp6) + (1888502954276779/100000000000000 : ℝ)*(sp7) + (2216778029/100000000000000 : ℝ)*(sp12) + (3292283887/6250000000000 : ℝ)*(sp13) + (8083527349/20000000000000 : ℝ)*(sp14) + (944251985645911/50000000000000 : ℝ)*(f.failure) + (1991256850335911/50000000000000 : ℝ)*(f.sum) + (26761280469693/4437500000000000000000000000 : ℝ)*base65 + (2617105402223455187/443750000000000000000000000000000 : ℝ)*base68 + (1870282662460955187/443750000000000000000000000000000 : ℝ)*base70 + (177163627679705187/443750000000000000000000000000000 : ℝ)*base72 + (258302228465011/8875000000000000000000000000 : ℝ)*base73 + (44449001582794813/443750000000000000000000000000000 : ℝ)*base75 + (1068849174860955187/443750000000000000000000000000000 : ℝ)*base78 + (2173746186782794813/443750000000000000000000000000000 : ℝ)*base79 + (8449503400989/8875000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2906201/312500000000000000000 : ℝ)*base89 + (2906201/312500000000000000000 : ℝ)*base91 + (2906201/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (58949/100000 : ℝ) ≤ (26159679061012672037883636091053/44375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3158383/20000000000000 : ℝ)*(lower1) + (142919/2500000000000 : ℝ)*(lower2) + (26924623/100000000000000 : ℝ)*(upper4) + (598771628424459/20000000000000 : ℝ)*(major0) + (598771628424459/20000000000000 : ℝ)*(major1) + (598771628424459/20000000000000 : ℝ)*(major2) + (63048832614509/1562500000000 : ℝ)*(sp0) + (4035091283095217/100000000000000 : ℝ)*(sp1) + (4035122373067451/100000000000000 : ℝ)*(sp2) + (120808609717611/6250000000000 : ℝ)*(sp3) + (1040068441/50000000000000 : ℝ)*(sp7) + (174538231/25000000000000 : ℝ)*(sp8) + (34702386283/100000000000000 : ℝ)*(sp9) + (3612414049/100000000000000 : ℝ)*(sp10) + (966469917809329/50000000000000 : ℝ)*(f.failure) + (8070251970963/200000000000 : ℝ)*(f.sum) + (506464049803/1775000000000000000000000000 : ℝ)*base66 + (81911411733519649/88750000000000000000000000000000 : ℝ)*base68 + (85948298968980351/88750000000000000000000000000000 : ℝ)*base69 + (766465401523519649/88750000000000000000000000000000 : ℝ)*base72 + (6761262047597/1775000000000000000000000000 : ℝ)*base73 + (683642832618519649/88750000000000000000000000000000 : ℝ)*base76 + (382039122203980351/88750000000000000000000000000000 : ℝ)*base77 + (343849081627269649/88750000000000000000000000000000 : ℝ)*base80 + (6272260080603/1775000000000000000000000000 : ℝ)*base82 + (3707361/312500000000000000000 : ℝ)*base90 + (3707361/312500000000000000000 : ℝ)*base92 + (3707361/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (39989/50000 : ℝ) ≤ (88728053908487072518304997577953/110937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12959617/100000000000000 : ℝ)*(upper0) + (2223639/25000000000000 : ℝ)*(upper3) + (9190381/25000000000000 : ℝ)*(upper4) + (1652897711999841/50000000000000 : ℝ)*(major0) + (1652897711999841/50000000000000 : ℝ)*(major1) + (1652897711999841/50000000000000 : ℝ)*(major2) + (25797879/6250000000000 : ℝ)*(sp0) + (24228208729/100000000000000 : ℝ)*(sp1) + (12023641503/50000000000000 : ℝ)*(sp2) + (1730473623/50000000000000 : ℝ)*(sp3) + (2225296437854869/50000000000000 : ℝ)*(sp8) + (2225284530133537/50000000000000 : ℝ)*(sp9) + (1112642310298199/25000000000000 : ℝ)*(sp10) + (2134334026040419/100000000000000 : ℝ)*(sp11) + (426867497397533/20000000000000 : ℝ)*(f.failure) + (2225296644237901/50000000000000 : ℝ)*(f.sum) + (4960809970053/4437500000000000000000000000 : ℝ)*base65 + (3647494352930732349/221875000000000000000000000000000 : ℝ)*base67 + (5408271875517651/221875000000000000000000000000000 : ℝ)*base70 + (731084512528642651/221875000000000000000000000000000 : ℝ)*base72 + (3285564258933/277343750000000000000000000 : ℝ)*base73 + (77813817002607349/221875000000000000000000000000000 : ℝ)*base75 + (635996047718232349/221875000000000000000000000000000 : ℝ)*base77 + (12960044627605732349/221875000000000000000000000000000 : ℝ)*base79 + (13906892196911/2218750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (624597/125000000000000000000 : ℝ)*base90 + (624597/125000000000000000000 : ℝ)*base92 + (624597/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-5273/6250 : ℝ) ≤ (-46796332302077106493816703871981/55468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (687399/2500000000000 : ℝ)*(lower0) + (33142371/10000000000000 : ℝ)*(lower1) + (36847987/12500000000000 : ℝ)*(lower2) + (1671163574568543/50000000000000 : ℝ)*(major0) + (1671163574568543/50000000000000 : ℝ)*(major1) + (1671163574568543/50000000000000 : ℝ)*(major2) + (4462382933/20000000000000 : ℝ)*(sp0) + (255854601871/50000000000000 : ℝ)*(sp5) + (537347496797/100000000000000 : ℝ)*(sp6) + (51457263323/50000000000000 : ℝ)*(sp7) + (1138707518939107/25000000000000 : ℝ)*(sp12) + (4554340678467351/100000000000000 : ℝ)*(sp13) + (569289380021787/12500000000000 : ℝ)*(sp14) + (2157820735675787/100000000000000 : ℝ)*(sp15) + (2157923650202433/100000000000000 : ℝ)*(f.failure) + (4554852387671093/100000000000000 : ℝ)*(f.sum) + (61233388682987/8875000000000000000000000000 : ℝ)*base66 + (1837665534165694827/221875000000000000000000000000000 : ℝ)*base67 + (1653375835671944827/221875000000000000000000000000000 : ℝ)*base69 + (1562967519068819827/221875000000000000000000000000000 : ℝ)*base71 + (99602573303903/2218750000000000000000000000 : ℝ)*base74 + (1724688080137569827/221875000000000000000000000000000 : ℝ)*base75 + (146649045903194827/221875000000000000000000000000000 : ℝ)*base77 + (4784958363065555173/221875000000000000000000000000000 : ℝ)*base80 + (26272992871763/8875000000000000000000000000 : ℝ)*base81 + (6908697/625000000000000000000 : ℝ)*base90 + (6908697/625000000000000000000 : ℝ)*base92 + (6908697/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1346_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9680391/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11159/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62857/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58949/100000 : ℝ) else (39989/50000 : ℝ) ≤ X j i ∧ X j i ≤ (5273/6250 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1346_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1346_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9680391/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7359/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11151/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62857/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58949/100000 : ℝ) else (39989/50000 : ℝ) ≤ X j i ∧ X j i ≤ (5273/6250 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1346_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1346_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1346_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4305/1024 : ℝ) ≤ p) (hpb : p ≤ (2153/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9680391/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7359/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11151/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62857/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58949/100000 : ℝ) else (39989/50000 : ℝ) ≤ X j i ∧ X j i ≤ (5273/6250 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1346_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
