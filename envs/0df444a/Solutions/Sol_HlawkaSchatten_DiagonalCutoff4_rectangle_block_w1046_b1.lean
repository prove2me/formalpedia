-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1046_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:51:25.595324+00:00
-- url     : https://prove2.me/submissions/64a0e2a1-8638-4164-a3b2-491179cef927

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
theorem support_rectangle_w1046_s3_0 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-88345203/400000000 : ℝ)*x 0 + (217596611/400000000 : ℝ)*x 1 + (326384561/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88345203/400000000 : ℝ)^8239 ≤ (13401612050541/100000000000000 : ℝ)^6191 := by
    have hnat : (88345203 : ℕ)^8239*100000000000000^6191 ≤ 13401612050541^6191*400000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88345203 400000000 13401612050541 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217596611/400000000 : ℝ)^8239 ≤ (5559494343277/12500000000000 : ℝ)^6191 := by
    have hnat : (217596611 : ℕ)^8239*12500000000000^6191 ≤ 5559494343277^6191*400000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217596611 400000000 5559494343277 12500000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326384561/625000000 : ℝ)^8239 ≤ (5265304149121/12500000000000 : ℝ)^6191 := by
    have hnat : (326384561 : ℕ)^8239*12500000000000^6191 ≤ 5265304149121^6191*625000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326384561 625000000 5265304149121 12500000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-88345203/400000000 : ℝ), (217596611/400000000 : ℝ), (326384561/625000000 : ℝ)] ![(13401612050541/100000000000000 : ℝ), (5559494343277/12500000000000 : ℝ), (5265304149121/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-88345203/400000000 : ℝ)|^8239 ≤ (13401612050541/100000000000000 : ℝ)^6191
        have hw : |(-88345203/400000000 : ℝ)|=(88345203/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217596611/400000000 : ℝ)|^8239 ≤ (5559494343277/12500000000000 : ℝ)^6191
        have hw : |(217596611/400000000 : ℝ)|=(217596611/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326384561/625000000 : ℝ)|^8239 ≤ (5265304149121/12500000000000 : ℝ)^6191
        have hw : |(326384561/625000000 : ℝ)|=(326384561/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s3_1 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5356214781/10000000000 : ℝ)*x 0 + (-2320198667/10000000000 : ℝ)*x 1 + (2611076569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356214781/10000000000 : ℝ)^8239 ≤ (21783790702149/50000000000000 : ℝ)^6191 := by
    have hnat : (5356214781 : ℕ)^8239*50000000000000^6191 ≤ 21783790702149^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356214781 10000000000 21783790702149 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2320198667/10000000000 : ℝ)^8239 ≤ (111796747237/781250000000 : ℝ)^6191 := by
    have hnat : (2320198667 : ℕ)^8239*781250000000^6191 ≤ 111796747237^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2320198667 10000000000 111796747237 781250000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2611076569/5000000000 : ℝ)^8239 ≤ (2106121746597/5000000000000 : ℝ)^6191 := by
    have hnat : (2611076569 : ℕ)^8239*5000000000000^6191 ≤ 2106121746597^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611076569 5000000000 2106121746597 5000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356214781/10000000000 : ℝ), (-2320198667/10000000000 : ℝ), (2611076569/5000000000 : ℝ)] ![(21783790702149/50000000000000 : ℝ), (111796747237/781250000000 : ℝ), (2106121746597/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356214781/10000000000 : ℝ)|^8239 ≤ (21783790702149/50000000000000 : ℝ)^6191
        have hw : |(5356214781/10000000000 : ℝ)|=(5356214781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2320198667/10000000000 : ℝ)|^8239 ≤ (111796747237/781250000000 : ℝ)^6191
        have hw : |(-2320198667/10000000000 : ℝ)|=(2320198667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2611076569/5000000000 : ℝ)|^8239 ≤ (2106121746597/5000000000000 : ℝ)^6191
        have hw : |(2611076569/5000000000 : ℝ)|=(2611076569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s3_2 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5356214817/10000000000 : ℝ)*x 0 + (5222153317/10000000000 : ℝ)*x 1 + (-1160099193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356214817/10000000000 : ℝ)^8239 ≤ (4356758179399/10000000000000 : ℝ)^6191 := by
    have hnat : (5356214817 : ℕ)^8239*10000000000000^6191 ≤ 4356758179399^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356214817 10000000000 4356758179399 10000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5222153317/10000000000 : ℝ)^8239 ≤ (42122436853397/100000000000000 : ℝ)^6191 := by
    have hnat : (5222153317 : ℕ)^8239*100000000000000^6191 ≤ 42122436853397^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5222153317 10000000000 42122436853397 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1160099193/5000000000 : ℝ)^8239 ≤ (715499066997/5000000000000 : ℝ)^6191 := by
    have hnat : (1160099193 : ℕ)^8239*5000000000000^6191 ≤ 715499066997^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1160099193 5000000000 715499066997 5000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356214817/10000000000 : ℝ), (5222153317/10000000000 : ℝ), (-1160099193/5000000000 : ℝ)] ![(4356758179399/10000000000000 : ℝ), (42122436853397/100000000000000 : ℝ), (715499066997/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356214817/10000000000 : ℝ)|^8239 ≤ (4356758179399/10000000000000 : ℝ)^6191
        have hw : |(5356214817/10000000000 : ℝ)|=(5356214817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5222153317/10000000000 : ℝ)|^8239 ≤ (42122436853397/100000000000000 : ℝ)^6191
        have hw : |(5222153317/10000000000 : ℝ)|=(5222153317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1160099193/5000000000 : ℝ)|^8239 ≤ (715499066997/5000000000000 : ℝ)^6191
        have hw : |(-1160099193/5000000000 : ℝ)|=(1160099193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s3_3 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187705151/5000000000 : ℝ)*x 0 + (208405601/500000000 : ℝ)*x 1 + (4593200857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187705151/5000000000 : ℝ)^8239 ≤ (1331455920353/4000000000000 : ℝ)^6191 := by
    have hnat : (2187705151 : ℕ)^8239*4000000000000^6191 ≤ 1331455920353^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187705151 5000000000 1331455920353 4000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208405601/500000000 : ℝ)^8239 ≤ (31204287750511/100000000000000 : ℝ)^6191 := by
    have hnat : (208405601 : ℕ)^8239*100000000000000^6191 ≤ 31204287750511^6191*500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208405601 500000000 31204287750511 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4593200857/10000000000 : ℝ)^8239 ≤ (35509314227481/100000000000000 : ℝ)^6191 := by
    have hnat : (4593200857 : ℕ)^8239*100000000000000^6191 ≤ 35509314227481^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4593200857 10000000000 35509314227481 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187705151/5000000000 : ℝ), (208405601/500000000 : ℝ), (4593200857/10000000000 : ℝ)] ![(1331455920353/4000000000000 : ℝ), (31204287750511/100000000000000 : ℝ), (35509314227481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187705151/5000000000 : ℝ)|^8239 ≤ (1331455920353/4000000000000 : ℝ)^6191
        have hw : |(2187705151/5000000000 : ℝ)|=(2187705151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208405601/500000000 : ℝ)|^8239 ≤ (31204287750511/100000000000000 : ℝ)^6191
        have hw : |(208405601/500000000 : ℝ)|=(208405601/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4593200857/10000000000 : ℝ)|^8239 ≤ (35509314227481/100000000000000 : ℝ)^6191
        have hw : |(4593200857/10000000000 : ℝ)|=(4593200857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s3_4 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-441730777/2000000000 : ℝ)*x 0 + (5223058679/10000000000 : ℝ)*x 1 + (5439004007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (441730777/2000000000 : ℝ)^8239 ≤ (3350451079737/25000000000000 : ℝ)^6191 := by
    have hnat : (441730777 : ℕ)^8239*25000000000000^6191 ≤ 3350451079737^6191*2000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441730777 2000000000 3350451079737 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5223058679/10000000000 : ℝ)^8239 ≤ (8426431129063/20000000000000 : ℝ)^6191 := by
    have hnat : (5223058679 : ℕ)^8239*20000000000000^6191 ≤ 8426431129063^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223058679 10000000000 8426431129063 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439004007/10000000000 : ℝ)^8239 ≤ (4446604001537/10000000000000 : ℝ)^6191 := by
    have hnat : (5439004007 : ℕ)^8239*10000000000000^6191 ≤ 4446604001537^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439004007 10000000000 4446604001537 10000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-441730777/2000000000 : ℝ), (5223058679/10000000000 : ℝ), (5439004007/10000000000 : ℝ)] ![(3350451079737/25000000000000 : ℝ), (8426431129063/20000000000000 : ℝ), (4446604001537/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-441730777/2000000000 : ℝ)|^8239 ≤ (3350451079737/25000000000000 : ℝ)^6191
        have hw : |(-441730777/2000000000 : ℝ)|=(441730777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5223058679/10000000000 : ℝ)|^8239 ≤ (8426431129063/20000000000000 : ℝ)^6191
        have hw : |(5223058679/10000000000 : ℝ)|=(5223058679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439004007/10000000000 : ℝ)|^8239 ≤ (4446604001537/10000000000000 : ℝ)^6191
        have hw : |(5439004007/10000000000 : ℝ)|=(5439004007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s3_5 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2650723553/5000000000 : ℝ)*x 0 + (-420669697/2000000000 : ℝ)*x 1 + (543900337/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650723553/5000000000 : ℝ)^8239 ≤ (10743934549267/25000000000000 : ℝ)^6191 := by
    have hnat : (2650723553 : ℕ)^8239*25000000000000^6191 ≤ 10743934549267^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650723553 5000000000 10743934549267 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (420669697/2000000000 : ℝ)^8239 ≤ (6279114349837/50000000000000 : ℝ)^6191 := by
    have hnat : (420669697 : ℕ)^8239*50000000000000^6191 ≤ 6279114349837^6191*2000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420669697 2000000000 6279114349837 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543900337/1000000000 : ℝ)^8239 ≤ (11116508271227/25000000000000 : ℝ)^6191 := by
    have hnat : (543900337 : ℕ)^8239*25000000000000^6191 ≤ 11116508271227^6191*1000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543900337 1000000000 11116508271227 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650723553/5000000000 : ℝ), (-420669697/2000000000 : ℝ), (543900337/1000000000 : ℝ)] ![(10743934549267/25000000000000 : ℝ), (6279114349837/50000000000000 : ℝ), (11116508271227/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650723553/5000000000 : ℝ)|^8239 ≤ (10743934549267/25000000000000 : ℝ)^6191
        have hw : |(2650723553/5000000000 : ℝ)|=(2650723553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-420669697/2000000000 : ℝ)|^8239 ≤ (6279114349837/50000000000000 : ℝ)^6191
        have hw : |(-420669697/2000000000 : ℝ)|=(420669697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543900337/1000000000 : ℝ)|^8239 ≤ (11116508271227/25000000000000 : ℝ)^6191
        have hw : |(543900337/1000000000 : ℝ)|=(543900337/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s3_6 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (165670211/312500000 : ℝ)*x 0 + (2719501933/5000000000 : ℝ)*x 1 + (-2103348287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165670211/312500000 : ℝ)^8239 ≤ (21487867189051/50000000000000 : ℝ)^6191 := by
    have hnat : (165670211 : ℕ)^8239*50000000000000^6191 ≤ 21487867189051^6191*312500000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165670211 312500000 21487867189051 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719501933/5000000000 : ℝ)^8239 ≤ (1389563702541/3125000000000 : ℝ)^6191 := by
    have hnat : (2719501933 : ℕ)^8239*3125000000000^6191 ≤ 1389563702541^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719501933 5000000000 1389563702541 3125000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2103348287/10000000000 : ℝ)^8239 ≤ (12558227126431/100000000000000 : ℝ)^6191 := by
    have hnat : (2103348287 : ℕ)^8239*100000000000000^6191 ≤ 12558227126431^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103348287 10000000000 12558227126431 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165670211/312500000 : ℝ), (2719501933/5000000000 : ℝ), (-2103348287/10000000000 : ℝ)] ![(21487867189051/50000000000000 : ℝ), (1389563702541/3125000000000 : ℝ), (12558227126431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165670211/312500000 : ℝ)|^8239 ≤ (21487867189051/50000000000000 : ℝ)^6191
        have hw : |(165670211/312500000 : ℝ)|=(165670211/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719501933/5000000000 : ℝ)|^8239 ≤ (1389563702541/3125000000000 : ℝ)^6191
        have hw : |(2719501933/5000000000 : ℝ)|=(2719501933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2103348287/10000000000 : ℝ)|^8239 ≤ (12558227126431/100000000000000 : ℝ)^6191
        have hw : |(-2103348287/10000000000 : ℝ)|=(2103348287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s3_7 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (437545621/1000000000 : ℝ)*x 0 + (4591432471/10000000000 : ℝ)*x 1 + (2084945623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437545621/1000000000 : ℝ)^8239 ≤ (1331474511699/4000000000000 : ℝ)^6191 := by
    have hnat : (437545621 : ℕ)^8239*4000000000000^6191 ≤ 1331474511699^6191*1000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437545621 1000000000 1331474511699 4000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4591432471/10000000000 : ℝ)^8239 ≤ (35491121829181/100000000000000 : ℝ)^6191 := by
    have hnat : (4591432471 : ℕ)^8239*100000000000000^6191 ≤ 35491121829181^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4591432471 10000000000 35491121829181 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084945623/5000000000 : ℝ)^8239 ≤ (15611007683871/50000000000000 : ℝ)^6191 := by
    have hnat : (2084945623 : ℕ)^8239*50000000000000^6191 ≤ 15611007683871^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084945623 5000000000 15611007683871 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(437545621/1000000000 : ℝ), (4591432471/10000000000 : ℝ), (2084945623/5000000000 : ℝ)] ![(1331474511699/4000000000000 : ℝ), (35491121829181/100000000000000 : ℝ), (15611007683871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(437545621/1000000000 : ℝ)|^8239 ≤ (1331474511699/4000000000000 : ℝ)^6191
        have hw : |(437545621/1000000000 : ℝ)|=(437545621/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4591432471/10000000000 : ℝ)|^8239 ≤ (35491121829181/100000000000000 : ℝ)^6191
        have hw : |(4591432471/10000000000 : ℝ)|=(4591432471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2084945623/5000000000 : ℝ)|^8239 ≤ (15611007683871/50000000000000 : ℝ)^6191
        have hw : |(2084945623/5000000000 : ℝ)|=(2084945623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1046_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2101/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8613/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1291/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1867/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2101/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8613/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2101/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8613/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2101/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8613/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2101/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8613/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2101/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8613/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2101/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8613/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8613/100000 : ℝ) ^ (4119/1024 : ℝ) ≤ (5208352379584433/100000000000000000000 : ℝ) := by
    have hpowers : (8613/100000 : ℝ)^4119 ≤ (5208352379584433/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8613 : ℕ)^4119*100000000000000000000^1024 ≤ 5208352379584433^1024*100000^4119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8613 100000 5208352379584433 100000000000000000000 4119 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8613/100000 : ℝ)) (X := (5208352379584433/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2101/12500 : ℝ) ^ (4119/1024 : ℝ) ≤ (76677601890212597/100000000000000000000 : ℝ) := by
    have hpowers : (2101/12500 : ℝ)^4119 ≤ (76677601890212597/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2101 : ℕ)^4119*100000000000000000000^1024 ≤ 76677601890212597^1024*12500^4119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2101 12500 76677601890212597 100000000000000000000 4119 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2101/12500 : ℝ)) (X := (76677601890212597/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005208352379584433/50000000000000000000 : ℝ) ≤ (1250032369168043/1250000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (50005208352379584433/50000000000000000000 : ℝ)^1024 ≤ (1250032369168043/1250000000000000 : ℝ)^4119 := by
      have hnat : (50005208352379584433 : ℕ)^1024*1250000000000000^4119 ≤ 1250032369168043^4119*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005208352379584433 50000000000000000000 1250032369168043 1250000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250032369168043/1250000000000000 : ℝ)) (X := (50005208352379584433/50000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10008188595426979703/10000000000000000000 : ℝ) ≤ (5001017545923567/5000000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (10008188595426979703/10000000000000000000 : ℝ)^1024 ≤ (5001017545923567/5000000000000000 : ℝ)^4119 := by
      have hnat : (10008188595426979703 : ℕ)^1024*5000000000000000^4119 ≤ 5001017545923567^4119*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10008188595426979703 10000000000000000000 5001017545923567 5000000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001017545923567/5000000000000000 : ℝ)) (X := (10008188595426979703/10000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50076677601890212597/50000000000000000000 : ℝ) ≤ (2500952807587481/2500000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (50076677601890212597/50000000000000000000 : ℝ)^1024 ≤ (2500952807587481/2500000000000000 : ℝ)^4119 := by
      have hnat : (50076677601890212597 : ℕ)^1024*2500000000000000^4119 ≤ 2500952807587481^4119*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50076677601890212597 50000000000000000000 2500952807587481 2500000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500952807587481/2500000000000000 : ℝ)) (X := (50076677601890212597/50000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5208352379584433/100000000000000000000 : ℝ) ≤ ((372370574367308357/372500000000000000 : ℝ)+2*(177613850279/81950000000000 : ℝ)*(8613/100000 : ℝ))^(4119/1024 : ℝ) := by
    rw [show (372370574367308357/372500000000000000 : ℝ)+2*(177613850279/81950000000000 : ℝ)*(8613/100000 : ℝ)=(1250032369168043/1250000000000000 : ℝ) by norm_num, show 1+2*(5208352379584433/100000000000000000000 : ℝ)=(50005208352379584433/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(76677601890212597/100000000000000000000 : ℝ)+(5208352379584433/100000000000000000000 : ℝ) ≤ ((372370574367308357/372500000000000000 : ℝ)+(177613850279/81950000000000 : ℝ)*((2101/12500 : ℝ)+(8613/100000 : ℝ)))^(4119/1024 : ℝ) := by
    rw [show (372370574367308357/372500000000000000 : ℝ)+(177613850279/81950000000000 : ℝ)*((2101/12500 : ℝ)+(8613/100000 : ℝ))=(5001017545923567/5000000000000000 : ℝ) by norm_num, show 1+(76677601890212597/100000000000000000000 : ℝ)+(5208352379584433/100000000000000000000 : ℝ)=(10008188595426979703/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(76677601890212597/100000000000000000000 : ℝ) ≤ ((372370574367308357/372500000000000000 : ℝ)+2*(177613850279/81950000000000 : ℝ)*(2101/12500 : ℝ))^(4119/1024 : ℝ) := by
    rw [show (372370574367308357/372500000000000000 : ℝ)+2*(177613850279/81950000000000 : ℝ)*(2101/12500 : ℝ)=(2500952807587481/2500000000000000 : ℝ) by norm_num, show 1+2*(76677601890212597/100000000000000000000 : ℝ)=(50076677601890212597/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (372370574367308357/372500000000000000 : ℝ)*(X 1 0+X 2 0)+(177613850279/81950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (8613/100000 : ℝ)) (hi := (2101/12500 : ℝ)) (c := (372370574367308357/372500000000000000 : ℝ)) (alpha := (177613850279/81950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (372370574367308357/372500000000000000 : ℝ)*(X 0 1+X 2 1)+(177613850279/81950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (8613/100000 : ℝ)) (hi := (2101/12500 : ℝ)) (c := (372370574367308357/372500000000000000 : ℝ)) (alpha := (177613850279/81950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (372370574367308357/372500000000000000 : ℝ)*(X 0 2+X 1 2)+(177613850279/81950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (8613/100000 : ℝ)) (hi := (2101/12500 : ℝ)) (c := (372370574367308357/372500000000000000 : ℝ)) (alpha := (177613850279/81950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-88345203/400000000 : ℝ)*X 0 0+(217596611/400000000 : ℝ)*X 0 1+(326384561/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356214781/10000000000 : ℝ)*X 1 0+(-2320198667/10000000000 : ℝ)*X 1 1+(2611076569/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5356214817/10000000000 : ℝ)*X 2 0+(5222153317/10000000000 : ℝ)*X 2 1+(-1160099193/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2187705151/5000000000 : ℝ)*X 0 0+(208405601/500000000 : ℝ)*X 0 1+(4593200857/10000000000 : ℝ)*X 0 2+(2187705151/5000000000 : ℝ)*X 1 0+(208405601/500000000 : ℝ)*X 1 1+(4593200857/10000000000 : ℝ)*X 1 2+(2187705151/5000000000 : ℝ)*X 2 0+(208405601/500000000 : ℝ)*X 2 1+(4593200857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-441730777/2000000000 : ℝ)*X 0 0+(5223058679/10000000000 : ℝ)*X 0 1+(5439004007/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2650723553/5000000000 : ℝ)*X 1 0+(-420669697/2000000000 : ℝ)*X 1 1+(543900337/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165670211/312500000 : ℝ)*X 2 0+(2719501933/5000000000 : ℝ)*X 2 1+(-2103348287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((437545621/1000000000 : ℝ)*X 0 0+(4591432471/10000000000 : ℝ)*X 0 1+(2084945623/5000000000 : ℝ)*X 0 2+(437545621/1000000000 : ℝ)*X 1 0+(4591432471/10000000000 : ℝ)*X 1 1+(2084945623/5000000000 : ℝ)*X 1 2+(437545621/1000000000 : ℝ)*X 2 0+(4591432471/10000000000 : ℝ)*X 2 1+(2084945623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (126686832028406056484813271/12804687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (590412639/25000000000000 : ℝ)*(base19) + (515621291/25000000000000 : ℝ)*(base23) + (44192877/25000000000000 : ℝ)*(lower2) + (39440383/20000000000000 : ℝ)*(upper3) + (10708727/5000000000000 : ℝ)*(upper5) + (108511579377611/3125000000000 : ℝ)*(major0) + (108511579377611/3125000000000 : ℝ)*(major1) + (108511579377611/3125000000000 : ℝ)*(major2) + (287012846416869/6250000000000 : ℝ)*(sp0) + (1148062387925517/25000000000000 : ℝ)*(sp1) + (4592249850867459/100000000000000 : ℝ)*(sp2) + (2352468556194623/100000000000000 : ℝ)*(sp3) + (289816767/625000000000 : ℝ)*(sp4) + (20280826999/100000000000000 : ℝ)*(sp7) + (1176244418510811/50000000000000 : ℝ)*(f.failure) + (287015744584539/6250000000000 : ℝ)*(f.sum) + (2252157750219/512187500000000000000000000 : ℝ)*base66 + (276931974341629081/25609375000000000000000000000000 : ℝ)*base68 + (148525864858191581/25609375000000000000000000000000 : ℝ)*base70 + (47442887478822353/12804687500000000000000000000000 : ℝ)*base72 + (28443656920419/8195000000000000000000000000 : ℝ)*base74 + (201854725945066581/25609375000000000000000000000000 : ℝ)*base76 + (193970313628035331/25609375000000000000000000000000 : ℝ)*base78 + (3254902613759853/12804687500000000000000000000000 : ℝ)*base80 + (36214253096729/8195000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (10546141/1250000000000000000000 : ℝ)*base89 + (10546141/1250000000000000000000 : ℝ)*base91 + (10546141/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (68055821506185640123223319/6402343750000000000000000000000 : ℝ) := by norm_num
    linear_combination (209329169/10000000000000 : ℝ)*(base19) + (458433647/25000000000000 : ℝ)*(base23) + (21723051/50000000000000 : ℝ)*(upper3) + (2380321/5000000000000 : ℝ)*(lower4) + (419456493/100000000000000 : ℝ)*(upper5) + (109422681697349/3125000000000 : ℝ)*(major0) + (109422681697349/3125000000000 : ℝ)*(major1) + (109422681697349/3125000000000 : ℝ)*(major2) + (28421502029/100000000000000 : ℝ)*(sp1) + (24536073447/100000000000000 : ℝ)*(sp2) + (463081009334817/10000000000000 : ℝ)*(sp4) + (1157694894638613/25000000000000 : ℝ)*(sp5) + (578847965442517/12500000000000 : ℝ)*(sp6) + (593060295238629/25000000000000 : ℝ)*(sp7) + (593060295238629/25000000000000 : ℝ)*(f.failure) + (463081009334817/10000000000000 : ℝ)*(f.sum) + (18359426289353/4097500000000000000000000000 : ℝ)*base66 + (5982709238054287/3201171875000000000000000000000 : ℝ)*base67 + (2107750409594551/6402343750000000000000000000000 : ℝ)*base70 + (32748813779081329/25609375000000000000000000000000 : ℝ)*base72 + (27389939427509/8195000000000000000000000000 : ℝ)*base73 + (14044631829019331/1600585937500000000000000000000 : ℝ)*base75 + (99087234036737579/25609375000000000000000000000000 : ℝ)*base78 + (24601897685487579/25609375000000000000000000000000 : ℝ)*base80 + (12716183143923/4097500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1126499/625000000000000000000 : ℝ)*base89 + (1126499/625000000000000000000 : ℝ)*base91 + (1126499/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1046_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2101/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8613/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1291/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1867/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1046_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1046_s4_0 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1106255893/5000000000 : ℝ)*x 0 + (5406953437/10000000000 : ℝ)*x 1 + (328286223/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1106255893/5000000000 : ℝ)^8239 ≤ (6716483176277/50000000000000 : ℝ)^6191 := by
    have hnat : (1106255893 : ℕ)^8239*50000000000000^6191 ≤ 6716483176277^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106255893 5000000000 6716483176277 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406953437/10000000000 : ℝ)^8239 ≤ (44117675047161/100000000000000 : ℝ)^6191 := by
    have hnat : (5406953437 : ℕ)^8239*100000000000000^6191 ≤ 44117675047161^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406953437 10000000000 44117675047161 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328286223/625000000 : ℝ)^8239 ≤ (21224679293973/50000000000000 : ℝ)^6191 := by
    have hnat : (328286223 : ℕ)^8239*50000000000000^6191 ≤ 21224679293973^6191*625000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328286223 625000000 21224679293973 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1106255893/5000000000 : ℝ), (5406953437/10000000000 : ℝ), (328286223/625000000 : ℝ)] ![(6716483176277/50000000000000 : ℝ), (44117675047161/100000000000000 : ℝ), (21224679293973/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1106255893/5000000000 : ℝ)|^8239 ≤ (6716483176277/50000000000000 : ℝ)^6191
        have hw : |(-1106255893/5000000000 : ℝ)|=(1106255893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406953437/10000000000 : ℝ)|^8239 ≤ (44117675047161/100000000000000 : ℝ)^6191
        have hw : |(5406953437/10000000000 : ℝ)|=(5406953437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328286223/625000000 : ℝ)|^8239 ≤ (21224679293973/50000000000000 : ℝ)^6191
        have hw : |(328286223/625000000 : ℝ)|=(328286223/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s4_1 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534806713/1000000000 : ℝ)*x 0 + (-286381313/1250000000 : ℝ)*x 1 + (5252579099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534806713/1000000000 : ℝ)^8239 ≤ (4347940705479/10000000000000 : ℝ)^6191 := by
    have hnat : (534806713 : ℕ)^8239*10000000000000^6191 ≤ 4347940705479^6191*1000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534806713 1000000000 4347940705479 10000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (286381313/1250000000 : ℝ)^8239 ≤ (14071239383063/100000000000000 : ℝ)^6191 := by
    have hnat : (286381313 : ℕ)^8239*100000000000000^6191 ≤ 14071239383063^6191*1250000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286381313 1250000000 14071239383063 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252579099/10000000000 : ℝ)^8239 ≤ (42449353543831/100000000000000 : ℝ)^6191 := by
    have hnat : (5252579099 : ℕ)^8239*100000000000000^6191 ≤ 42449353543831^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252579099 10000000000 42449353543831 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534806713/1000000000 : ℝ), (-286381313/1250000000 : ℝ), (5252579099/10000000000 : ℝ)] ![(4347940705479/10000000000000 : ℝ), (14071239383063/100000000000000 : ℝ), (42449353543831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534806713/1000000000 : ℝ)|^8239 ≤ (4347940705479/10000000000000 : ℝ)^6191
        have hw : |(534806713/1000000000 : ℝ)|=(534806713/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-286381313/1250000000 : ℝ)|^8239 ≤ (14071239383063/100000000000000 : ℝ)^6191
        have hw : |(-286381313/1250000000 : ℝ)|=(286381313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252579099/10000000000 : ℝ)|^8239 ≤ (42449353543831/100000000000000 : ℝ)^6191
        have hw : |(5252579099/10000000000 : ℝ)|=(5252579099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s4_2 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2674033807/5000000000 : ℝ)*x 0 + (2626289373/5000000000 : ℝ)*x 1 + (-2291050329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674033807/5000000000 : ℝ)^8239 ≤ (21739706145673/50000000000000 : ℝ)^6191 := by
    have hnat : (2674033807 : ℕ)^8239*50000000000000^6191 ≤ 21739706145673^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674033807 5000000000 21739706145673 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2626289373/5000000000 : ℝ)^8239 ≤ (424493497473/1000000000000 : ℝ)^6191 := by
    have hnat : (2626289373 : ℕ)^8239*1000000000000^6191 ≤ 424493497473^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626289373 5000000000 424493497473 1000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2291050329/10000000000 : ℝ)^8239 ≤ (14071237952689/100000000000000 : ℝ)^6191 := by
    have hnat : (2291050329 : ℕ)^8239*100000000000000^6191 ≤ 14071237952689^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2291050329 10000000000 14071237952689 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674033807/5000000000 : ℝ), (2626289373/5000000000 : ℝ), (-2291050329/10000000000 : ℝ)] ![(21739706145673/50000000000000 : ℝ), (424493497473/1000000000000 : ℝ), (14071237952689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674033807/5000000000 : ℝ)|^8239 ≤ (21739706145673/50000000000000 : ℝ)^6191
        have hw : |(2674033807/5000000000 : ℝ)|=(2674033807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2626289373/5000000000 : ℝ)|^8239 ≤ (424493497473/1000000000000 : ℝ)^6191
        have hw : |(2626289373/5000000000 : ℝ)|=(2626289373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2291050329/10000000000 : ℝ)|^8239 ≤ (14071237952689/100000000000000 : ℝ)^6191
        have hw : |(-2291050329/10000000000 : ℝ)|=(2291050329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s4_3 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (273607119/625000000 : ℝ)*x 0 + (1057419427/2500000000 : ℝ)*x 1 + (4531029703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273607119/625000000 : ℝ)^8239 ≤ (33309722220579/100000000000000 : ℝ)^6191 := by
    have hnat : (273607119 : ℕ)^8239*100000000000000^6191 ≤ 33309722220579^6191*625000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273607119 625000000 33309722220579 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057419427/2500000000 : ℝ)^8239 ≤ (31819158149613/100000000000000 : ℝ)^6191 := by
    have hnat : (1057419427 : ℕ)^8239*100000000000000^6191 ≤ 31819158149613^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057419427 2500000000 31819158149613 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4531029703/10000000000 : ℝ)^8239 ≤ (17435559807319/50000000000000 : ℝ)^6191 := by
    have hnat : (4531029703 : ℕ)^8239*50000000000000^6191 ≤ 17435559807319^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4531029703 10000000000 17435559807319 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273607119/625000000 : ℝ), (1057419427/2500000000 : ℝ), (4531029703/10000000000 : ℝ)] ![(33309722220579/100000000000000 : ℝ), (31819158149613/100000000000000 : ℝ), (17435559807319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273607119/625000000 : ℝ)|^8239 ≤ (33309722220579/100000000000000 : ℝ)^6191
        have hw : |(273607119/625000000 : ℝ)|=(273607119/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1057419427/2500000000 : ℝ)|^8239 ≤ (31819158149613/100000000000000 : ℝ)^6191
        have hw : |(1057419427/2500000000 : ℝ)|=(1057419427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4531029703/10000000000 : ℝ)|^8239 ≤ (17435559807319/50000000000000 : ℝ)^6191
        have hw : |(4531029703/10000000000 : ℝ)|=(4531029703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s4_4 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2212520337/10000000000 : ℝ)*x 0 + (1050607051/2000000000 : ℝ)*x 1 + (135162393/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2212520337/10000000000 : ℝ)^8239 ≤ (3358258860719/25000000000000 : ℝ)^6191 := by
    have hnat : (2212520337 : ℕ)^8239*25000000000000^6191 ≤ 3358258860719^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212520337 10000000000 3358258860719 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050607051/2000000000 : ℝ)^8239 ≤ (42454259592003/100000000000000 : ℝ)^6191 := by
    have hnat : (1050607051 : ℕ)^8239*100000000000000^6191 ≤ 42454259592003^6191*2000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050607051 2000000000 42454259592003 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135162393/250000000 : ℝ)^8239 ≤ (44112704952637/100000000000000 : ℝ)^6191 := by
    have hnat : (135162393 : ℕ)^8239*100000000000000^6191 ≤ 44112704952637^6191*250000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135162393 250000000 44112704952637 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2212520337/10000000000 : ℝ), (1050607051/2000000000 : ℝ), (135162393/250000000 : ℝ)] ![(3358258860719/25000000000000 : ℝ), (42454259592003/100000000000000 : ℝ), (44112704952637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2212520337/10000000000 : ℝ)|^8239 ≤ (3358258860719/25000000000000 : ℝ)^6191
        have hw : |(-2212520337/10000000000 : ℝ)|=(2212520337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1050607051/2000000000 : ℝ)|^8239 ≤ (42454259592003/100000000000000 : ℝ)^6191
        have hw : |(1050607051/2000000000 : ℝ)|=(1050607051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135162393/250000000 : ℝ)|^8239 ≤ (44112704952637/100000000000000 : ℝ)^6191
        have hw : |(135162393/250000000 : ℝ)|=(135162393/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s4_5 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1061849437/2000000000 : ℝ)*x 0 + (-1068567073/5000000000 : ℝ)*x 1 + (5406495673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061849437/2000000000 : ℝ)^8239 ≤ (43059906244791/100000000000000 : ℝ)^6191 := by
    have hnat : (1061849437 : ℕ)^8239*100000000000000^6191 ≤ 43059906244791^6191*2000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061849437 2000000000 43059906244791 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1068567073/5000000000 : ℝ)^8239 ≤ (801711831133/6250000000000 : ℝ)^6191 := by
    have hnat : (1068567073 : ℕ)^8239*6250000000000^6191 ≤ 801711831133^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068567073 5000000000 801711831133 6250000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406495673/10000000000 : ℝ)^8239 ≤ (44112704442297/100000000000000 : ℝ)^6191 := by
    have hnat : (5406495673 : ℕ)^8239*100000000000000^6191 ≤ 44112704442297^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406495673 10000000000 44112704442297 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061849437/2000000000 : ℝ), (-1068567073/5000000000 : ℝ), (5406495673/10000000000 : ℝ)] ![(43059906244791/100000000000000 : ℝ), (801711831133/6250000000000 : ℝ), (44112704442297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061849437/2000000000 : ℝ)|^8239 ≤ (43059906244791/100000000000000 : ℝ)^6191
        have hw : |(1061849437/2000000000 : ℝ)|=(1061849437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1068567073/5000000000 : ℝ)|^8239 ≤ (801711831133/6250000000000 : ℝ)^6191
        have hw : |(-1068567073/5000000000 : ℝ)|=(1068567073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406495673/10000000000 : ℝ)|^8239 ≤ (44112704442297/100000000000000 : ℝ)^6191
        have hw : |(5406495673/10000000000 : ℝ)|=(5406495673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s4_6 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1061849431/2000000000 : ℝ)*x 0 + (5406495689/10000000000 : ℝ)*x 1 + (-534283541/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061849431/2000000000 : ℝ)^8239 ≤ (1345622060031/3125000000000 : ℝ)^6191 := by
    have hnat : (1061849431 : ℕ)^8239*3125000000000^6191 ≤ 1345622060031^6191*2000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061849431 2000000000 1345622060031 3125000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406495689/10000000000 : ℝ)^8239 ≤ (44112704616029/100000000000000 : ℝ)^6191 := by
    have hnat : (5406495689 : ℕ)^8239*100000000000000^6191 ≤ 44112704616029^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406495689 10000000000 44112704616029 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (534283541/2500000000 : ℝ)^8239 ≤ (12827389441907/100000000000000 : ℝ)^6191 := by
    have hnat : (534283541 : ℕ)^8239*100000000000000^6191 ≤ 12827389441907^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534283541 2500000000 12827389441907 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061849431/2000000000 : ℝ), (5406495689/10000000000 : ℝ), (-534283541/2500000000 : ℝ)] ![(1345622060031/3125000000000 : ℝ), (44112704616029/100000000000000 : ℝ), (12827389441907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061849431/2000000000 : ℝ)|^8239 ≤ (1345622060031/3125000000000 : ℝ)^6191
        have hw : |(1061849431/2000000000 : ℝ)|=(1061849431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406495689/10000000000 : ℝ)|^8239 ≤ (44112704616029/100000000000000 : ℝ)^6191
        have hw : |(5406495689/10000000000 : ℝ)|=(5406495689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-534283541/2500000000 : ℝ)|^8239 ≤ (12827389441907/100000000000000 : ℝ)^6191
        have hw : |(-534283541/2500000000 : ℝ)|=(534283541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s4_7 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4377731411/10000000000 : ℝ)*x 0 + (4530138289/10000000000 : ℝ)*x 1 + (2115285941/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377731411/10000000000 : ℝ)^8239 ≤ (16654949748169/50000000000000 : ℝ)^6191 := by
    have hnat : (4377731411 : ℕ)^8239*50000000000000^6191 ≤ 16654949748169^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377731411 10000000000 16654949748169 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4530138289/10000000000 : ℝ)^8239 ≤ (8715497523373/25000000000000 : ℝ)^6191 := by
    have hnat : (4530138289 : ℕ)^8239*25000000000000^6191 ≤ 8715497523373^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530138289 10000000000 8715497523373 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115285941/5000000000 : ℝ)^8239 ≤ (1591405520113/5000000000000 : ℝ)^6191 := by
    have hnat : (2115285941 : ℕ)^8239*5000000000000^6191 ≤ 1591405520113^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115285941 5000000000 1591405520113 5000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377731411/10000000000 : ℝ), (4530138289/10000000000 : ℝ), (2115285941/5000000000 : ℝ)] ![(16654949748169/50000000000000 : ℝ), (8715497523373/25000000000000 : ℝ), (1591405520113/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377731411/10000000000 : ℝ)|^8239 ≤ (16654949748169/50000000000000 : ℝ)^6191
        have hw : |(4377731411/10000000000 : ℝ)|=(4377731411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4530138289/10000000000 : ℝ)|^8239 ≤ (8715497523373/25000000000000 : ℝ)^6191
        have hw : |(4530138289/10000000000 : ℝ)|=(4530138289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115285941/5000000000 : ℝ)|^8239 ≤ (1591405520113/5000000000000 : ℝ)^6191
        have hw : |(2115285941/5000000000 : ℝ)|=(2115285941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1046_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1867/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1291/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5489/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14247/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1867/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1291/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1867/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1291/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1867/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1291/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1867/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1291/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1867/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1291/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1867/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1291/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1291/12500 : ℝ) ^ (4119/1024 : ℝ) ≤ (2162463535154401/20000000000000000000 : ℝ) := by
    have hpowers : (1291/12500 : ℝ)^4119 ≤ (2162463535154401/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1291 : ℕ)^4119*20000000000000000000^1024 ≤ 2162463535154401^1024*12500^4119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1291 12500 2162463535154401 20000000000000000000 4119 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1291/12500 : ℝ)) (X := (2162463535154401/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1867/12500 : ℝ) ^ (4119/1024 : ℝ) ≤ (23842937064997591/50000000000000000000 : ℝ) := by
    have hpowers : (1867/12500 : ℝ)^4119 ≤ (23842937064997591/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1867 : ℕ)^4119*50000000000000000000^1024 ≤ 23842937064997591^1024*12500^4119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1867 12500 23842937064997591 50000000000000000000 4119 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1867/12500 : ℝ)) (X := (23842937064997591/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002162463535154401/10000000000000000000 : ℝ) ≤ (1000053755347913/1000000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (10002162463535154401/10000000000000000000 : ℝ)^1024 ≤ (1000053755347913/1000000000000000 : ℝ)^4119 := by
      have hnat : (10002162463535154401 : ℕ)^1024*1000000000000000^4119 ≤ 1000053755347913^4119*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002162463535154401 10000000000000000000 1000053755347913 1000000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000053755347913/1000000000000000 : ℝ)) (X := (10002162463535154401/10000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100058498191805767187/100000000000000000000 : ℝ) ≤ (10001453969114279/10000000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (100058498191805767187/100000000000000000000 : ℝ)^1024 ≤ (10001453969114279/10000000000000000 : ℝ)^4119 := by
      have hnat : (100058498191805767187 : ℕ)^1024*10000000000000000^4119 ≤ 10001453969114279^4119*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100058498191805767187 100000000000000000000 10001453969114279 10000000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001453969114279/10000000000000000 : ℝ)) (X := (100058498191805767187/100000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25023842937064997591/25000000000000000000 : ℝ) ≤ (2500592596187357/2500000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (25023842937064997591/25000000000000000000 : ℝ)^1024 ≤ (2500592596187357/2500000000000000 : ℝ)^4119 := by
      have hnat : (25023842937064997591 : ℕ)^1024*2500000000000000^4119 ≤ 2500592596187357^4119*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25023842937064997591 25000000000000000000 2500592596187357 2500000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500592596187357/2500000000000000 : ℝ)) (X := (25023842937064997591/25000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2162463535154401/20000000000000000000 : ℝ) ≤ ((319885746979668009/320000000000000000 : ℝ)+2*(101823959461/51200000000000 : ℝ)*(1291/12500 : ℝ))^(4119/1024 : ℝ) := by
    rw [show (319885746979668009/320000000000000000 : ℝ)+2*(101823959461/51200000000000 : ℝ)*(1291/12500 : ℝ)=(1000053755347913/1000000000000000 : ℝ) by norm_num, show 1+2*(2162463535154401/20000000000000000000 : ℝ)=(10002162463535154401/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23842937064997591/50000000000000000000 : ℝ)+(2162463535154401/20000000000000000000 : ℝ) ≤ ((319885746979668009/320000000000000000 : ℝ)+(101823959461/51200000000000 : ℝ)*((1867/12500 : ℝ)+(1291/12500 : ℝ)))^(4119/1024 : ℝ) := by
    rw [show (319885746979668009/320000000000000000 : ℝ)+(101823959461/51200000000000 : ℝ)*((1867/12500 : ℝ)+(1291/12500 : ℝ))=(10001453969114279/10000000000000000 : ℝ) by norm_num, show 1+(23842937064997591/50000000000000000000 : ℝ)+(2162463535154401/20000000000000000000 : ℝ)=(100058498191805767187/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23842937064997591/50000000000000000000 : ℝ) ≤ ((319885746979668009/320000000000000000 : ℝ)+2*(101823959461/51200000000000 : ℝ)*(1867/12500 : ℝ))^(4119/1024 : ℝ) := by
    rw [show (319885746979668009/320000000000000000 : ℝ)+2*(101823959461/51200000000000 : ℝ)*(1867/12500 : ℝ)=(2500592596187357/2500000000000000 : ℝ) by norm_num, show 1+2*(23842937064997591/50000000000000000000 : ℝ)=(25023842937064997591/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (319885746979668009/320000000000000000 : ℝ)*(X 1 0+X 2 0)+(101823959461/51200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (1291/12500 : ℝ)) (hi := (1867/12500 : ℝ)) (c := (319885746979668009/320000000000000000 : ℝ)) (alpha := (101823959461/51200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (319885746979668009/320000000000000000 : ℝ)*(X 0 1+X 2 1)+(101823959461/51200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (1291/12500 : ℝ)) (hi := (1867/12500 : ℝ)) (c := (319885746979668009/320000000000000000 : ℝ)) (alpha := (101823959461/51200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (319885746979668009/320000000000000000 : ℝ)*(X 0 2+X 1 2)+(101823959461/51200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (1291/12500 : ℝ)) (hi := (1867/12500 : ℝ)) (c := (319885746979668009/320000000000000000 : ℝ)) (alpha := (101823959461/51200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1106255893/5000000000 : ℝ)*X 0 0+(5406953437/10000000000 : ℝ)*X 0 1+(328286223/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534806713/1000000000 : ℝ)*X 1 0+(-286381313/1250000000 : ℝ)*X 1 1+(5252579099/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674033807/5000000000 : ℝ)*X 2 0+(2626289373/5000000000 : ℝ)*X 2 1+(-2291050329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((273607119/625000000 : ℝ)*X 0 0+(1057419427/2500000000 : ℝ)*X 0 1+(4531029703/10000000000 : ℝ)*X 0 2+(273607119/625000000 : ℝ)*X 1 0+(1057419427/2500000000 : ℝ)*X 1 1+(4531029703/10000000000 : ℝ)*X 1 2+(273607119/625000000 : ℝ)*X 2 0+(1057419427/2500000000 : ℝ)*X 2 1+(4531029703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2212520337/10000000000 : ℝ)*X 0 0+(1050607051/2000000000 : ℝ)*X 0 1+(135162393/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061849437/2000000000 : ℝ)*X 1 0+(-1068567073/5000000000 : ℝ)*X 1 1+(5406495673/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061849431/2000000000 : ℝ)*X 2 0+(5406495689/10000000000 : ℝ)*X 2 1+(-534283541/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4377731411/10000000000 : ℝ)*X 0 0+(4530138289/10000000000 : ℝ)*X 0 1+(2115285941/5000000000 : ℝ)*X 0 2+(4377731411/10000000000 : ℝ)*X 1 0+(4530138289/10000000000 : ℝ)*X 1 1+(2115285941/5000000000 : ℝ)*X 1 2+(4377731411/10000000000 : ℝ)*X 2 0+(4530138289/10000000000 : ℝ)*X 2 1+(2115285941/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1584129132280211515272633/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1115196281/50000000000000 : ℝ)*(base19) + (567290179/25000000000000 : ℝ)*(base23) + (8093833/100000000000000 : ℝ)*(upper2) + (52063371/100000000000000 : ℝ)*(upper3) + (30088873/10000000000000 : ℝ)*(upper4) + (244907440879717/5000000000000 : ℝ)*(major0) + (244907440879717/5000000000000 : ℝ)*(major1) + (244907440879717/5000000000000 : ℝ)*(major2) + (6477815407005609/100000000000000 : ℝ)*(sp0) + (404866178120833/6250000000000 : ℝ)*(sp1) + (3238929405582587/50000000000000 : ℝ)*(sp2) + (829601110063409/25000000000000 : ℝ)*(sp3) + (45673320281/100000000000000 : ℝ)*(sp4) + (7962646907/25000000000000 : ℝ)*(sp7) + (207402268177579/6250000000000 : ℝ)*(f.failure) + (647786108032589/10000000000000 : ℝ)*(f.sum) + (118773334631/128000000000000000000000000 : ℝ)*base66 + (4149495456429703/1600000000000000000000000000000 : ℝ)*base67 + (3233414387629703/1600000000000000000000000000000 : ℝ)*base69 + (22866172058029703/1600000000000000000000000000000 : ℝ)*base71 + (211850043367/128000000000000000000000000 : ℝ)*base74 + (1383893196370297/1600000000000000000000000000000 : ℝ)*base76 + (15656946144429703/1600000000000000000000000000000 : ℝ)*base77 + (4169564230829703/1600000000000000000000000000000 : ℝ)*base79 + (342294431513/128000000000000000000000000 : ℝ)*base81 + (66051/156250000000000000000 : ℝ)*base90 + (66051/156250000000000000000 : ℝ)*base92 + (66051/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1098332283408768150667443/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1369655941/100000000000000 : ℝ)*(base19) + (54984561/4000000000000 : ℝ)*(base23) + (57122359/100000000000000 : ℝ)*(upper2) + (582877/2000000000000 : ℝ)*(upper3) + (86810321/25000000000000 : ℝ)*(upper5) + (492724951035561/10000000000000 : ℝ)*(major0) + (492724951035561/10000000000000 : ℝ)*(major1) + (492724951035561/10000000000000 : ℝ)*(major2) + (18496428037/50000000000000 : ℝ)*(sp1) + (27991712129/100000000000000 : ℝ)*(sp2) + (3258173590582219/50000000000000 : ℝ)*(sp4) + (6516308818652423/100000000000000 : ℝ)*(sp5) + (1629079453709571/25000000000000 : ℝ)*(sp6) + (3338151656491393/100000000000000 : ℝ)*(sp7) + (3338151656491393/100000000000000 : ℝ)*(f.failure) + (3258173590582219/50000000000000 : ℝ)*(f.sum) + (775839493869/256000000000000000000000000 : ℝ)*base65 + (34600901217450701/3200000000000000000000000000000 : ℝ)*base68 + (25159329118250701/3200000000000000000000000000000 : ℝ)*base70 + (2093906436650701/3200000000000000000000000000000 : ℝ)*base72 + (867956885267/256000000000000000000000000 : ℝ)*base74 + (39830873582250701/3200000000000000000000000000000 : ℝ)*base76 + (7053148440149299/3200000000000000000000000000000 : ℝ)*base77 + (101313561121450701/3200000000000000000000000000000 : ℝ)*base80 + (232663979283/256000000000000000000000000 : ℝ)*base82 + (5673817/2500000000000000000000 : ℝ)*base90 + (5673817/2500000000000000000000 : ℝ)*base92 + (5673817/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1046_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1867/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1291/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5489/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14247/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1046_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1046_s5_0 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1106701007/5000000000 : ℝ)*x 0 + (1349396023/2500000000 : ℝ)*x 1 + (1315341287/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1106701007/5000000000 : ℝ)^8239 ≤ (6720079842913/50000000000000 : ℝ)^6191 := by
    have hnat : (1106701007 : ℕ)^8239*50000000000000^6191 ≤ 6720079842913^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106701007 5000000000 6720079842913 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349396023/2500000000 : ℝ)^8239 ≤ (22007983141503/50000000000000 : ℝ)^6191 := by
    have hnat : (1349396023 : ℕ)^8239*50000000000000^6191 ≤ 22007983141503^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349396023 2500000000 22007983141503 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315341287/2500000000 : ℝ)^8239 ≤ (42543874018467/100000000000000 : ℝ)^6191 := by
    have hnat : (1315341287 : ℕ)^8239*100000000000000^6191 ≤ 42543874018467^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315341287 2500000000 42543874018467 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1106701007/5000000000 : ℝ), (1349396023/2500000000 : ℝ), (1315341287/2500000000 : ℝ)] ![(6720079842913/50000000000000 : ℝ), (22007983141503/50000000000000 : ℝ), (42543874018467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1106701007/5000000000 : ℝ)|^8239 ≤ (6720079842913/50000000000000 : ℝ)^6191
        have hw : |(-1106701007/5000000000 : ℝ)|=(1106701007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349396023/2500000000 : ℝ)|^8239 ≤ (22007983141503/50000000000000 : ℝ)^6191
        have hw : |(1349396023/2500000000 : ℝ)|=(1349396023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315341287/2500000000 : ℝ)|^8239 ≤ (42543874018467/100000000000000 : ℝ)^6191
        have hw : |(1315341287/2500000000 : ℝ)|=(1315341287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s5_1 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334108623/625000000 : ℝ)*x 0 + (-1141282047/5000000000 : ℝ)*x 1 + (5261365089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334108623/625000000 : ℝ)^8239 ≤ (43454208892467/100000000000000 : ℝ)^6191 := by
    have hnat : (334108623 : ℕ)^8239*100000000000000^6191 ≤ 43454208892467^6191*625000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334108623 625000000 43454208892467 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1141282047/5000000000 : ℝ)^8239 ≤ (3500479428331/25000000000000 : ℝ)^6191 := by
    have hnat : (1141282047 : ℕ)^8239*25000000000000^6191 ≤ 3500479428331^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141282047 5000000000 3500479428331 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261365089/10000000000 : ℝ)^8239 ≤ (2658992086473/6250000000000 : ℝ)^6191 := by
    have hnat : (5261365089 : ℕ)^8239*6250000000000^6191 ≤ 2658992086473^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261365089 10000000000 2658992086473 6250000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334108623/625000000 : ℝ), (-1141282047/5000000000 : ℝ), (5261365089/10000000000 : ℝ)] ![(43454208892467/100000000000000 : ℝ), (3500479428331/25000000000000 : ℝ), (2658992086473/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334108623/625000000 : ℝ)|^8239 ≤ (43454208892467/100000000000000 : ℝ)^6191
        have hw : |(334108623/625000000 : ℝ)|=(334108623/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1141282047/5000000000 : ℝ)|^8239 ≤ (3500479428331/25000000000000 : ℝ)^6191
        have hw : |(-1141282047/5000000000 : ℝ)|=(1141282047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261365089/10000000000 : ℝ)|^8239 ≤ (2658992086473/6250000000000 : ℝ)^6191
        have hw : |(5261365089/10000000000 : ℝ)|=(5261365089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s5_2 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345737987/10000000000 : ℝ)*x 0 + (5261365109/10000000000 : ℝ)*x 1 + (-2282564043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345737987/10000000000 : ℝ)^8239 ≤ (8690841819601/20000000000000 : ℝ)^6191 := by
    have hnat : (5345737987 : ℕ)^8239*20000000000000^6191 ≤ 8690841819601^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345737987 10000000000 8690841819601 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261365109/10000000000 : ℝ)^8239 ≤ (10635968399697/25000000000000 : ℝ)^6191 := by
    have hnat : (5261365109 : ℕ)^8239*25000000000000^6191 ≤ 10635968399697^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261365109 10000000000 10635968399697 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2282564043/10000000000 : ℝ)^8239 ≤ (1750239662123/12500000000000 : ℝ)^6191 := by
    have hnat : (2282564043 : ℕ)^8239*12500000000000^6191 ≤ 1750239662123^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282564043 10000000000 1750239662123 12500000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345737987/10000000000 : ℝ), (5261365109/10000000000 : ℝ), (-2282564043/10000000000 : ℝ)] ![(8690841819601/20000000000000 : ℝ), (10635968399697/25000000000000 : ℝ), (1750239662123/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345737987/10000000000 : ℝ)|^8239 ≤ (8690841819601/20000000000000 : ℝ)^6191
        have hw : |(5345737987/10000000000 : ℝ)|=(5345737987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261365109/10000000000 : ℝ)|^8239 ≤ (10635968399697/25000000000000 : ℝ)^6191
        have hw : |(5261365109/10000000000 : ℝ)|=(5261365109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2282564043/10000000000 : ℝ)|^8239 ≤ (1750239662123/12500000000000 : ℝ)^6191
        have hw : |(-2282564043/10000000000 : ℝ)|=(2282564043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s5_3 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4378230493/10000000000 : ℝ)*x 0 + (849465999/2000000000 : ℝ)*x 1 + (564155069/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378230493/10000000000 : ℝ)^8239 ≤ (6662990659159/20000000000000 : ℝ)^6191 := by
    have hnat : (4378230493 : ℕ)^8239*20000000000000^6191 ≤ 6662990659159^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378230493 10000000000 6662990659159 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (849465999/2000000000 : ℝ)^8239 ≤ (127984017013/400000000000 : ℝ)^6191 := by
    have hnat : (849465999 : ℕ)^8239*400000000000^6191 ≤ 127984017013^6191*2000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849465999 2000000000 127984017013 400000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (564155069/1250000000 : ℝ)^8239 ≤ (34689042424581/100000000000000 : ℝ)^6191 := by
    have hnat : (564155069 : ℕ)^8239*100000000000000^6191 ≤ 34689042424581^6191*1250000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564155069 1250000000 34689042424581 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378230493/10000000000 : ℝ), (849465999/2000000000 : ℝ), (564155069/1250000000 : ℝ)] ![(6662990659159/20000000000000 : ℝ), (127984017013/400000000000 : ℝ), (34689042424581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378230493/10000000000 : ℝ)|^8239 ≤ (6662990659159/20000000000000 : ℝ)^6191
        have hw : |(4378230493/10000000000 : ℝ)|=(4378230493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(849465999/2000000000 : ℝ)|^8239 ≤ (127984017013/400000000000 : ℝ)^6191
        have hw : |(849465999/2000000000 : ℝ)|=(849465999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(564155069/1250000000 : ℝ)|^8239 ≤ (34689042424581/100000000000000 : ℝ)^6191
        have hw : |(564155069/1250000000 : ℝ)|=(564155069/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s5_4 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-276675977/1250000000 : ℝ)*x 0 + (328857539/625000000 : ℝ)*x 1 + (5397227281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (276675977/1250000000 : ℝ)^8239 ≤ (13440206571023/100000000000000 : ℝ)^6191 := by
    have hnat : (276675977 : ℕ)^8239*100000000000000^6191 ≤ 13440206571023^6191*1250000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276675977 1250000000 13440206571023 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328857539/625000000 : ℝ)^8239 ≤ (8509539867087/20000000000000 : ℝ)^6191 := by
    have hnat : (328857539 : ℕ)^8239*20000000000000^6191 ≤ 8509539867087^6191*625000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328857539 625000000 8509539867087 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397227281/10000000000 : ℝ)^8239 ≤ (44012094080979/100000000000000 : ℝ)^6191 := by
    have hnat : (5397227281 : ℕ)^8239*100000000000000^6191 ≤ 44012094080979^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397227281 10000000000 44012094080979 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-276675977/1250000000 : ℝ), (328857539/625000000 : ℝ), (5397227281/10000000000 : ℝ)] ![(13440206571023/100000000000000 : ℝ), (8509539867087/20000000000000 : ℝ), (44012094080979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-276675977/1250000000 : ℝ)|^8239 ≤ (13440206571023/100000000000000 : ℝ)^6191
        have hw : |(-276675977/1250000000 : ℝ)|=(276675977/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328857539/625000000 : ℝ)|^8239 ≤ (8509539867087/20000000000000 : ℝ)^6191
        have hw : |(328857539/625000000 : ℝ)|=(328857539/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397227281/10000000000 : ℝ)|^8239 ≤ (44012094080979/100000000000000 : ℝ)^6191
        have hw : |(5397227281/10000000000 : ℝ)|=(5397227281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s5_5 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (42491861/80000000 : ℝ)*x 0 + (-1073350971/5000000000 : ℝ)*x 1 + (67465341/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42491861/80000000 : ℝ)^8239 ≤ (43084035676417/100000000000000 : ℝ)^6191 := by
    have hnat : (42491861 : ℕ)^8239*100000000000000^6191 ≤ 43084035676417^6191*80000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42491861 80000000 43084035676417 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1073350971/5000000000 : ℝ)^8239 ≤ (6451935121899/50000000000000 : ℝ)^6191 := by
    have hnat : (1073350971 : ℕ)^8239*50000000000000^6191 ≤ 6451935121899^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073350971 5000000000 6451935121899 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67465341/125000000 : ℝ)^8239 ≤ (44012094070127/100000000000000 : ℝ)^6191 := by
    have hnat : (67465341 : ℕ)^8239*100000000000000^6191 ≤ 44012094070127^6191*125000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67465341 125000000 44012094070127 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42491861/80000000 : ℝ), (-1073350971/5000000000 : ℝ), (67465341/125000000 : ℝ)] ![(43084035676417/100000000000000 : ℝ), (6451935121899/50000000000000 : ℝ), (44012094070127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42491861/80000000 : ℝ)|^8239 ≤ (43084035676417/100000000000000 : ℝ)^6191
        have hw : |(42491861/80000000 : ℝ)|=(42491861/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1073350971/5000000000 : ℝ)|^8239 ≤ (6451935121899/50000000000000 : ℝ)^6191
        have hw : |(-1073350971/5000000000 : ℝ)|=(1073350971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67465341/125000000 : ℝ)|^8239 ≤ (44012094070127/100000000000000 : ℝ)^6191
        have hw : |(67465341/125000000 : ℝ)|=(67465341/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s5_6 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327870657/2500000000 : ℝ)*x 0 + (5397227283/10000000000 : ℝ)*x 1 + (-1073350967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327870657/2500000000 : ℝ)^8239 ≤ (43084035708801/100000000000000 : ℝ)^6191 := by
    have hnat : (1327870657 : ℕ)^8239*100000000000000^6191 ≤ 43084035708801^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327870657 2500000000 43084035708801 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397227283/10000000000 : ℝ)^8239 ≤ (44012094102683/100000000000000 : ℝ)^6191 := by
    have hnat : (5397227283 : ℕ)^8239*100000000000000^6191 ≤ 44012094102683^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397227283 10000000000 44012094102683 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1073350967/5000000000 : ℝ)^8239 ≤ (6451935089901/50000000000000 : ℝ)^6191 := by
    have hnat : (1073350967 : ℕ)^8239*50000000000000^6191 ≤ 6451935089901^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073350967 5000000000 6451935089901 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327870657/2500000000 : ℝ), (5397227283/10000000000 : ℝ), (-1073350967/5000000000 : ℝ)] ![(43084035708801/100000000000000 : ℝ), (44012094102683/100000000000000 : ℝ), (6451935089901/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327870657/2500000000 : ℝ)|^8239 ≤ (43084035708801/100000000000000 : ℝ)^6191
        have hw : |(1327870657/2500000000 : ℝ)|=(1327870657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397227283/10000000000 : ℝ)|^8239 ≤ (44012094102683/100000000000000 : ℝ)^6191
        have hw : |(5397227283/10000000000 : ℝ)|=(5397227283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1073350967/5000000000 : ℝ)|^8239 ≤ (6451935089901/50000000000000 : ℝ)^6191
        have hw : |(-1073350967/5000000000 : ℝ)|=(1073350967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s5_7 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4378241851/10000000000 : ℝ)*x 0 + (4512546653/10000000000 : ℝ)*x 1 + (2124013233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378241851/10000000000 : ℝ)^8239 ≤ (16657534155643/50000000000000 : ℝ)^6191 := by
    have hnat : (4378241851 : ℕ)^8239*50000000000000^6191 ≤ 16657534155643^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378241851 10000000000 16657534155643 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4512546653/10000000000 : ℝ)^8239 ≤ (34681944967979/100000000000000 : ℝ)^6191 := by
    have hnat : (4512546653 : ℕ)^8239*100000000000000^6191 ≤ 34681944967979^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512546653 10000000000 34681944967979 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124013233/5000000000 : ℝ)^8239 ≤ (32002986710031/100000000000000 : ℝ)^6191 := by
    have hnat : (2124013233 : ℕ)^8239*100000000000000^6191 ≤ 32002986710031^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124013233 5000000000 32002986710031 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378241851/10000000000 : ℝ), (4512546653/10000000000 : ℝ), (2124013233/5000000000 : ℝ)] ![(16657534155643/50000000000000 : ℝ), (34681944967979/100000000000000 : ℝ), (32002986710031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378241851/10000000000 : ℝ)|^8239 ≤ (16657534155643/50000000000000 : ℝ)^6191
        have hw : |(4378241851/10000000000 : ℝ)|=(4378241851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4512546653/10000000000 : ℝ)|^8239 ≤ (34681944967979/100000000000000 : ℝ)^6191
        have hw : |(4512546653/10000000000 : ℝ)|=(4512546653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2124013233/5000000000 : ℝ)|^8239 ≤ (32002986710031/100000000000000 : ℝ)^6191
        have hw : |(2124013233/5000000000 : ℝ)|=(2124013233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1046_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14247/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5489/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5583/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14051/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14247/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5489/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14247/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5489/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14247/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5489/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14247/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5489/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14247/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5489/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14247/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5489/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5489/50000 : ℝ) ^ (4119/1024 : ℝ) ≤ (13821085637661217/100000000000000000000 : ℝ) := by
    have hpowers : (5489/50000 : ℝ)^4119 ≤ (13821085637661217/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5489 : ℕ)^4119*100000000000000000000^1024 ≤ 13821085637661217^1024*50000^4119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5489 50000 13821085637661217 100000000000000000000 4119 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5489/50000 : ℝ)) (X := (13821085637661217/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14247/100000 : ℝ) ^ (4119/1024 : ℝ) ≤ (61617710576817/156250000000000000 : ℝ) := by
    have hpowers : (14247/100000 : ℝ)^4119 ≤ (61617710576817/156250000000000000 : ℝ)^1024 := by
      have hnat : (14247 : ℕ)^4119*156250000000000000^1024 ≤ 61617710576817^1024*100000^4119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14247 100000 61617710576817 156250000000000000 4119 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14247/100000 : ℝ)) (X := (61617710576817/156250000000000000 : ℝ)) (by norm_num) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013821085637661217/50000000000000000000 : ℝ) ≤ (5000343562081753/5000000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (50013821085637661217/50000000000000000000 : ℝ)^1024 ≤ (5000343562081753/5000000000000000 : ℝ)^4119 := by
      have hnat : (50013821085637661217 : ℕ)^1024*5000000000000000^4119 ≤ 5000343562081753^4119*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013821085637661217 50000000000000000000 5000343562081753 5000000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000343562081753/5000000000000000 : ℝ)) (X := (50013821085637661217/50000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100053256420406824097/100000000000000000000 : ℝ) ≤ (10001323711251039/10000000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (100053256420406824097/100000000000000000000 : ℝ)^1024 ≤ (10001323711251039/10000000000000000 : ℝ)^4119 := by
      have hnat : (100053256420406824097 : ℕ)^1024*10000000000000000^4119 ≤ 10001323711251039^4119*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100053256420406824097 100000000000000000000 10001323711251039 10000000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001323711251039/10000000000000000 : ℝ)) (X := (100053256420406824097/100000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (78186617710576817/78125000000000000 : ℝ) ≤ (2500490074584643/2500000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (78186617710576817/78125000000000000 : ℝ)^1024 ≤ (2500490074584643/2500000000000000 : ℝ)^4119 := by
      have hnat : (78186617710576817 : ℕ)^1024*2500000000000000^4119 ≤ 2500490074584643^4119*78125000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78186617710576817 78125000000000000 2500490074584643 2500000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500490074584643/2500000000000000 : ℝ)) (X := (78186617710576817/78125000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13821085637661217/100000000000000000000 : ℝ) ≤ ((16339134651398313283/16345000000000000000 : ℝ)+2*(636587087533/326900000000000 : ℝ)*(5489/50000 : ℝ))^(4119/1024 : ℝ) := by
    rw [show (16339134651398313283/16345000000000000000 : ℝ)+2*(636587087533/326900000000000 : ℝ)*(5489/50000 : ℝ)=(5000343562081753/5000000000000000 : ℝ) by norm_num, show 1+2*(13821085637661217/100000000000000000000 : ℝ)=(50013821085637661217/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(61617710576817/156250000000000000 : ℝ)+(13821085637661217/100000000000000000000 : ℝ) ≤ ((16339134651398313283/16345000000000000000 : ℝ)+(636587087533/326900000000000 : ℝ)*((14247/100000 : ℝ)+(5489/50000 : ℝ)))^(4119/1024 : ℝ) := by
    rw [show (16339134651398313283/16345000000000000000 : ℝ)+(636587087533/326900000000000 : ℝ)*((14247/100000 : ℝ)+(5489/50000 : ℝ))=(10001323711251039/10000000000000000 : ℝ) by norm_num, show 1+(61617710576817/156250000000000000 : ℝ)+(13821085637661217/100000000000000000000 : ℝ)=(100053256420406824097/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(61617710576817/156250000000000000 : ℝ) ≤ ((16339134651398313283/16345000000000000000 : ℝ)+2*(636587087533/326900000000000 : ℝ)*(14247/100000 : ℝ))^(4119/1024 : ℝ) := by
    rw [show (16339134651398313283/16345000000000000000 : ℝ)+2*(636587087533/326900000000000 : ℝ)*(14247/100000 : ℝ)=(2500490074584643/2500000000000000 : ℝ) by norm_num, show 1+2*(61617710576817/156250000000000000 : ℝ)=(78186617710576817/78125000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16339134651398313283/16345000000000000000 : ℝ)*(X 1 0+X 2 0)+(636587087533/326900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (5489/50000 : ℝ)) (hi := (14247/100000 : ℝ)) (c := (16339134651398313283/16345000000000000000 : ℝ)) (alpha := (636587087533/326900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16339134651398313283/16345000000000000000 : ℝ)*(X 0 1+X 2 1)+(636587087533/326900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (5489/50000 : ℝ)) (hi := (14247/100000 : ℝ)) (c := (16339134651398313283/16345000000000000000 : ℝ)) (alpha := (636587087533/326900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16339134651398313283/16345000000000000000 : ℝ)*(X 0 2+X 1 2)+(636587087533/326900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (5489/50000 : ℝ)) (hi := (14247/100000 : ℝ)) (c := (16339134651398313283/16345000000000000000 : ℝ)) (alpha := (636587087533/326900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1106701007/5000000000 : ℝ)*X 0 0+(1349396023/2500000000 : ℝ)*X 0 1+(1315341287/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334108623/625000000 : ℝ)*X 1 0+(-1141282047/5000000000 : ℝ)*X 1 1+(5261365089/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345737987/10000000000 : ℝ)*X 2 0+(5261365109/10000000000 : ℝ)*X 2 1+(-2282564043/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4378230493/10000000000 : ℝ)*X 0 0+(849465999/2000000000 : ℝ)*X 0 1+(564155069/1250000000 : ℝ)*X 0 2+(4378230493/10000000000 : ℝ)*X 1 0+(849465999/2000000000 : ℝ)*X 1 1+(564155069/1250000000 : ℝ)*X 1 2+(4378230493/10000000000 : ℝ)*X 2 0+(849465999/2000000000 : ℝ)*X 2 1+(564155069/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-276675977/1250000000 : ℝ)*X 0 0+(328857539/625000000 : ℝ)*X 0 1+(5397227281/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((42491861/80000000 : ℝ)*X 1 0+(-1073350971/5000000000 : ℝ)*X 1 1+(67465341/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327870657/2500000000 : ℝ)*X 2 0+(5397227283/10000000000 : ℝ)*X 2 1+(-1073350967/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4378241851/10000000000 : ℝ)*X 0 0+(4512546653/10000000000 : ℝ)*X 0 1+(2124013233/5000000000 : ℝ)*X 0 2+(4378241851/10000000000 : ℝ)*X 1 0+(4512546653/10000000000 : ℝ)*X 1 1+(2124013233/5000000000 : ℝ)*X 1 2+(4378241851/10000000000 : ℝ)*X 2 0+(4512546653/10000000000 : ℝ)*X 2 1+(2124013233/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2586684481663671623471754207/817250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (743996723/100000000000000 : ℝ)*(base19) + (149633787/20000000000000 : ℝ)*(base23) + (234357/2000000000000 : ℝ)*(lower2) + (25022719/100000000000000 : ℝ)*(upper3) + (22680183/25000000000000 : ℝ)*(upper5) + (5550921437104781/100000000000000 : ℝ)*(major0) + (5550921437104781/100000000000000 : ℝ)*(major1) + (5550921437104781/100000000000000 : ℝ)*(major2) + (1835285010634117/25000000000000 : ℝ)*(sp0) + (7341160218078421/100000000000000 : ℝ)*(sp1) + (734116021390621/10000000000000 : ℝ)*(sp2) + (3760672906612479/100000000000000 : ℝ)*(sp3) + (20919538677/100000000000000 : ℝ)*(sp4) + (8900018331/100000000000000 : ℝ)*(sp7) + (376068180663081/10000000000000 : ℝ)*(f.failure) + (1468232192415029/20000000000000 : ℝ)*(f.sum) + (32374467630093/16345000000000000000000000000 : ℝ)*base65 + (18861910960295243977/1634500000000000000000000000000000 : ℝ)*base68 + (9959469253748743977/1634500000000000000000000000000000 : ℝ)*base70 + (25530729972283243977/1634500000000000000000000000000000 : ℝ)*base72 + (33367432408757/16345000000000000000000000000 : ℝ)*base74 + (21761180311444743977/1634500000000000000000000000000000 : ℝ)*base76 + (21135577030082243977/1634500000000000000000000000000000 : ℝ)*base78 + (11587054473712243977/1634500000000000000000000000000000 : ℝ)*base80 + (33120646609007/16345000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (36511/250000000000000000000 : ℝ)*base89 + (36511/250000000000000000000 : ℝ)*base91 + (36511/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (35434345856779164921693/4086250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1617225007/100000000000000 : ℝ)*(base19) + (1767447803/100000000000000 : ℝ)*(base23) + (177298203/100000000000000 : ℝ)*(upper3) + (64389907/100000000000000 : ℝ)*(lower4) + (174780177/100000000000000 : ℝ)*(upper5) + (21797147085717/390625000000 : ℝ)*(major0) + (21797147085717/390625000000 : ℝ)*(major1) + (21797147085717/390625000000 : ℝ)*(major2) + (5210571619/12500000000000 : ℝ)*(sp1) + (91068199/200000000000 : ℝ)*(sp2) + (7379709649567771/100000000000000 : ℝ)*(sp4) + (1844916586942453/25000000000000 : ℝ)*(sp5) + (7379662348020467/100000000000000 : ℝ)*(sp6) + (3780429369265829/100000000000000 : ℝ)*(sp7) + (3780429369265829/100000000000000 : ℝ)*(f.failure) + (7379709649567771/100000000000000 : ℝ)*(f.sum) + (20193059035881/16345000000000000000000000000 : ℝ)*base65 + (875135698746837/51078125000000000000000000000000 : ℝ)*base68 + (641913854791809337/51078125000000000000000000000000 : ℝ)*base70 + (115672985177721913/51078125000000000000000000000000 : ℝ)*base71 + (9501000136191/16345000000000000000000000000 : ℝ)*base73 + (129765974704912481/25539062500000000000000000000000 : ℝ)*base76 + (200621232458034413/51078125000000000000000000000000 : ℝ)*base77 + (223980876886306269/25539062500000000000000000000000 : ℝ)*base79 + (1480570979551/4086250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3169699/2500000000000000000000 : ℝ)*base89 + (3169699/2500000000000000000000 : ℝ)*base91 + (3169699/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1046_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14247/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5489/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1046_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1046_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2101/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8613/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1046_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1046_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1046_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2101/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8613/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5583/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1046_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
